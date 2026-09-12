# MPSS: every derivation has a uniformly sized copy

`MPSS/Sized` defines when a derivation's binder families are uniformly sized and proves that
weakening, reflexivity and renaming a bound name preserve it. This module adds the renaming of
an *unbound* name (the shape a `Me-Bet` body needs, where the parameter is not in the context),
the two head-renaming wrappers `MPSS/DiamondStep` uses, and the construction itself: `uniform`
rebuilds a derivation with every family generated from one member by renaming, and
`uniformCtx` does the same for every piece of a context reduction.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Uniform where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Sized
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Open using (∉-ann; ∉-head)
open import MPSS.Rename using (rename-fvar; open-rename; substStack-id)
open import PSS.Syntax using (subst-fresh; subst-fvar-≢; subst-fvar-≡; subst-intro; subst-open;
                              lc-fvar; fresh; fresh-∉; ∉-tail; ∉-++ˡ; ∉-++ʳ; closeRec)
open import PSS.Close using (open-close; close-open; fv-close)
```

## Renaming an unbound name preserves the size

`MPSS/Open`'s `⟶ᵉ-subst₀` at a variable, with the size carried along.

```agda
Renamed₀ : ∀ {Γ s u v} → Name → Name → ℕ → Set
Renamed₀ {Γ} {s} {u} {v} x y n =
  Σ[ d′ ∈ Γ ∣ s ⊢ (u [ x := fvar y ]) ⟶ᵉ (v [ x := fvar y ]) ] Sized d′ n

rename₀ˢ : ∀ {Γ s u v n} x y → x ∉ dom Γ
         → (d : Γ ∣ s ⊢ u ⟶ᵉ v) → Sized d n → Renamed₀ {Γ} {s} {u} {v} x y n

rename₀ˢ x y x∉ (Me-Var {x = z} pv) sd
  rewrite proj₂ (rename-fvar x y z) = Me-Var pv , sd
rename₀ˢ x y x∉ (Me-Top pv) sd = Me-Top pv , sd
rename₀ˢ x y x∉ (Me-TAp pv) sd = Me-TAp pv , sd

rename₀ˢ {Γ} {s} x y x∉ (Me-Pro {x = z} {α = α} {α' = β} pv m d) (k , sd , eqn) = go
  where
    x≢z : x ≢ z
    x≢z refl = x∉ (∈-dom m)

    ih = rename₀ˢ x y x∉ d sd
    eq = subst-fresh {α} x (fvar y) (∉-ann (prevalid-ctx pv) x∉ m)

    ih′ : Σ[ d′ ∈ Γ ∣ s ⊢ α ⟶ᵉ (β [ x := fvar y ]) ] Sized d′ k
    ih′ = subst (λ q → Γ ∣ s ⊢ q ⟶ᵉ (β [ x := fvar y ])) eq (proj₁ ih)
        , sized-subst-src eq (proj₂ ih)

    go : Renamed₀ {Γ} {s} {fvar z} {β} x y _
    go rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z = Me-Pro pv m (proj₁ ih′) , k , proj₂ ih′ , eqn

rename₀ˢ {Γ} {s} x y x∉ (Me-App {u = u} {u' = u′} {v = w} {v' = w′} d e) (k , l , sd , se , eqn) = go
  where
    x∉w : x ∉ fv w
    x∉w = ∉-head (⟶ᵉ-prevalid d) x∉

    ih  = rename₀ˢ x y x∉ d sd
    ihe = rename₀ˢ x y x∉ e se
    eq  = sym (subst-fresh {w} x (fvar y) x∉w)

    ih′ : Σ[ d′ ∈ Γ ∣ ((w [ x := fvar y ]) ∷ s) ⊢ (u [ x := fvar y ]) ⟶ᵉ (u′ [ x := fvar y ]) ] Sized d′ k
    ih′ = subst (λ q → Γ ∣ (q ∷ s) ⊢ (u [ x := fvar y ]) ⟶ᵉ (u′ [ x := fvar y ])) eq (proj₁ ih)
        , sized-subst-stk eq (proj₂ ih)
      where
        sized-subst-stk : ∀ {Γ s u v n w w′} (eq : w ≡ w′) {d : Γ ∣ (w ∷ s) ⊢ u ⟶ᵉ v}
                        → Sized d n → Sized (subst (λ q → Γ ∣ (q ∷ s) ⊢ u ⟶ᵉ v) eq d) n
        sized-subst-stk refl sd = sd

    go : Renamed₀ {Γ} {s} {app u w} {app u′ w′} x y _
    go = Me-App (proj₁ ih′) (proj₁ ihe) , k , l , proj₂ ih′ , proj₂ ihe , eqn

rename₀ˢ {Γ} x y x∉ (Me-Fun {t = a} {t' = a′} {u = u} {u' = u′} L d F) (k , l , sd , sF , eqn) =
  Me-Fun (x ∷ y ∷ L ++ dom Γ) (proj₁ iha) (λ z∉ → proj₁ (bodyΣ z∉))
  , k , l , proj₂ iha , (λ z∉ → proj₂ (bodyΣ z∉)) , eqn
  where
    iha = rename₀ˢ x y x∉ d sd

    Body : Name → Set
    Body z = Σ[ d′ ∈ ((z , sub , a [ x := fvar y ]) ∷ Γ) ∣ []
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u′ [ x := fvar y ]) ^ fvar z) ]
              Sized d′ l

    bodyΣ : ∀ {z} → z ∉ (x ∷ y ∷ L ++ dom Γ) → Body z
    bodyΣ {z} z∉ = transport (rename₀ˢ x y x∉′ (F z∉L) (sF z∉L))
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail (∉-tail z∉))

        pvz = ⟶ᵉ-prevalid (F z∉L)

        x∉′ : x ∉ dom ((z , sub , a) ∷ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        x∉a : x ∉ fv a
        x∉a = ∉-ann (prevalid-ctx pvz) x∉′ (here refl)

        transport : Renamed₀ {(z , sub , a) ∷ Γ} {[]} {u ^ fvar z} {u′ ^ fvar z} x y l → Body z
        transport h rewrite subst-fresh {a} x (fvar y) x∉a
                          | sym (open-rename y x≢z u) | sym (open-rename y x≢z u′) = h

rename₀ˢ {Γ} x y x∉ (Me-FOp {s = s} {α = α} {t = a} {t' = a′} {u = u} {u' = u′} L d F)
         (k , l , sd , sF , eqn) =
  Me-FOp (x ∷ y ∷ L ++ dom Γ) (proj₁ iha) (λ z∉ → proj₁ (bodyΣ z∉))
  , k , l , proj₂ iha , (λ z∉ → proj₂ (bodyΣ z∉)) , eqn
  where
    iha = rename₀ˢ x y x∉ d sd

    Body : Name → Set
    Body z = Σ[ d′ ∈ ((z , eqv , α) ∷ Γ) ∣ s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u′ [ x := fvar y ]) ^ fvar z) ]
              Sized d′ l

    bodyΣ : ∀ {z} → z ∉ (x ∷ y ∷ L ++ dom Γ) → Body z
    bodyΣ {z} z∉ = transport (rename₀ˢ x y x∉′ (F z∉L) (sF z∉L))
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail (∉-tail z∉))

        x∉′ : x ∉ dom ((z , eqv , α) ∷ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        transport : Renamed₀ {(z , eqv , α) ∷ Γ} {s} {u ^ fvar z} {u′ ^ fvar z} x y l → Body z
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u′) = h

rename₀ˢ {Γ} {s} x y x∉ (Me-Bet {t = a} {u = u} {u' = u′} {v = w} {v' = w′} L F e)
         (k , l , sF , se , eqn) = result
  where
    Body : Name → Set
    Body z = Σ[ d′ ∈ Γ ∣ s ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u′ [ x := fvar y ]) ^ fvar z) ]
              Sized d′ k

    bodyΣ : ∀ {z} → z ∉ (x ∷ y ∷ L) → Body z
    bodyΣ {z} z∉ = transport (rename₀ˢ x y x∉ (F z∉L) (sF z∉L))
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-tail (∉-tail z∉)

        transport : Renamed₀ {Γ} {s} {u ^ fvar z} {u′ ^ fvar z} x y k → Body z
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u′) = h

    ihe = rename₀ˢ x y x∉ e se

    result : Renamed₀ {Γ} {s} {app (lam a u) w} {u′ ^ w′} x y _
    result rewrite subst-open (lc-fvar {y}) 0 w′ u′ x =
      Me-Bet {t = a [ x := fvar y ]} {u' = u′ [ x := fvar y ]} (x ∷ y ∷ L)
             (λ z∉ → proj₁ (bodyΣ z∉)) (proj₁ ihe)
      , k , l , (λ z∉ → proj₂ (bodyΣ z∉)) , proj₂ ihe , eqn
```

## The two head-renaming wrappers

```agda
rename-headˢ : ∀ {Γ s b w a α n} x y
             → x ∉ dom Γ → y ∉ dom Γ → x ∉ fv α → x ∉ fv b → x ∉ fvStack s → LC w
             → (d : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ w) → Sized d n
             → Σ[ d′ ∈ ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ᵉ ((closeRec 0 x w) ^ fvar y) ]
                 Sized d′ n
rename-headˢ {Γ} {s} {b} {w} {a} {α} {n} x y x∉Γ y∉Γ x∉α x∉b x∉s lw d sd with x ≟ y
... | yes refl = dΣ
  where
    dΣ : Σ[ d′ ∈ ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ ((closeRec 0 x w) ^ fvar x) ] Sized d′ n
    dΣ rewrite open-close lw 0 x = d , sd
... | no x≢y = result
  where
    y∉ : y ∉ dom ([] ++ (x , a , α) ∷ Γ)
    y∉ (here p)  = x≢y (sym p)
    y∉ (there h) = y∉Γ h

    dΣ : Σ[ d′ ∈ ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ ((closeRec 0 x w) ^ fvar x) ] Sized d′ n
    dΣ rewrite open-close lw 0 x = d , sd

    renamed = renameˢ [] y∉ (proj₁ dΣ) (proj₂ dΣ)

    result : Σ[ d′ ∈ ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ᵉ ((closeRec 0 x w) ^ fvar y) ] Sized d′ n
    result rewrite sym (substStack-id x (fvar y) s x∉s)
                 | subst-intro {b} (lc-fvar {y}) x x∉b
                 | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
                 = renamed

close-rename₀ˢ : ∀ {Γ s u w n} x y → x ∉ dom Γ → x ∉ fv u → LC w
               → (d : Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ w) → Sized d n
               → Σ[ d′ ∈ Γ ∣ s ⊢ (u ^ fvar y) ⟶ᵉ ((closeRec 0 x w) ^ fvar y) ] Sized d′ n
close-rename₀ˢ {Γ} {s} {u} {w} {n} x y x∉Γ x∉u lw d sd
  rewrite subst-intro {u} (lc-fvar {y}) x x∉u
        | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
  = rename₀ˢ x y x∉Γ (proj₁ dΣ) (proj₂ dΣ)
  where
    dΣ : Σ[ d′ ∈ Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ ((closeRec 0 x w) ^ fvar x) ] Sized d′ n
    dΣ rewrite open-close lw 0 x = d , sd
```

## Uniformization

Each binder family is regenerated from its member at one fresh name. Local closure of the
subject supplies the local closure of the targets the renaming needs.

```agda
Uniform : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ v → Set
Uniform {Γ} {s} {u} {v} d = Σ[ d′ ∈ Γ ∣ s ⊢ u ⟶ᵉ v ] ∃[ n ] Sized d′ n

uniform : ∀ {Γ s u v} → LC u → (d : Γ ∣ s ⊢ u ⟶ᵉ v) → Uniform d
uniform lu (Me-Var pv) = Me-Var pv , 1 , refl
uniform lu (Me-Top pv) = Me-Top pv , 1 , refl
uniform lu (Me-TAp pv) = Me-TAp pv , 1 , refl
uniform lu (Me-Pro pv m d) with uniform (prevalid-bound-lc (prevalid-ctx pv) m) d
... | d′ , n , sd = Me-Pro pv m d′ , suc n , n , sd , refl
uniform (lc-app lu lv) (Me-App d e) with uniform lu d | uniform lv e
... | d′ , k , sd | e′ , l , se = Me-App d′ e′ , suc (k + l) , k , l , sd , se , refl

uniform {Γ} (lc-lam {t = t} {b = b} L₀ lt F₀) (Me-Fun {t = t₁} {t' = t′} {u = u} {u' = u′} L d F) = result
  where
    A = L ++ L₀ ++ dom Γ ++ fv u ++ fv u′ ++ fv t
    x₀ = fresh A
    a∉ = fresh-∉ A
    x₀∉L  = ∉-++ˡ a∉
    r₁ = ∉-++ʳ L a∉
    x₀∉L₀ = ∉-++ˡ r₁
    r₂ = ∉-++ʳ L₀ r₁
    x₀∉Γ : x₀ ∉ dom Γ
    x₀∉Γ = ∉-++ˡ r₂
    r₃ = ∉-++ʳ (dom Γ) r₂
    x₀∉u : x₀ ∉ fv u
    x₀∉u = ∉-++ˡ r₃
    r₄ = ∉-++ʳ (fv u) r₃
    x₀∉u′ : x₀ ∉ fv u′
    x₀∉u′ = ∉-++ˡ r₄
    x₀∉t : x₀ ∉ fv t
    x₀∉t = ∉-++ʳ (fv u′) r₄

    ua = uniform lt d
    ub = uniform (F₀ x₀∉L₀) (F x₀∉L)
    lw : LC (u′ ^ fvar x₀)
    lw = ⟶ᵉ-lc (F₀ x₀∉L₀) (F x₀∉L)

    Body : Name → Set
    Body y = Σ[ d′ ∈ ((y , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar y) ⟶ᵉ (u′ ^ fvar y) ] Sized d′ (proj₁ (proj₂ ub))

    bodyΣ : ∀ {y} → y ∉ (x₀ ∷ A) → Body y
    bodyΣ {y} y∉ = fix (rename-headˢ {b = u} x₀ y x₀∉Γ y∉Γ x₀∉t x₀∉u (λ ()) lw (proj₁ ub) (proj₂ (proj₂ ub)))
      where
        y∉Γ : y ∉ dom Γ
        y∉Γ = ∉-++ˡ (∉-++ʳ L₀ (∉-++ʳ L (∉-tail y∉)))
        fix : Σ[ d′ ∈ ((y , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar y) ⟶ᵉ ((closeRec 0 x₀ (u′ ^ fvar x₀)) ^ fvar y) ]
                Sized d′ (proj₁ (proj₂ ub))
            → Body y
        fix h rewrite close-open 0 x₀ u′ x₀∉u′ = h

    result : Uniform (Me-Fun {t' = t′} {u' = u′} L d F)
    result = Me-Fun (x₀ ∷ A) (proj₁ ua) (λ y∉ → proj₁ (bodyΣ y∉))
           , suc (proj₁ (proj₂ ua) + proj₁ (proj₂ ub))
           , proj₁ (proj₂ ua) , proj₁ (proj₂ ub) , proj₂ (proj₂ ua) , (λ y∉ → proj₂ (bodyΣ y∉)) , refl

uniform {Γ} (lc-lam {t = t} {b = b} L₀ lt F₀) (Me-FOp {s = s} {α = α} {t = t₁} {t' = t′} {u = u} {u' = u′} L d F) = result
  where
    A = L ++ L₀ ++ dom Γ ++ fv u ++ fv u′ ++ fv t ++ fv α ++ fvStack s
    x₀ = fresh A
    a∉ = fresh-∉ A
    x₀∉L  = ∉-++ˡ a∉
    r₁ = ∉-++ʳ L a∉
    x₀∉L₀ = ∉-++ˡ r₁
    r₂ = ∉-++ʳ L₀ r₁
    x₀∉Γ : x₀ ∉ dom Γ
    x₀∉Γ = ∉-++ˡ r₂
    r₃ = ∉-++ʳ (dom Γ) r₂
    x₀∉u : x₀ ∉ fv u
    x₀∉u = ∉-++ˡ r₃
    r₄ = ∉-++ʳ (fv u) r₃
    x₀∉u′ : x₀ ∉ fv u′
    x₀∉u′ = ∉-++ˡ r₄
    r₅ = ∉-++ʳ (fv u′) r₄
    x₀∉t : x₀ ∉ fv t
    x₀∉t = ∉-++ˡ r₅
    r₆ = ∉-++ʳ (fv t) r₅
    x₀∉α : x₀ ∉ fv α
    x₀∉α = ∉-++ˡ r₆
    x₀∉s : x₀ ∉ fvStack s
    x₀∉s = ∉-++ʳ (fv α) r₆

    ua = uniform lt d
    ub = uniform (F₀ x₀∉L₀) (F x₀∉L)
    lw : LC (u′ ^ fvar x₀)
    lw = ⟶ᵉ-lc (F₀ x₀∉L₀) (F x₀∉L)

    Body : Name → Set
    Body y = Σ[ d′ ∈ ((y , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar y) ⟶ᵉ (u′ ^ fvar y) ] Sized d′ (proj₁ (proj₂ ub))

    bodyΣ : ∀ {y} → y ∉ (x₀ ∷ A) → Body y
    bodyΣ {y} y∉ = fix (rename-headˢ {b = u} x₀ y x₀∉Γ y∉Γ x₀∉α x₀∉u x₀∉s lw (proj₁ ub) (proj₂ (proj₂ ub)))
      where
        y∉Γ : y ∉ dom Γ
        y∉Γ = ∉-++ˡ (∉-++ʳ L₀ (∉-++ʳ L (∉-tail y∉)))
        fix : Σ[ d′ ∈ ((y , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar y) ⟶ᵉ ((closeRec 0 x₀ (u′ ^ fvar x₀)) ^ fvar y) ]
                Sized d′ (proj₁ (proj₂ ub))
            → Body y
        fix h rewrite close-open 0 x₀ u′ x₀∉u′ = h

    result : Uniform (Me-FOp {t' = t′} {u' = u′} L d F)
    result = Me-FOp (x₀ ∷ A) (proj₁ ua) (λ y∉ → proj₁ (bodyΣ y∉))
           , suc (proj₁ (proj₂ ua) + proj₁ (proj₂ ub))
           , proj₁ (proj₂ ua) , proj₁ (proj₂ ub) , proj₂ (proj₂ ua) , (λ y∉ → proj₂ (bodyΣ y∉)) , refl

uniform {Γ} {s} (lc-app (lc-lam {t = t} {b = b} L₀ lt F₀) lv) (Me-Bet {t = t₁} {u = u} {u' = u′} {v = w} {v' = w′} L F e) = result
  where
    A = L ++ L₀ ++ dom Γ ++ fv u ++ fv u′
    x₀ = fresh A
    a∉ = fresh-∉ A
    x₀∉L  = ∉-++ˡ a∉
    r₁ = ∉-++ʳ L a∉
    x₀∉L₀ = ∉-++ˡ r₁
    r₂ = ∉-++ʳ L₀ r₁
    x₀∉Γ : x₀ ∉ dom Γ
    x₀∉Γ = ∉-++ˡ r₂
    r₃ = ∉-++ʳ (dom Γ) r₂
    x₀∉u : x₀ ∉ fv u
    x₀∉u = ∉-++ˡ r₃
    x₀∉u′ : x₀ ∉ fv u′
    x₀∉u′ = ∉-++ʳ (fv u) r₃

    ue = uniform lv e
    ub = uniform (F₀ x₀∉L₀) (F x₀∉L)
    lw : LC (u′ ^ fvar x₀)
    lw = ⟶ᵉ-lc (F₀ x₀∉L₀) (F x₀∉L)

    Body : Name → Set
    Body y = Σ[ d′ ∈ Γ ∣ s ⊢ (u ^ fvar y) ⟶ᵉ (u′ ^ fvar y) ] Sized d′ (proj₁ (proj₂ ub))

    bodyΣ : ∀ {y} → y ∉ (x₀ ∷ A) → Body y
    bodyΣ {y} y∉ = fix (close-rename₀ˢ {u = u} x₀ y x₀∉Γ x₀∉u lw (proj₁ ub) (proj₂ (proj₂ ub)))
      where
        fix : Σ[ d′ ∈ Γ ∣ s ⊢ (u ^ fvar y) ⟶ᵉ ((closeRec 0 x₀ (u′ ^ fvar x₀)) ^ fvar y) ]
                Sized d′ (proj₁ (proj₂ ub))
            → Body y
        fix h rewrite close-open 0 x₀ u′ x₀∉u′ = h

    result : Uniform (Me-Bet {t = t} {u' = u′} L F e)
    result = Me-Bet {t = t} {u' = u′} (x₀ ∷ A) (λ y∉ → proj₁ (bodyΣ y∉)) (proj₁ ue)
           , suc (proj₁ (proj₂ ub) + proj₁ (proj₂ ue))
           , proj₁ (proj₂ ub) , proj₁ (proj₂ ue) , (λ y∉ → proj₂ (bodyΣ y∉)) , proj₂ (proj₂ ue) , refl
```

## Sized context reductions

```agda
SizedCtx : ∀ {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → Set
SizedCtx Ct-Refl      = ⊤
SizedCtx (Ct-Ann c e) = SizedCtx c × ∃[ n ] Sized e n
SizedCtx (Ct-Stk c e) = SizedCtx c × ∃[ n ] Sized e n

uniformCtx : ∀ {Γ s Γ' s'} → Γ prevalid → All LC s → (c : Γ ∣ s ↣ Γ' ∣ s')
           → Σ[ c′ ∈ Γ ∣ s ↣ Γ' ∣ s' ] SizedCtx c′
uniformCtx pv ls Ct-Refl = Ct-Refl , tt
uniformCtx pv ls (Ct-Ann c e) with uniformCtx (tail-prevalid pv) ls c | uniform (head-lc pv) e
... | c′ , sc | e′ , n , se = Ct-Ann c′ e′ , sc , n , se
uniformCtx pv (lα ∷ ls) (Ct-Stk c e) with uniformCtx pv ls c | uniform lα e
... | c′ , sc | e′ , n , se = Ct-Stk c′ e′ , sc , n , se

stack-lc : ∀ {Γ s} → Γ ∣ s prevalid → All LC s
stack-lc (Pv-Nil _)        = []
stack-lc (Pv-Sta pv lα _)  = lα ∷ stack-lc pv
```

## What this establishes

`uniform` and `uniformCtx`: any equivalence derivation on a locally closed subject, and any
context reduction of a prevalid configuration, can be replaced by one with the same conclusion
whose binder families are uniformly sized. With `MPSS/Sized`, this is what lets the mixed
diamond's induction measure count derivation nodes.
