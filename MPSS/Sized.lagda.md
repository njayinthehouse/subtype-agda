# MPSS: uniformly sized equivalence derivations

A measure for the mixed diamond (`MPSS/MixedDiamond`) has to count the nodes of an original
derivation. The size of a derivation with cofinitely quantified binder premises is not well
defined by choosing one fresh name, because a family may have members of different sizes at
different names, and the recursion opens each binder at a name chosen later. So the size is a
*relation*: `Sized d n` says every member of every family in `d` has the size the relation
assigns. Every derivation has a uniformly sized copy with the same conclusion (`uniform`, in
`MPSS/Uniform`), built by renaming one member to all names; the renaming, weakening and
reflexivity constructions preserve the relation, which is what this module proves.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Sized where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.StackPush using (⟶ᵉ-refl; prevalid-cons; fv-lam-ann; fv-lam-body; fv-open-cons)
open import MPSS.VariantMeasure using (tsize; tsize-open)
open import MPSS.Rename
  using (substCtx; substStack; rename-fvar; open-rename; prevalid-rename;
         x∉-domΔ; x∉-domΓ; x∉-w; x∉-boundΓ; ∈-substCtx; substStack-id)
open import PSS.Syntax using (subst-fresh; subst-fvar-≢; subst-fvar-≡; subst-intro; subst-open;
                              lc-fvar; ∉-tail; ∉-++ˡ; ∉-++ʳ; closeRec)
open import PSS.Close using (open-close; fv-close)
```

## The relation

Defined by recursion on the derivation, as `MPSS/Strengthen`'s `Avoids` is, so that using it
never asks Agda to unify a derivation's indices — the target of `Me-Bet` is an opening, which
the unifier cannot invert.

```agda
Sized : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ v → ℕ → Set
Sized (Me-Var _)       n = n ≡ 1
Sized (Me-Top _)       n = n ≡ 1
Sized (Me-TAp _)       n = n ≡ 1
Sized (Me-Pro _ _ d)   n = ∃[ k ] (Sized d k × n ≡ suc k)
Sized (Me-App d e)     n = ∃[ k ] ∃[ l ] (Sized d k × Sized e l × n ≡ suc (k + l))
Sized (Me-Bet L F e)   n =
  ∃[ k ] ∃[ l ] ((∀ {x} (x∉ : x ∉ L) → Sized (F x∉) k) × Sized e l × n ≡ suc (k + l))
Sized (Me-Fun L d F)   n =
  ∃[ k ] ∃[ l ] (Sized d k × (∀ {x} (x∉ : x ∉ L) → Sized (F x∉) l) × n ≡ suc (k + l))
Sized (Me-FOp L d F)   n =
  ∃[ k ] ∃[ l ] (Sized d k × (∀ {x} (x∉ : x ∉ L) → Sized (F x∉) l) × n ≡ suc (k + l))
```

Transporting along an equality of indices keeps the size.

```agda
sized-subst-src : ∀ {Γ s u u′ v n} (eq : u ≡ u′) {d : Γ ∣ s ⊢ u ⟶ᵉ v}
                → Sized d n → Sized (subst (λ z → Γ ∣ s ⊢ z ⟶ᵉ v) eq d) n
sized-subst-src refl sd = sd

sized-subst-tgt : ∀ {Γ s u v v′ n} (eq : v ≡ v′) {d : Γ ∣ s ⊢ u ⟶ᵉ v}
                → Sized d n → Sized (subst (λ z → Γ ∣ s ⊢ u ⟶ᵉ z) eq d) n
sized-subst-tgt refl sd = sd
```

## Weakening preserves the size

`⟶ᵉ-weaken` maps every member of a family pointwise, so a uniform size stays uniform. The
derivation is matched first, so that the size's index is determined before its constructor is.

```agda
Sized-weaken : ∀ (Δ Θ : Ctx) {Γ s u v n} (pv : (Δ ++ Θ ++ Γ) ∣ s prevalid)
               (d : (Δ ++ Γ) ∣ s ⊢ u ⟶ᵉ v) → Sized d n
             → Sized (⟶ᵉ-weaken Δ Θ pv d) n
Sized-weaken Δ Θ pv (Me-Var _)      sd = sd
Sized-weaken Δ Θ pv (Me-Top _)      sd = sd
Sized-weaken Δ Θ pv (Me-TAp _)      sd = sd
Sized-weaken Δ Θ pv (Me-Pro _ m d)  (k , sd , eq) = k , Sized-weaken Δ Θ pv d sd , eq
Sized-weaken Δ Θ pv (Me-App d e)    (k , l , sd , se , eq) =
  k , l , Sized-weaken Δ Θ _ d sd , Sized-weaken Δ Θ _ e se , eq
Sized-weaken Δ Θ pv (Me-Bet L F e)  (k , l , sF , se , eq) =
  k , l , (λ x∉ → Sized-weaken Δ Θ pv (F x∉) (sF x∉)) , Sized-weaken Δ Θ _ e se , eq
Sized-weaken Δ Θ {Γ} pv (Me-Fun L d F) (k , l , sd , sF , eq) =
  k , l , Sized-weaken Δ Θ pv d sd
  , (λ {y} y∉ → Sized-weaken (_ ∷ Δ) Θ _ (F (∉-++ˡ y∉)) (sF (∉-++ˡ y∉))) , eq
Sized-weaken Δ Θ {Γ} pv (Me-FOp L d F) (k , l , sd , sF , eq) =
  k , l , Sized-weaken Δ Θ _ d sd
  , (λ {y} y∉ → Sized-weaken (_ ∷ Δ) Θ _ (F (∉-++ˡ y∉)) (sF (∉-++ˡ y∉))) , eq
```

## Reflexivity has the size of the term

```agda
Sized-refl : ∀ {Γ s t} (pv : Γ ∣ s prevalid) (lt : LC t) (f : fv t ⊑ dom Γ)
           → Sized (⟶ᵉ-refl pv lt f) (tsize t)
Sized-refl pv lc-fvar f = refl
Sized-refl pv lc-Top  f = refl
Sized-refl pv (lc-app {u} {v} lu lv) f =
  tsize u , tsize v
  , Sized-refl (Pv-Sta pv lv (fv-app-arg {u} {v} f)) lu (fv-app-op {u} {v} f)
  , Sized-refl (prevalid-nil pv) lv (fv-app-arg {u} {v} f) , refl
  where open import MPSS.StackPush using (fv-app-arg; fv-app-op)
Sized-refl {Γ} {[]} pv (lc-lam {t} {b} L lt F) f =
  tsize t , tsize b , Sized-refl pv lt (fv-lam-ann {t} {b} f)
  , (λ {x} x∉ → subst (Sized (⟶ᵉ-refl (prevalid-cons pv (∉-++ʳ L x∉) lt (fv-lam-ann {t} {b} f))
                                       (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))))
                       (tsize-open 0 x b)
                       (Sized-refl (prevalid-cons pv (∉-++ʳ L x∉) lt (fv-lam-ann {t} {b} f))
                                   (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))))
  , refl
Sized-refl {Γ} {α ∷ s} pv (lc-lam {t} {b} L lt F) f =
  tsize t , tsize b , Sized-refl (prevalid-nil pv) lt (fv-lam-ann {t} {b} f)
  , (λ {x} x∉ → subst (Sized (⟶ᵉ-refl (pvx x∉) (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))))
                       (tsize-open 0 x b)
                       (Sized-refl (pvx x∉) (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))))
  , refl
  where
    pvx : ∀ {x} → x ∉ (L ++ dom Γ) → ((x , eqv , α) ∷ Γ) ∣ s prevalid
    pvx x∉ = prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉) (prevalid-head-lc pv) (prevalid-head-fv pv)
```

## Renaming a bound name preserves the size

`MPSS/Rename`'s `⟶ᵉ-rename`, with the size carried along. The output is a new derivation, since
the original lemma rewrites inside local definitions that a proof about it cannot reach.

```agda
Renamed : ∀ (Δ : Ctx) {Γ x y a w s u v} → ℕ → Set
Renamed Δ {Γ} {x} {y} {a} {w} {s} {u} {v} n =
  Σ[ d′ ∈ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
            ⊢ (u [ x := fvar y ]) ⟶ᵉ (v [ x := fvar y ]) ] Sized d′ n

renameˢ : ∀ (Δ : Ctx) {Γ x y a w s u v n}
        → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
        → (d : (Δ ++ (x , a , w) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v) → Sized d n
        → Renamed Δ {Γ} {x} {y} {a} {w} {s} {u} {v} n

renameˢ Δ {Γ} {x} {y} y∉ (Me-Var {x = z} pv) sd
  rewrite proj₂ (rename-fvar x y z) = Me-Var (prevalid-rename Δ y∉ pv) , sd

renameˢ Δ y∉ (Me-Top pv) sd = Me-Top (prevalid-rename Δ y∉ pv) , sd

renameˢ Δ y∉ (Me-TAp pv) sd = Me-TAp (prevalid-rename Δ y∉ pv) , sd

renameˢ Δ {Γ} {x} {y} {a} {w} {s} y∉ (Me-Pro {x = z} {α = α} {α' = α′} pv mem d) (k , sd , eqn)
  with ∈-++⁻ Δ mem
... | inj₁ m = pro-Δ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ (prevalid-ctx pv) (subst (_∈ dom Δ) (sym p) (∈-dom m))

    ih = renameˢ Δ y∉ d sd

    pro-Δ : Renamed Δ {Γ} {x} {y} {a} {w} {s} {fvar z} {α′} _
    pro-Δ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Me-Pro (prevalid-rename Δ y∉ pv) (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m)) (proj₁ ih)
      , k , proj₂ ih , eqn
... | inj₂ (here refl) = pro-self
  where
    ih = renameˢ Δ y∉ d sd
    eq = subst-fresh {w} x (fvar y) (x∉-w Δ (prevalid-ctx pv))

    ih′ : Σ[ d′ ∈ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                    ⊢ w ⟶ᵉ (α′ [ x := fvar y ]) ] Sized d′ _
    ih′ = subst (λ q → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                          ⊢ q ⟶ᵉ (α′ [ x := fvar y ])) eq (proj₁ ih)
        , sized-subst-src eq (proj₂ ih)

    pro-self : Renamed Δ {Γ} {x} {y} {a} {w} {s} {fvar x} {α′} _
    pro-self rewrite subst-fvar-≡ {x} (fvar y) =
      Me-Pro (prevalid-rename Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl)) (proj₁ ih′)
      , k , proj₂ ih′ , eqn
... | inj₂ (there m) = pro-Γ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ (prevalid-ctx pv) (subst (_∈ dom Γ) (sym p) (∈-dom m))

    ih = renameˢ Δ y∉ d sd
    eq = subst-fresh {α} x (fvar y) (x∉-boundΓ Δ (prevalid-ctx pv) m)

    ih′ : Σ[ d′ ∈ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                    ⊢ α ⟶ᵉ (α′ [ x := fvar y ]) ] Sized d′ _
    ih′ = subst (λ q → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                          ⊢ q ⟶ᵉ (α′ [ x := fvar y ])) eq (proj₁ ih)
        , sized-subst-src eq (proj₂ ih)

    pro-Γ : Renamed Δ {Γ} {x} {y} {a} {w} {s} {fvar z} {α′} _
    pro-Γ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Me-Pro (prevalid-rename Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m)) (proj₁ ih′)
      , k , proj₂ ih′ , eqn

renameˢ Δ y∉ (Me-App d e) (k , l , sd , se , eqn) with renameˢ Δ y∉ d sd | renameˢ Δ y∉ e se
... | o′ , so′ | p′ , sp′ = Me-App o′ p′ , k , l , so′ , sp′ , eqn

renameˢ Δ {Γ} {x} {y} {a} {w} {s} y∉ (Me-Bet {t = t} {u = u} {u' = u′} {v = v} {v' = v′} L F e)
        (k , l , sF , se , eqn) = result
  where
    Body : Name → Set
    Body z = Σ[ d′ ∈ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u′ [ x := fvar y ]) ^ fvar z) ]
              Sized d′ k

    bodyΣ : ∀ {z} → z ∉ (x ∷ L) → Body z
    bodyΣ {z} z∉ = transport (renameˢ Δ y∉ (F (∉-tail z∉)) (sF (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        transport : Renamed Δ {Γ} {x} {y} {a} {w} {s} {u ^ fvar z} {u′ ^ fvar z} k → Body z
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u′) = h

    ihp = renameˢ Δ y∉ e se

    result : Renamed Δ {Γ} {x} {y} {a} {w} {s} {app (lam t u) v} {u′ ^ v′} _
    result rewrite subst-open (lc-fvar {y}) 0 v′ u′ x =
      Me-Bet {u' = u′ [ x := fvar y ]} (x ∷ L) (λ z∉ → proj₁ (bodyΣ z∉)) (proj₁ ihp)
      , k , l , (λ z∉ → proj₂ (bodyΣ z∉)) , proj₂ ihp , eqn

renameˢ Δ {Γ} {x} {y} {a} {w} y∉ (Me-Fun {t = t} {t' = t′} {u = u} {u' = u′} L d F) (k , l , sd , sF , eqn) =
  Me-Fun (x ∷ y ∷ L) (proj₁ iha) (λ z∉ → proj₁ (bodyΣ z∉))
  , k , l , proj₂ iha , (λ z∉ → proj₂ (bodyΣ z∉)) , eqn
  where
    iha = renameˢ Δ y∉ d sd

    Body : Name → Set
    Body z = Σ[ d′ ∈ ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u′ [ x := fvar y ]) ^ fvar z) ]
              Sized d′ l

    bodyΣ : ∀ {z} → z ∉ (x ∷ y ∷ L) → Body z
    bodyΣ {z} z∉ = transport (renameˢ ((z , sub , t) ∷ Δ) y∉′ (F (∉-tail (∉-tail z∉)))
                                                              (sF (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉′ : y ∉ dom ((z , sub , t) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉′ (here p)  = y≢z p
        y∉′ (there h) = y∉ h

        transport : Renamed ((z , sub , t) ∷ Δ) {Γ} {x} {y} {a} {w} {[]} {u ^ fvar z} {u′ ^ fvar z} l
                  → Body z
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u′) = h

renameˢ Δ {Γ} {x} {y} {a} {w} y∉ (Me-FOp {s = s} {α = β} {t = t} {t' = t′} {u = u} {u' = u′} L d F)
        (k , l , sd , sF , eqn) =
  Me-FOp (x ∷ y ∷ L) (proj₁ iha) (λ z∉ → proj₁ (bodyΣ z∉))
  , k , l , proj₂ iha , (λ z∉ → proj₂ (bodyΣ z∉)) , eqn
  where
    iha = renameˢ Δ y∉ d sd

    Body : Name → Set
    Body z = Σ[ d′ ∈ ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u′ [ x := fvar y ]) ^ fvar z) ]
              Sized d′ l

    bodyΣ : ∀ {z} → z ∉ (x ∷ y ∷ L) → Body z
    bodyΣ {z} z∉ = transport (renameˢ ((z , eqv , β) ∷ Δ) y∉′ (F (∉-tail (∉-tail z∉)))
                                                              (sF (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉′ : y ∉ dom ((z , eqv , β) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉′ (here p)  = y≢z p
        y∉′ (there h) = y∉ h

        transport : Renamed ((z , eqv , β) ∷ Δ) {Γ} {x} {y} {a} {w} {s} {u ^ fvar z} {u′ ^ fvar z} l
                  → Body z
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u′) = h
```
