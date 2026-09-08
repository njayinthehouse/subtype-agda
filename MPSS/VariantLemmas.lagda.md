# MPSS: the standard lemmas for the variant relation

The variant `⟶ᵉ′` of `MPSS/EmptyStackPro` needs the same infrastructure as `⟶ᵉ` where a
derivation of the variant has to be *built*: context weakening, reflexivity, renaming of a bound
name, and wrapping a single body step under a binder. Where only a *fact about* a variant
derivation is needed — its prevalidity, local closure or scoping of its target — the embedding
`⟶ᵉ′⊆⟶ᵉ` and the original lemma serve. Each construction below follows its original clause by
clause (`MPSS/Weakening`, `MPSS/StackPush`, `MPSS/Rename`, `MPSS/Wrap`); the only new clause is
`Me-Pro′`, whose premise is at the empty stack.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantLemmas where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Close using (open-close; fv-close)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.StackPush using (prevalid-cons; dom-++; fv-lam-ann; fv-lam-body; fv-app-op; fv-app-arg; fv-open-cons)
open import MPSS.Weakening using (∈-weaken; dom-⊑)
open import MPSS.Rename using (prevalid-rename; ∈-substCtx; substCtx; substStack; substStack-id;
                               x∉-w; x∉-domΔ; x∉-domΓ; x∉-boundΓ; rename-fvar; open-rename)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ)
```

## Facts, through the embedding

```agda
⟶ᵉ′-prevalid : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ′ v → Γ ∣ s prevalid
⟶ᵉ′-prevalid d = ⟶ᵉ-prevalid (⟶ᵉ′⊆⟶ᵉ d)

⟶ᵉ′-lc : ∀ {Γ s u v} → LC u → Γ ∣ s ⊢ u ⟶ᵉ′ v → LC v
⟶ᵉ′-lc lu d = ⟶ᵉ-lc lu (⟶ᵉ′⊆⟶ᵉ d)

fv-⟶ᵉ′ : ∀ {Γ s t t′ N} → dom Γ ⊑ N → Γ ∣ s ⊢ t ⟶ᵉ′ t′ → fv t ⊑ N → fv t′ ⊑ N
fv-⟶ᵉ′ dn d ft = fv-⟶ᵉ dn (⟶ᵉ′⊆⟶ᵉ d) ft
```

## Weakening

```agda
⟶ᵉ′-weaken : ∀ (Δ Θ : Ctx) {Γ s u v}
           → (Δ ++ Θ ++ Γ) ∣ s prevalid
           → (Δ ++ Γ) ∣ s ⊢ u ⟶ᵉ′ v
           → (Δ ++ Θ ++ Γ) ∣ s ⊢ u ⟶ᵉ′ v
⟶ᵉ′-weaken Δ Θ pv (Me-Var′ _)      = Me-Var′ pv
⟶ᵉ′-weaken Δ Θ pv (Me-Top′ _)      = Me-Top′ pv
⟶ᵉ′-weaken Δ Θ pv (Me-TAp′ _)      = Me-TAp′ pv
⟶ᵉ′-weaken Δ Θ pv (Me-Pro′ _ m d)  =
  Me-Pro′ pv (∈-weaken Δ Θ m) (⟶ᵉ′-weaken Δ Θ (prevalid-nil pv) d)
⟶ᵉ′-weaken Δ Θ pv (Me-App′ d e)    =
  Me-App′ (⟶ᵉ′-weaken Δ Θ pv′ d) (⟶ᵉ′-weaken Δ Θ (prevalid-nil pv) e)
  where
    inner = ⟶ᵉ′-prevalid d
    pv′ = Pv-Sta pv (prevalid-head-lc inner) (λ h → dom-⊑ Δ Θ (prevalid-head-fv inner h))
⟶ᵉ′-weaken Δ Θ pv (Me-Bet′ {u' = u'} L F e) =
  Me-Bet′ {u' = u'} L (λ x∉ → ⟶ᵉ′-weaken Δ Θ pv (F x∉))
          (⟶ᵉ′-weaken Δ Θ (prevalid-nil pv) e)
⟶ᵉ′-weaken Δ Θ {Γ} pv (Me-Fun′ {t = t} {u = u} {u' = u'} L d F) =
  Me-Fun′ (L ++ dom (Δ ++ Θ ++ Γ)) (⟶ᵉ′-weaken Δ Θ pv d) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ∣ [] ⊢ (u ^ fvar y) ⟶ᵉ′ (u' ^ fvar y)
    body {y} y∉ = ⟶ᵉ′-weaken ((y , sub , t) ∷ Δ) Θ pv′ (F (∉-++ˡ y∉))
      where
        inner : ((y , sub , t) ∷ Δ ++ Γ) prevalid
        inner = prevalid-ctx (⟶ᵉ′-prevalid (F (∉-++ˡ y∉)))
        pv′ : ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ∣ [] prevalid
        pv′ = Pv-Nil (Pv-Ctx (prevalid-ctx pv) (∉-++ʳ L y∉) (head-lc inner)
                             (λ h → dom-⊑ Δ Θ (head-fv inner h)))
⟶ᵉ′-weaken Δ Θ {Γ} pv (Me-FOp′ {s = s} {α = α} {u = u} {u' = u'} L d F) =
  Me-FOp′ (L ++ dom (Δ ++ Θ ++ Γ)) (⟶ᵉ′-weaken Δ Θ (prevalid-nil pv) d) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , eqv , α) ∷ Δ ++ Θ ++ Γ) ∣ s ⊢ (u ^ fvar y) ⟶ᵉ′ (u' ^ fvar y)
    body {y} y∉ = ⟶ᵉ′-weaken ((y , eqv , α) ∷ Δ) Θ pv′ (F (∉-++ˡ y∉))
      where
        pv′ : ((y , eqv , α) ∷ Δ ++ Θ ++ Γ) ∣ s prevalid
        pv′ = prevalid-cons (prevalid-pop pv) (∉-++ʳ L y∉)
                            (prevalid-head-lc pv) (prevalid-head-fv pv)
```

## Reflexivity

```agda
⟶ᵉ′-refl : ∀ {Γ s t} → Γ ∣ s prevalid → LC t → fv t ⊑ dom Γ → Γ ∣ s ⊢ t ⟶ᵉ′ t
⟶ᵉ′-refl pv lc-fvar        f = Me-Var′ pv
⟶ᵉ′-refl pv lc-Top         f = Me-Top′ pv
⟶ᵉ′-refl pv (lc-app {u} {v} lu lv) f =
  Me-App′ (⟶ᵉ′-refl (Pv-Sta pv lv (fv-app-arg {u} {v} f)) lu (fv-app-op {u} {v} f))
          (⟶ᵉ′-refl (prevalid-nil pv) lv (fv-app-arg {u} {v} f))
⟶ᵉ′-refl {Γ} {[]} pv (lc-lam {t} {b} L lt F) f =
  Me-Fun′ (L ++ dom Γ) (⟶ᵉ′-refl pv lt (fv-lam-ann {t} {b} f)) body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ′ (b ^ fvar x)
    body {x} x∉ =
      ⟶ᵉ′-refl (prevalid-cons pv (∉-++ʳ L x∉) lt (fv-lam-ann {t} {b} f))
               (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))
⟶ᵉ′-refl {Γ} {α ∷ s} pv (lc-lam {t} {b} L lt F) f =
  Me-FOp′ (L ++ dom Γ) (⟶ᵉ′-refl (prevalid-nil pv) lt (fv-lam-ann {t} {b} f)) body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ′ (b ^ fvar x)
    body {x} x∉ =
      ⟶ᵉ′-refl (prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                              (prevalid-head-lc pv) (prevalid-head-fv pv))
               (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))

refl-head′ : ∀ {Γ s v} → Γ ∣ (v ∷ s) prevalid → Γ ∣ [] ⊢ v ⟶ᵉ′ v
refl-head′ pv = ⟶ᵉ′-refl (prevalid-nil pv) (prevalid-head-lc pv) (prevalid-head-fv pv)
```

## Renaming a bound name

The one difference from `MPSS/Rename` is in `Me-Pro′`: the premise is at the empty stack, and
`substStack x (fvar y) []` is `[]` by definition.

```agda
⟶ᵉ′-rename : ∀ (Δ : Ctx) {Γ x y a w s u v}
           → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
           → (Δ ++ (x , a , w) ∷ Γ) ∣ s ⊢ u ⟶ᵉ′ v
           → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
               ⊢ (u [ x := fvar y ]) ⟶ᵉ′ (v [ x := fvar y ])

⟶ᵉ′-rename Δ {Γ} {x} {y} y∉ (Me-Var′ {x = z} pv)
  rewrite proj₂ (rename-fvar x y z) = Me-Var′ (prevalid-rename Δ y∉ pv)

⟶ᵉ′-rename Δ y∉ (Me-Top′ pv) = Me-Top′ (prevalid-rename Δ y∉ pv)

⟶ᵉ′-rename Δ y∉ (Me-TAp′ pv) = Me-TAp′ (prevalid-rename Δ y∉ pv)

⟶ᵉ′-rename Δ {Γ} {x} {y} {a} {w} {s} y∉ (Me-Pro′ {_} {_} {z} {α} {α'} pv mem d)
  with ∈-++⁻ Δ mem
... | inj₁ m = pro-Δ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ (prevalid-ctx pv) (subst (_∈ dom Δ) (sym p) (∈-dom m))

    pro-Δ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ᵉ′ (α' [ x := fvar y ])
    pro-Δ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Me-Pro′ (prevalid-rename Δ y∉ pv)
              (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m))
              (⟶ᵉ′-rename Δ y∉ d)
... | inj₂ (here refl) = pro-self
  where
    ih : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ []
           ⊢ w ⟶ᵉ′ (α' [ x := fvar y ])
    ih = subst (λ q → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ []
                        ⊢ q ⟶ᵉ′ (α' [ x := fvar y ]))
               (subst-fresh {w} x (fvar y) (x∉-w Δ (prevalid-ctx pv)))
               (⟶ᵉ′-rename Δ y∉ d)

    pro-self : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                 ⊢ ((fvar x) [ x := fvar y ]) ⟶ᵉ′ (α' [ x := fvar y ])
    pro-self rewrite subst-fvar-≡ {x} (fvar y) =
      Me-Pro′ (prevalid-rename Δ y∉ pv)
              (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl))
              ih
... | inj₂ (there m) = pro-Γ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ (prevalid-ctx pv) (subst (_∈ dom Γ) (sym p) (∈-dom m))

    ih : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ []
           ⊢ α ⟶ᵉ′ (α' [ x := fvar y ])
    ih = subst (λ q → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ []
                        ⊢ q ⟶ᵉ′ (α' [ x := fvar y ]))
               (subst-fresh {α} x (fvar y) (x∉-boundΓ Δ (prevalid-ctx pv) m))
               (⟶ᵉ′-rename Δ y∉ d)

    pro-Γ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ᵉ′ (α' [ x := fvar y ])
    pro-Γ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Me-Pro′ (prevalid-rename Δ y∉ pv)
              (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m))
              ih

⟶ᵉ′-rename Δ y∉ (Me-App′ d e) = Me-App′ (⟶ᵉ′-rename Δ y∉ d) (⟶ᵉ′-rename Δ y∉ e)

⟶ᵉ′-rename Δ {Γ} {x} {y} {a} {w} {s} y∉ (Me-Bet′ {_} {_} {t} {u} {u'} {v} {v'} L F e) = result
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ′ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ′-rename Δ y∉ (F (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        transport : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ᵉ′ ((u' ^ fvar z) [ x := fvar y ])
                  → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ′ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h

    result : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
               ⊢ ((app (lam t u) v) [ x := fvar y ]) ⟶ᵉ′ ((u' ^ v') [ x := fvar y ])
    result rewrite subst-open (lc-fvar {y}) 0 v' u' x =
      Me-Bet′ {u' = u' [ x := fvar y ]} (x ∷ L) body (⟶ᵉ′-rename Δ y∉ e)

⟶ᵉ′-rename Δ {Γ} {x} {y} {a} {w} y∉ (Me-Fun′ {_} {t} {t'} {u} {u'} L d F) =
  Me-Fun′ (x ∷ y ∷ L) (⟶ᵉ′-rename Δ y∉ d) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ′ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ′-rename ((z , sub , t) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , sub , t) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        transport : ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ᵉ′ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ′ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h

⟶ᵉ′-rename Δ {Γ} {x} {y} {a} {w} y∉ (Me-FOp′ {_} {s} {β} {t} {t'} {u} {u'} L d F) =
  Me-FOp′ (x ∷ y ∷ L) (⟶ᵉ′-rename Δ y∉ d) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
             ∣ substStack x (fvar y) s
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ′ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ′-rename ((z , eqv , β) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , eqv , β) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        transport : ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ᵉ′ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ′ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h
```

## The head form, and wrapping under a binder

```agda
⟶ᵉ′-rename-head : ∀ {Γ s b w a α} x y
                → x ∉ dom Γ → y ∉ dom Γ → x ∉ fv α → x ∉ fv b → x ∉ fvStack s → LC w
                → ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ′ w
                → ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ᵉ′ ((closeRec 0 x w) ^ fvar y)
⟶ᵉ′-rename-head {Γ} {s} {b} {w} {a} {α} x y x∉Γ y∉Γ x∉α x∉b x∉s lw d with x ≟ y
... | yes refl = d'
  where
    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ′ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d
... | no x≢y = result
  where
    y∉ : y ∉ dom ([] ++ (x , a , α) ∷ Γ)
    y∉ (here p)  = x≢y (sym p)
    y∉ (there h) = y∉Γ h

    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ′ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d

    renamed : ((y , a , α) ∷ Γ) ∣ substStack x (fvar y) s
                ⊢ ((b ^ fvar x) [ x := fvar y ]) ⟶ᵉ′ (((closeRec 0 x w) ^ fvar x) [ x := fvar y ])
    renamed = ⟶ᵉ′-rename [] y∉ d'

    result : ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ᵉ′ ((closeRec 0 x w) ^ fvar y)
    result rewrite sym (substStack-id x (fvar y) s x∉s)
                 | subst-intro {b} (lc-fvar {y}) x x∉b
                 | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
                 = renamed

wrapᵉ′-fun : ∀ {Γ w a a′} x → x ∉ dom Γ → LC a → LC a′
           → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ′ a′
           → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ᵉ′ lam w (closeRec 0 x a′)
wrapᵉ′-fun {Γ} {w} {a} {a′} x x∉Γ la la′ d =
  Me-Fun′ (dom Γ) (⟶ᵉ′-refl (Pv-Nil (tail-prevalid pv)) (head-lc pv) (head-fv pv)) fam
  where
    pv = prevalid-ctx (⟶ᵉ′-prevalid d)

    d′ : ((x , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ᵉ′ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ᵉ′ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ᵉ′-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) (λ ()) la′ d′

wrapᵉ′-fop : ∀ {Γ s w α a a′} x → x ∉ dom Γ → x ∉ fvStack s → LC a → LC a′
           → LC w → fv w ⊑ dom Γ
           → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ᵉ′ a′
           → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ᵉ′ lam w (closeRec 0 x a′)
wrapᵉ′-fop {Γ} {s} {w} {α} {a} {a′} x x∉Γ x∉s la la′ lw fw d =
  Me-FOp′ (dom Γ) (⟶ᵉ′-refl (Pv-Nil (tail-prevalid pv)) lw fw) fam
  where
    pv = prevalid-ctx (⟶ᵉ′-prevalid d)

    d′ : ((x , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ᵉ′ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ᵉ′ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ᵉ′-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) x∉s la′ d′
```

## What this establishes

For the variant relation: `⟶ᵉ′-weaken`, `⟶ᵉ′-refl`, `⟶ᵉ′-rename`, `⟶ᵉ′-rename-head`,
`wrapᵉ′-fun`, `wrapᵉ′-fop`, and the three facts that come through the embedding. These are what
`MPSS/Peel` needs to turn a derivation of the original relation into a chain of variant steps.
