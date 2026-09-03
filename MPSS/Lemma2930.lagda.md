# MPSS: Lemmas 29 and 30, as one dichotomy

> **Lemma 29 (Promotion under substitution outside of covariant contexts).** Let
> `Γ, x≤t, Γ′; nil ⊢ Co[x] ⟶≤ Co[t]` be a derivation for some covariant context `Co`. Then
> `Γ, x≤t, Γ′[x\α]; nil ⊢ Co₍ₓ∖α₎[x] ⟶≤ Co₍ₓ∖α₎[t]`.
>
> **Lemma 30 (Promotion under substitution inside of covariant contexts).** If
> `Γ, x≤t, Γ′; s ⊢ u ⟶≤ v` and this derivation is NOT of the form `Co[x] ⟶≤ Co[t]`, then
> `Γ, Γ′[x\α]; s[x\α] ⊢ u[x\α] ⟶≤ v[x\α]`.

The two are stated as a case split on a property of a *derivation*, which is not a usable
hypothesis: it cannot be carried into the cofinite family of an abstraction rule, where different
witnesses could in principle take different rules. `MPSS/CoPair` replaces it by the corresponding
property of the source and target *terms*, which is decidable and does carry.

That makes the two lemmas one statement — a dichotomy, decided before the induction rather than
during it. Lemma 9 uses it exactly this way: the left branch hands Conjecture 8 its covariant
context, and the right branch hands `Ws-Lf2` a promotion.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Lemma2930 where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Rename using (substCtx; substStack; prevalid-suffix)
open import MPSS.Subst28 using (Lem-28-stk; inject)
open import MPSS.SubstDrop using (⟶ᵉ-drop; ∈-drop; no-sub-x)
open import MPSS.CoPair using (CoPair; cp-var; cp-fun; cp-app; coPair?; cp-open₀)

open import PSS.Syntax using (subst-open; subst-fvar-≢; ∉-++ˡ; ∉-++ʳ; ∉-tail)
```

## The freshness a binder case needs

`t` is the annotation of the entry being removed, so it is scoped in `Γ` and a name fresh for the
whole context is fresh for it.

```agda
z∉ann : ∀ (Δ : Ctx) {Γ x t z}
      → (Δ ++ (x , sub , t) ∷ Γ) prevalid
      → z ∉ dom (Δ ++ (x , sub , t) ∷ Γ)
      → z ∉ fv t
z∉ann Δ {Γ} {x} {t} pv z∉ h =
  z∉ (inject Δ ((x , sub , t) ∷ Γ) (inj₂ (there (head-fv (prevalid-suffix Δ pv) h))))
```

## Promotion, off the covariant pattern

```agda
⟶ˢ-drop′ : ∀ (Δ : Ctx) {Γ x t α s u v}
         → LC α → fv α ⊑ dom Γ
         → ¬ CoPair x t u v
         → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ˢ v
         → (substCtx x α Δ ++ Γ) ∣ (substStack x α s) ⊢ (u [ x := α ]) ⟶ˢ (v [ x := α ])

⟶ˢ-drop′ Δ {Γ} {x} {t} {α} lα fα nc (Ms-Pro {x = y} pv m) = go (x ≟ y)
  where
    go : Dec (x ≡ y) → (substCtx x α Δ ++ Γ) ∣ _ ⊢ ((fvar y) [ x := α ]) ⟶ˢ _
    go (yes refl) = ⊥-elim (nc (tr (no-sub-x Δ (prevalid-ctx pv) m)))
      where
        tr : ∀ {w} → w ≡ t → CoPair x t (fvar x) w
        tr refl = cp-var
    go (no q) rewrite subst-fvar-≢ {x} {y} α q =
      Ms-Pro (Lem-28-stk Δ lα fα pv) (∈-drop Δ (prevalid-ctx pv) (λ p → q (sym p)) m)

⟶ˢ-drop′ Δ lα fα nc (Ms-Top pv)   = Ms-Top (Lem-28-stk Δ lα fα pv)
⟶ˢ-drop′ Δ lα fα nc (Ms-Equ pv e) = Ms-Equ (Lem-28-stk Δ lα fα pv) (⟶ᵉ-drop Δ lα fα e)
⟶ˢ-drop′ Δ lα fα nc (Ms-App st)   = Ms-App (⟶ˢ-drop′ Δ lα fα (λ c → nc (cp-app c)) st)

⟶ˢ-drop′ Δ {Γ} {x} {t} {α} lα fα nc (Ms-Fun {t = w} {u = u} {u' = u′} L F) =
  Ms-Fun (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
             ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
    body {z} z∉ =
      tr (⟶ˢ-drop′ ((z , sub , w) ∷ Δ) lα fα nc′ (F z∉L))
      where
        z∉L  = ∉-++ˡ (∉-tail z∉)
        z∉u  = ∉-++ˡ (∉-++ʳ L (∉-tail z∉))
        z∉u′ = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))
        z∉Γ  = ∉-++ʳ (fv u′) (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))

        z≢x : z ≢ x
        z≢x p = z∉ (here p)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)

        ctx : (Δ ++ (x , sub , t) ∷ Γ) prevalid
        ctx = tail-prevalid (prevalid-ctx (⟶ˢ-prevalid (F z∉L)))

        nc′ : ¬ CoPair x t (u ^ fvar z) (u′ ^ fvar z)
        nc′ c = nc (cp-fun (cp-open₀ 0 z u u′ z≢x (z∉ann Δ ctx z∉Γ) z∉u z∉u′ c))

        eq  = trans (subst-open lα 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))
        eq′ = trans (subst-open lα 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := α ])) (subst-fvar-≢ α x≢z))

        tr : ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
               ⊢ ((u ^ fvar z) [ x := α ]) ⟶ˢ ((u′ ^ fvar z) [ x := α ])
           → ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
               ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
        tr h rewrite sym eq | sym eq′ = h

⟶ˢ-drop′ Δ {Γ} {x} {t} {α} lα fα nc
         (Ms-FOp {s = s} {α = β} {t = w} {u = u} {u' = u′} L F) =
  Ms-FOp (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
             ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
    body {z} z∉ =
      tr (⟶ˢ-drop′ ((z , eqv , β) ∷ Δ) lα fα nc′ (F z∉L))
      where
        z∉L  = ∉-++ˡ (∉-tail z∉)
        z∉u  = ∉-++ˡ (∉-++ʳ L (∉-tail z∉))
        z∉u′ = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))
        z∉Γ  = ∉-++ʳ (fv u′) (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))

        z≢x : z ≢ x
        z≢x p = z∉ (here p)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)

        ctx : (Δ ++ (x , sub , t) ∷ Γ) prevalid
        ctx = tail-prevalid (prevalid-ctx (⟶ˢ-prevalid (F z∉L)))

        nc′ : ¬ CoPair x t (u ^ fvar z) (u′ ^ fvar z)
        nc′ c = nc (cp-fun (cp-open₀ 0 z u u′ z≢x (z∉ann Δ ctx z∉Γ) z∉u z∉u′ c))

        eq  = trans (subst-open lα 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))
        eq′ = trans (subst-open lα 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := α ])) (subst-fvar-≢ α x≢z))

        tr : ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u ^ fvar z) [ x := α ]) ⟶ˢ ((u′ ^ fvar z) [ x := α ])
           → ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
        tr h rewrite sym eq | sym eq′ = h
```

## The dichotomy

```agda
Lem-29-30 : ∀ (Δ : Ctx) {Γ x t α s u v}
          → LC α → fv α ⊑ dom Γ
          → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ˢ v
          → CoPair x t u v
          ⊎ ((substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ (u [ x := α ]) ⟶ˢ (v [ x := α ]))
Lem-29-30 Δ {x = x} {t = t} {u = u} {v = v} lα fα d with coPair? x t u v
... | yes c = inj₁ c
... | no  q = inj₂ (⟶ˢ-drop′ Δ lα fα q d)
```

## What this establishes

Lemmas 29 and 30 together, with the case split decided on the terms. The `Ms-Pro` case is the
whole content of the split: promoting the removed variable yields its own annotation, by
`no-sub-x`, and that is precisely `CoPair` at the empty context — so a derivation that promotes
`x` is excluded by the hypothesis rather than assumed away.
