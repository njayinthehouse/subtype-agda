# MPSS: narrowing a promotion, and Lemma 24's missing conclusion

`MPSS/Narrowing24` proves the first two conclusions of Lemma 24 — the new promotion and the join.
The third, that the new target is well-formed, is the one `MPSS/AUDIT` records as unestablished,
and it is the one Lemma 23 cannot do without. This module supplies it.

Narrowing is easier than substitution in one respect that shapes everything below: it changes no
*terms*, only an annotation in the context. So the dichotomy of Lemmas 29 and 30 carries over with
no `subst-open` transport at all, and the `CoPair` condition — reused verbatim from
`MPSS/CoPair` — decides it.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Narrow24 where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Rename using (prevalid-suffix)
open import MPSS.Subst28 using (inject)
open import MPSS.SubstDrop using (no-sub-x)
open import MPSS.Narrowing using (prevalid-narrowˢ; Lem-25; ann-lc; ann-fv)
open import MPSS.CoPair using (CoPair; cp-var; cp-fun; cp-app; coPair?; cp-open₀)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ-dom)

open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ; ∉-tail)
```

## Membership survives narrowing

Only the narrowed entry changes, and it is reached only through its own name.

```agda
∈-narrow : ∀ (Δ : Ctx) {Γ x t t' z b w}
         → z ≢ x
         → (z , b , w) ∈ (Δ ++ (x , sub , t) ∷ Γ)
         → (z , b , w) ∈ (Δ ++ (x , sub , t') ∷ Γ)
∈-narrow Δ z≢x m with ∈-++⁻ Δ m
... | inj₁ p           = ∈-++⁺ˡ p
... | inj₂ (here refl) = ⊥-elim (z≢x refl)
... | inj₂ (there p)   = ∈-++⁺ʳ Δ (there p)
```

## The freshness a binder case needs

```agda
z∉ann : ∀ (Δ : Ctx) {Γ x t z}
      → (Δ ++ (x , sub , t) ∷ Γ) prevalid
      → z ∉ dom (Δ ++ (x , sub , t) ∷ Γ)
      → z ∉ fv t
z∉ann Δ {Γ} {x} {t} pv z∉ h =
  z∉ (inject Δ ((x , sub , t) ∷ Γ) (inj₂ (there (head-fv (prevalid-suffix Δ pv) h))))
```

## Narrowing a promotion, off the covariant pattern

Every rule but `Ms-Pro` transfers verbatim; `Ms-Pro` on the narrowed variable is exactly the
`CoPair` the hypothesis excludes.

```agda
⟶ˢ-narrow : ∀ (Δ : Ctx) {Γ x t t' s u v}
          → Γ ∣ [] ⊢ t ⟶ᵉ t'
          → ¬ CoPair x t u v
          → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ˢ v
          → (Δ ++ (x , sub , t') ∷ Γ) ∣ s ⊢ u ⟶ˢ v

⟶ˢ-narrow Δ {Γ} {x} {t} {t'} e nc (Ms-Pro {x = y} pv m) = go (x ≟ y)
  where
    ctx = prevalid-ctx pv
    pv' = prevalid-narrowˢ Δ (⟶ᵉ-lc (ann-lc Δ ctx) e) (fv-⟶ᵉ-dom e (ann-fv Δ ctx)) pv

    go : Dec (x ≡ y) → (Δ ++ (x , sub , t') ∷ Γ) ∣ _ ⊢ fvar y ⟶ˢ _
    go (yes refl) = ⊥-elim (nc (tr (no-sub-x Δ ctx m)))
      where
        tr : ∀ {w} → w ≡ t → CoPair x t (fvar x) w
        tr refl = cp-var
    go (no q) = Ms-Pro pv' (∈-narrow Δ (λ p → q (sym p)) m)

⟶ˢ-narrow Δ {Γ} {x} {t} {t'} e nc (Ms-Top pv) =
  Ms-Top (prevalid-narrowˢ Δ (⟶ᵉ-lc (ann-lc Δ ctx) e) (fv-⟶ᵉ-dom e (ann-fv Δ ctx)) pv)
  where ctx = prevalid-ctx pv

⟶ˢ-narrow Δ {Γ} {x} {t} {t'} e nc (Ms-Equ pv d) =
  Ms-Equ (prevalid-narrowˢ Δ (⟶ᵉ-lc (ann-lc Δ ctx) e) (fv-⟶ᵉ-dom e (ann-fv Δ ctx)) pv)
         (Lem-25 Δ e d)
  where ctx = prevalid-ctx pv

⟶ˢ-narrow Δ e nc (Ms-App st) = Ms-App (⟶ˢ-narrow Δ e (λ c → nc (cp-app c)) st)

⟶ˢ-narrow Δ {Γ} {x} {t} {t'} e nc (Ms-Fun {t = w} {u = u} {u' = u′} L F) =
  Ms-Fun (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , sub , w) ∷ Δ ++ (x , sub , t') ∷ Γ) ∣ []
             ⊢ (u ^ fvar z) ⟶ˢ (u′ ^ fvar z)
    body {z} z∉ = ⟶ˢ-narrow ((z , sub , w) ∷ Δ) e nc′ (F z∉L)
      where
        z∉L  = ∉-++ˡ (∉-tail z∉)
        z∉u  = ∉-++ˡ (∉-++ʳ L (∉-tail z∉))
        z∉u′ = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))
        z∉Γ  = ∉-++ʳ (fv u′) (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))

        z≢x : z ≢ x
        z≢x p = z∉ (here p)

        ctx : (Δ ++ (x , sub , t) ∷ Γ) prevalid
        ctx = tail-prevalid (prevalid-ctx (⟶ˢ-prevalid (F z∉L)))

        nc′ : ¬ CoPair x t (u ^ fvar z) (u′ ^ fvar z)
        nc′ c = nc (cp-fun (cp-open₀ 0 z u u′ z≢x (z∉ann Δ ctx z∉Γ) z∉u z∉u′ c))

⟶ˢ-narrow Δ {Γ} {x} {t} {t'} e nc (Ms-FOp {s = s} {α = β} {t = w} {u = u} {u' = u′} L F) =
  Ms-FOp (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv u ++ fv u′ ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , eqv , β) ∷ Δ ++ (x , sub , t') ∷ Γ) ∣ s
             ⊢ (u ^ fvar z) ⟶ˢ (u′ ^ fvar z)
    body {z} z∉ = ⟶ˢ-narrow ((z , eqv , β) ∷ Δ) e nc′ (F z∉L)
      where
        z∉L  = ∉-++ˡ (∉-tail z∉)
        z∉u  = ∉-++ˡ (∉-++ʳ L (∉-tail z∉))
        z∉u′ = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))
        z∉Γ  = ∉-++ʳ (fv u′) (∉-++ʳ (fv u) (∉-++ʳ L (∉-tail z∉)))

        z≢x : z ≢ x
        z≢x p = z∉ (here p)

        ctx : (Δ ++ (x , sub , t) ∷ Γ) prevalid
        ctx = tail-prevalid (prevalid-ctx (⟶ˢ-prevalid (F z∉L)))

        nc′ : ¬ CoPair x t (u ^ fvar z) (u′ ^ fvar z)
        nc′ c = nc (cp-fun (cp-open₀ 0 z u u′ z≢x (z∉ann Δ ctx z∉Γ) z∉u z∉u′ c))
```

## The dichotomy

```agda
narrow-split : ∀ (Δ : Ctx) {Γ x t t' s u v}
             → Γ ∣ [] ⊢ t ⟶ᵉ t'
             → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ˢ v
             → CoPair x t u v
             ⊎ ((Δ ++ (x , sub , t') ∷ Γ) ∣ s ⊢ u ⟶ˢ v)
narrow-split Δ {x = x} {t = t} {u = u} {v = v} e d with coPair? x t u v
... | yes c = inj₁ c
... | no  q = inj₂ (⟶ˢ-narrow Δ e q d)
```

## What this establishes

`⟶ˢ-narrow`, the narrowing counterpart of Lemma 30, and the split that separates it from the case
Lemma 24's third conclusion has to handle. Off the covariant pattern the promotion transfers with
its target unchanged, so its well-formedness is the hypothesis's and there is nothing to prove;
the work is all in the covariant case, where the target really does move from `Co[t]` to `Co[t′]`.
