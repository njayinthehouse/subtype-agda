# MPSS: scoping and uniqueness of annotations

Two small facts the diamond needs. Equivalence reduction keeps a term scoped in the context —
`Me-Pro` replaces a variable by an annotation, which prevalidity scopes, and `Me-Bet` substitutes
an operand that was already scoped. And a prevalid context records at most one annotation per
name, so two `Me-Pro` steps on the same variable read the same annotation.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Preserve where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import PSS.Scope using (fv-open-lower; fv-open-split)
open import PSS.Syntax using (subst-open)
```

## Annotations are unique

```agda
ann-unique : ∀ {Γ x a α β} → Γ prevalid → (x , a , α) ∈ Γ → (x , a , β) ∈ Γ → α ≡ β
ann-unique (Pv-Ctx _ x∉ _ _) (here refl) (here refl) = refl
ann-unique (Pv-Ctx _ x∉ _ _) (here refl) (there n)   = ⊥-elim (x∉ (∈-dom n))
ann-unique (Pv-Ctx _ x∉ _ _) (there m)   (here refl) = ⊥-elim (x∉ (∈-dom m))
ann-unique (Pv-Ctx pv _ _ _) (there m)   (there n)   = ann-unique pv m n
ann-unique (Pv-EqA _ x∉ _ _) (here refl) (here refl) = refl
ann-unique (Pv-EqA _ x∉ _ _) (here refl) (there n)   = ⊥-elim (x∉ (∈-dom n))
ann-unique (Pv-EqA _ x∉ _ _) (there m)   (here refl) = ⊥-elim (x∉ (∈-dom m))
ann-unique (Pv-EqA pv _ _ _) (there m)   (there n)   = ann-unique pv m n
```

## Equivalence reduction preserves scoping

Stated against an ambient name list rather than `dom Γ` directly. The generalisation is forced by
`Me-Bet`, whose body premise is taken in a context that does not bind the parameter
(`MPSS/BetaScope`): the opened body is scoped only in `dom Γ` together with that name, so the
invariant has to allow extra names.

```agda
fv-⟶ᵉ : ∀ {Γ s t t′ N} → dom Γ ⊑ N → Γ ∣ s ⊢ t ⟶ᵉ t′ → fv t ⊑ N → fv t′ ⊑ N
fv-⟶ᵉ dn (Me-Var _)      ft = ft
fv-⟶ᵉ dn (Me-Top _)      ft = ft
fv-⟶ᵉ dn (Me-TAp _)      ft = λ ()
fv-⟶ᵉ dn (Me-Pro pv m d) ft =
  fv-⟶ᵉ dn d (λ h → dn (prevalid-bound-fv (prevalid-ctx pv) m h))

fv-⟶ᵉ {t = app u v} dn (Me-App {u' = u′} d e) ft h with ∈-++⁻ (fv u′) h
... | inj₁ p = fv-⟶ᵉ dn d (λ q → ft (∈-++⁺ˡ q)) p
... | inj₂ p = fv-⟶ᵉ dn e (λ q → ft (∈-++⁺ʳ (fv u) q)) p

fv-⟶ᵉ {Γ} {t = lam a b} {N = N} dn (Me-Fun {t = t₀} {t' = a′} {u = u} {u' = u′} L d F) ft h
  with ∈-++⁻ (fv a′) h
... | inj₁ p = fv-⟶ᵉ dn d (λ q → ft (∈-++⁺ˡ q)) p
... | inj₂ p = body p
  where
    A    = L ++ fv u′
    x    = fresh A
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ L (fresh-∉ A)

    dn′ : dom ((x , sub , t₀) ∷ Γ) ⊑ (x ∷ N)
    dn′ (here refl) = here refl
    dn′ (there q)   = there (dn q)

    ftb : fv (u ^ fvar x) ⊑ (x ∷ N)
    ftb q with fv-open-split 0 (fvar x) u q
    ... | inj₁ r           = there (ft (∈-++⁺ʳ (fv a) r))
    ... | inj₂ (here refl) = here refl

    inner : fv (u′ ^ fvar x) ⊑ (x ∷ N)
    inner = fv-⟶ᵉ dn′ (F x∉L) ftb

    body : ∀ {y} → y ∈ fv u′ → y ∈ N
    body {y} q with inner (fv-open-lower 0 (fvar x) u′ q)
    ... | here refl = ⊥-elim (x∉u′ q)
    ... | there r   = r

fv-⟶ᵉ {Γ} {t = lam a b} {N = N} dn (Me-FOp {α = α} {t' = a′} {u = u} {u' = u′} L d F) ft h
  with ∈-++⁻ (fv a′) h
... | inj₁ p = fv-⟶ᵉ dn d (λ q → ft (∈-++⁺ˡ q)) p
... | inj₂ p = body p
  where
    A    = L ++ fv u′
    x    = fresh A
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ L (fresh-∉ A)

    dn′ : dom ((x , eqv , α) ∷ Γ) ⊑ (x ∷ N)
    dn′ (here refl) = here refl
    dn′ (there q)   = there (dn q)

    ftb : fv (u ^ fvar x) ⊑ (x ∷ N)
    ftb q with fv-open-split 0 (fvar x) u q
    ... | inj₁ r           = there (ft (∈-++⁺ʳ (fv a) r))
    ... | inj₂ (here refl) = here refl

    inner : fv (u′ ^ fvar x) ⊑ (x ∷ N)
    inner = fv-⟶ᵉ dn′ (F x∉L) ftb

    body : ∀ {y} → y ∈ fv u′ → y ∈ N
    body {y} q with inner (fv-open-lower 0 (fvar x) u′ q)
    ... | here refl = ⊥-elim (x∉u′ q)
    ... | there r   = r

fv-⟶ᵉ {Γ} {t = app (lam a b) w} {N = N} dn (Me-Bet {u = u} {u' = u′} {v' = w′} L F e) ft h
  with fv-open-split 0 w′ u′ h
... | inj₂ q = fv-⟶ᵉ dn e (λ r → ft (∈-++⁺ʳ (fv (lam a b)) r)) q
... | inj₁ q = body q
  where
    A    = L ++ fv u′
    x    = fresh A
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ L (fresh-∉ A)

    dn′ : dom Γ ⊑ (x ∷ N)
    dn′ q = there (dn q)

    ftb : fv (u ^ fvar x) ⊑ (x ∷ N)
    ftb r with fv-open-split 0 (fvar x) u r
    ... | inj₁ p           = there (ft (∈-++⁺ˡ (∈-++⁺ʳ (fv a) p)))
    ... | inj₂ (here refl) = here refl

    inner : fv (u′ ^ fvar x) ⊑ (x ∷ N)
    inner = fv-⟶ᵉ dn′ (F x∉L) ftb

    body : ∀ {y} → y ∈ fv u′ → y ∈ N
    body {y} r with inner (fv-open-lower 0 (fvar x) u′ r)
    ... | here refl = ⊥-elim (x∉u′ r)
    ... | there p   = p
```

The form the diamond uses.

```agda
fv-⟶ᵉ-dom : ∀ {Γ s t t′} → Γ ∣ s ⊢ t ⟶ᵉ t′ → fv t ⊑ dom Γ → fv t′ ⊑ dom Γ
fv-⟶ᵉ-dom = fv-⟶ᵉ (λ h → h)
```

## What this establishes

`ann-unique` — a prevalid context records one annotation per name, so two `Me-Pro` steps on the
same variable read the same term. `fv-⟶ᵉ` — equivalence reduction keeps a term scoped, stated
against an ambient list because `Me-Bet` reduces its body in a context that does not bind the
parameter.
