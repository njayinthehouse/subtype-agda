# MPSS: transitivity elimination

> **Theorem 3 (Transitivity elimination).** If `Γ;s ⊢ u ⊲* v` then `Γ;s ⊢ u ⊲ v`.

The paper's route, and v1's: transitivity of the single-step relation, proved by pushing an
equivalence step along the left of a derivation, which is where the two commutation results are
spent. Both are assumed here — see `MPSS/Assumed` — so this module says exactly that Theorem 3
follows from Lemmas 1 and 2 and nothing else.

The two modes divide the work. Pushing past `As-Left-1` crosses a promotion, so it needs strong
commutation (Lemma 1); pushing past `As-Left-2` crosses another equivalence step, so it needs the
diamond (Lemma 2). Both are applied at `Ct-Refl`, the identity context reduction: transitivity
never needs to move the context, only to close a local peak.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Transitivity where

open import Data.Product.Base using (_×_; _,_)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Assumed using (Lem-1; Lem-2)

module _ (lem-1 : Lem-1) (lem-2 : Lem-2) where
```

## Pushing an equivalence step along the left

> If `Γ;s ⊢ u ⟶≡ u′` and `Γ;s ⊢ u ⊲ t`, then `Γ;s ⊢ u′ ⊲ t`.

At `As-Refl` the step is turned around and re-read on the right: `u′ ⊲ u′` and `u ⟶≡ u′` give
`u′ ⊲ u` by `As-Right`. At a left step the peak `u′ ⟵ u ⟶ t₂` is closed by commutation, and the
derivation continues from the common reduct.

```agda
  push≡ : ∀ {Γ s u u' t m}
        → Γ ∣ s ⊢ u ⟶ᵉ u'
        → Γ ∣ s ⊢ u ⊲[ m ] t
        → Γ ∣ s ⊢ u' ⊲[ m ] t
  push≡ e (As-Refl pv)      = As-Right (As-Refl pv) e
  push≡ e (As-Right d e₁)   = As-Right (push≡ e d) e₁
  push≡ e (As-Left-1 st d)  with lem-1 e st Ct-Refl
  ... | _ , eʳ , stʳ        = As-Left-1 stʳ (push≡ eʳ d)
  push≡ e (As-Left-2 e₁ d)  with lem-2 e e₁ Ct-Refl Ct-Refl
  ... | _ , eˡ , eʳ         = As-Left-2 eˡ (push≡ eʳ d)
```

## Transitivity of the single-step relation

```agda
  ⊲-trans : ∀ {Γ s v u t m}
          → Γ ∣ s ⊢ v ⊲[ m ] u
          → Γ ∣ s ⊢ u ⊲[ m ] t
          → Γ ∣ s ⊢ v ⊲[ m ] t
  ⊲-trans (As-Refl _)      d₂ = d₂
  ⊲-trans (As-Left-1 st d) d₂ = As-Left-1 st (⊲-trans d d₂)
  ⊲-trans (As-Left-2 e d)  d₂ = As-Left-2 e (⊲-trans d d₂)
  ⊲-trans (As-Right d e)   d₂ = ⊲-trans d (push≡ e d₂)
```

The last case is the one that consumes `push≡`: `As-Right` leaves the right-hand side one
equivalence step ahead of where the second derivation starts, and that step has to be moved onto
the second derivation before the two can be joined.

## Theorem 3

```agda
  Thm-3 : ∀ {Γ s u v m} → Γ ∣ s ⊢ u ⊲*[ m ] v → Γ ∣ s ⊢ u ⊲[ m ] v
  Thm-3 (Ast-Sub d)       = d
  Thm-3 (Ast-Trans d₁ d₂) = ⊲-trans (Thm-3 d₁) (Thm-3 d₂)
```

## What this establishes

Theorem 3, in both modes, from Lemmas 1 and 2. Also `⊲-trans` and `push≡`, which the inversion
lemma and Theorem 11 use directly.
