# MPSS: no supertype of Top

> **Theorem 11 (No supertype of Top).** Let `Γ;s` be an extended context and `λx≤t.u` a term. We
> cannot have `Γ;s ⊢ Top ≤* λx≤t.u`.

The paper proves it by first collapsing the transitive derivation with Theorem 3, so as printed
it sits downstream of transitivity elimination and hence of the commutation theorem. **The
single-step form needs none of that**, and is proved here outright: `Top` promotes only to
itself, an abstraction equivalence-reduces only to an abstraction, so the two never meet.
Theorem 11 as printed is then one application of Theorem 3 away, and is recorded below as a
corollary taking that theorem as a hypothesis.

This is the shape of v1's Theorem 4.3, which `PSS/Transitivity` proves the same way.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.TopLemma where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
```

## Top reduces only to Top

```agda
Top-⟶ᵉ : ∀ {Γ s w} → Γ ∣ s ⊢ Top ⟶ᵉ w → w ≡ Top
Top-⟶ᵉ (Me-Top _) = refl

Top-⟶ˢ : ∀ {Γ s w} → Γ ∣ s ⊢ Top ⟶ˢ w → w ≡ Top
Top-⟶ˢ (Ms-Top _)   = refl
Top-⟶ˢ (Ms-Equ _ e) = Top-⟶ᵉ e
```

## The single-step theorem

Every promotion out of `Top` lands on `Top`, and every equivalence step into an abstraction comes
from an abstraction, so the derivation can only ever be shortened, never closed.

```agda
Top≰lam : ∀ {Γ s a b} → ¬ (Γ ∣ s ⊢ Top ≤ lam a b)
Top≰lam (As-Left-1 (Ms-Top _) d)             = Top≰lam d
Top≰lam (As-Left-1 (Ms-Equ _ (Me-Top _)) d)  = Top≰lam d
Top≰lam (As-Right d (Me-Fun _ _ _))          = Top≰lam d
Top≰lam (As-Right d (Me-FOp _ _ _))          = Top≰lam d
```

The equivalence reading fails too, by the same argument with `As-Left-2`.

```agda
Top≉lam : ∀ {Γ s a b} → ¬ (Γ ∣ s ⊢ Top ≋ lam a b)
Top≉lam (As-Left-2 (Me-Top _) d)     = Top≉lam d
Top≉lam (As-Right d (Me-Fun _ _ _))  = Top≉lam d
Top≉lam (As-Right d (Me-FOp _ _ _))  = Top≉lam d
```

## Theorem 11

Stated as the paper does, over the transitive relation, with Theorem 3 as the hypothesis it is
proved from there.

```agda
Thm-3 : Set
Thm-3 = ∀ {Γ s u v m} → Γ ∣ s ⊢ u ⊲*[ m ] v → Γ ∣ s ⊢ u ⊲[ m ] v

Thm-11 : Thm-3 → ∀ {Γ s a b} → ¬ (Γ ∣ s ⊢ Top ⊲*[ sub-m ] lam a b)
Thm-11 trans d = Top≰lam (trans d)
```

## What this establishes

`Top≰lam` and `Top≉lam` — no abstraction is above `Top` in either reading of the single-step
relation, proved outright and independently of the commutation theorem. `Thm-11` is v2's
Theorem 11, reduced to Theorem 3 alone; that is the paper's own route, and the only part of it
that was not already available.
