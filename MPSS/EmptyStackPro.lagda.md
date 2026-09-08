# MPSS: equivalence reduction with promotion at the empty stack

The diamond's difficulty is located in one design choice (`../PLAN.md`, "What the positions
say"): `Me-Pro`'s premise reduces the annotation *at the current stack*, so an unfolded definition
can consume the pending operands in the same step, and the join recursion has to copy pieces under
the stack and may re-enter old material. This module defines the variant `⟶ᵉ′` in which the
premise is at the empty stack, and proves that a variant step is an original step. The converse,
that an original step is a chain of variant steps, is `MPSS/Peel`; together they say the two
relations have the same reflexive-transitive closure, which is all the machine relation `⊲` sees.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.EmptyStackPro where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Product.Base using (_,_)

open import MPSS.WellFormed
open import MPSS.StackPush using (pushᵉ)
```

## The variant

Every rule but `Me-Pro′` is the rule of `⟶ᵉ` with `⟶ᵉ′` in place of `⟶ᵉ`.

```agda
infix 3 _∣_⊢_⟶ᵉ′_
data _∣_⊢_⟶ᵉ′_ : Ctx → Stack → Tm → Tm → Set where

  Me-Var′ : ∀ {Γ s x}
          → Γ ∣ s prevalid
          → Γ ∣ s ⊢ fvar x ⟶ᵉ′ fvar x

  Me-Top′ : ∀ {Γ s}
          → Γ ∣ s prevalid
          → Γ ∣ s ⊢ Top ⟶ᵉ′ Top

  Me-Pro′ : ∀ {Γ s x α α'}
          → Γ ∣ s prevalid
          → x ≐ α ∈ Γ
          → Γ ∣ [] ⊢ α ⟶ᵉ′ α'
          → Γ ∣ s ⊢ fvar x ⟶ᵉ′ α'

  Me-App′ : ∀ {Γ s u u' v v'}
          → Γ ∣ (v ∷ s) ⊢ u ⟶ᵉ′ u'
          → Γ ∣ [] ⊢ v ⟶ᵉ′ v'
          → Γ ∣ s ⊢ app u v ⟶ᵉ′ app u' v'

  Me-TAp′ : ∀ {Γ s u}
          → Γ ∣ s prevalid
          → Γ ∣ s ⊢ app Top u ⟶ᵉ′ Top

  Me-Bet′ : ∀ {Γ s t u u' v v'} (L : List Name)
          → (∀ {x} → x ∉ L → Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ (u' ^ fvar x))
          → Γ ∣ [] ⊢ v ⟶ᵉ′ v'
          → Γ ∣ s ⊢ app (lam t u) v ⟶ᵉ′ (u' ^ v')

  Me-Fun′ : ∀ {Γ t t' u u'} (L : List Name)
          → Γ ∣ [] ⊢ t ⟶ᵉ′ t'
          → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶ᵉ′ (u' ^ fvar x))
          → Γ ∣ [] ⊢ lam t u ⟶ᵉ′ lam t' u'

  Me-FOp′ : ∀ {Γ s α t t' u u'} (L : List Name)
          → Γ ∣ [] ⊢ t ⟶ᵉ′ t'
          → (∀ {x} → x ∉ L → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ (u' ^ fvar x))
          → Γ ∣ (α ∷ s) ⊢ lam t u ⟶ᵉ′ lam t' u'
```

## A variant step is an original step

The premise of `Me-Pro′` is pushed under the stack by stack-monotonicity (`pushᵉ`), which is
valid because the conclusion's stack is prevalid.

```agda
⟶ᵉ′⊆⟶ᵉ : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ′ v → Γ ∣ s ⊢ u ⟶ᵉ v
⟶ᵉ′⊆⟶ᵉ (Me-Var′ pv)        = Me-Var pv
⟶ᵉ′⊆⟶ᵉ (Me-Top′ pv)        = Me-Top pv
⟶ᵉ′⊆⟶ᵉ (Me-Pro′ pv m d)    = Me-Pro pv m (pushᵉ (⟶ᵉ′⊆⟶ᵉ d) pv)
⟶ᵉ′⊆⟶ᵉ (Me-App′ d e)       = Me-App (⟶ᵉ′⊆⟶ᵉ d) (⟶ᵉ′⊆⟶ᵉ e)
⟶ᵉ′⊆⟶ᵉ (Me-TAp′ pv)        = Me-TAp pv
⟶ᵉ′⊆⟶ᵉ (Me-Bet′ {u' = u'} L F e) =
  Me-Bet {u' = u'} L (λ x∉ → ⟶ᵉ′⊆⟶ᵉ (F x∉)) (⟶ᵉ′⊆⟶ᵉ e)
⟶ᵉ′⊆⟶ᵉ (Me-Fun′ {u' = u'} L d F) =
  Me-Fun {u' = u'} L (⟶ᵉ′⊆⟶ᵉ d) (λ x∉ → ⟶ᵉ′⊆⟶ᵉ (F x∉))
⟶ᵉ′⊆⟶ᵉ (Me-FOp′ {u' = u'} L d F) =
  Me-FOp {u' = u'} L (⟶ᵉ′⊆⟶ᵉ d) (λ x∉ → ⟶ᵉ′⊆⟶ᵉ (F x∉))
```

## What this establishes

`⟶ᵉ′ ⊆ ⟶ᵉ`, one step to one step. The variant is a restriction of the original relation, not a
different one: it forbids only the interaction of an unfolded definition with the pending operands
inside the step that unfolds it.
