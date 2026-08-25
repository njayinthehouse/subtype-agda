# MPSS: reduction of extended contexts

v2's Figure 3 — the relation the commutativity theorem quantifies over. It "captures the
evolution of annotations during reduction": an abstraction's annotation can itself reduce, so a
diagram completed at one context must be allowed to finish at a reduced one.

Two differences from v1's Figure 3, both consequences of changes already recorded in `MPSS/Diff`:

- annotations come in two kinds, so `Ct-Ann` carries the kind along unchanged;
- the equivalence steps in the premises are **context-indexed** (`Γ ∣ [] ⊢ t ⟶ᵉ t'`) where v1's
  were context-free.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CtxReduction where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import MPSS.Reduction
open import MPSS.Scope using (⟶ᵉ-lc)

len : Stack → ℕ
len []      = 0
len (_ ∷ s) = ℕ.suc (len s)
```

## The relation

```agda
infix 3 _∣_↣_∣_
data _∣_↣_∣_ : Ctx → Stack → Ctx → Stack → Set where

  Ct-Refl : ∀ {Γ s} → Γ ∣ s ↣ Γ ∣ s

  Ct-Ann  : ∀ {Γ s Γ' s' x c t t'}
          → Γ ∣ s ↣ Γ' ∣ s'
          → Γ ∣ [] ⊢ t ⟶ᵉ t'
          → ((x , c , t) ∷ Γ) ∣ s ↣ ((x , c , t') ∷ Γ') ∣ s'

  Ct-Stk  : ∀ {Γ s Γ' s' α α'}
          → Γ ∣ s ↣ Γ' ∣ s'
          → Γ ∣ [] ⊢ α ⟶ᵉ α'
          → Γ ∣ (α ∷ s) ↣ Γ' ∣ (α' ∷ s')
```

## Domains and annotation kinds are preserved

Reduction only rewrites the *terms* in a context; the binding structure is untouched. This is
what lets a lookup on the left be replayed on the right.

```agda
↣-dom : ∀ {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → dom Γ ≡ dom Γ'
↣-dom Ct-Refl        = refl
↣-dom (Ct-Ann d _)   = cong (_ ∷_) (↣-dom d)
↣-dom (Ct-Stk d _)   = ↣-dom d

↣-stack-len : ∀ {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → len s ≡ len s'
↣-stack-len Ct-Refl      = refl
↣-stack-len (Ct-Ann d _) = ↣-stack-len d
↣-stack-len (Ct-Stk d _) = cong ℕ.suc (↣-stack-len d)
```

## What this establishes

v2's Figure 3, and the two structural invariants every later proof leans on: context reduction
changes neither the domain nor the stack's length, only the terms recorded.

The two differences from v1's Figure 3 are exactly the ones `MPSS/Diff` proves are real —
annotations come in two kinds, and the equivalence premises are context-indexed rather than
decorative.
