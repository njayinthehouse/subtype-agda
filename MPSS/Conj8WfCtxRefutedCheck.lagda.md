# MPSS: the statement refuted, checked from outside

The declared type below is written out in full from `MPSS/WellFormed` and `MPSS/Conjecture8`
alone — not through `MPSS/WfCtx`'s abbreviation — and `MPSS/Conj8WfCtxRefuted`'s theorem is
checked against it.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conj8WfCtxRefutedCheck where

open import Relation.Nullary using (¬_)
open import Data.Product.Base using (_×_; _,_)

open import MPSS.WellFormed
open import MPSS.Conjecture8 using (CoCtx; plug)
open import MPSS.WfCtx using (WfCtx)
open import MPSS.Conj8WfCtxRefuted using (¬Conj-8ʷᶜ)

check : ¬ (∀ {Γ u t} (C : CoCtx) → WfCtx Γ
           → LC u → LC t
           → Γ ⊢ u ≤*wf t → Γ ⊢ plug C u wf → Γ ⊢ plug C t wf
           → Γ ⊢ plug C u ≤*wf plug C t)
check = ¬Conj-8ʷᶜ
```

## The term is the one Hurkens prints

Hurkens gives the lengths of `⊥`, `U`, `Δ`, `Ω` and of the whole proof term as 3, 15, 241, 145 and
2039 (p. 269: "the total number of applications, abstractions, products, and occurrences of
variables and sorts").

```agda
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import PSS.Syntax using (Tm; bvar; fvar; Top; lam; app)
open import MPSS.HurkensTerm

size : Tm → ℕ
size (bvar _)  = 1
size (fvar _)  = 1
size Top       = 1
size (lam a b) = suc (size a + size b)
size (app f v) = suc (size f + size v)

lengths : (size ⊥ᵗ ≡ 3) × (size U ≡ 15) × (size Δ ≡ 241) × (size Ω ≡ 145) × (size H ≡ 2039)
lengths = refl , refl , refl , refl , refl
```
