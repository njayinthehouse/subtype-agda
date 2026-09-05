# MPSS: configuration depth, then term depth

`AUDIT.md`'s fourth candidate for Lemma 2's induction is lexicographic on three components:

> configuration depth `max(ρ u, maxᵢ (1 + ρ sᵢ))`, then term depth, then derivation size

with `ρ` the unfolding depth of a term — each variable worth one more than its annotation. The
audit's verdict: "`Me-Pro` decreases the second component and `Me-App` the third, but `Me-FOp`
increases the second while leaving the first equal, since the bound variable's weight `1 + ρ α` is
exactly the stack entry's contribution."

The first two components are `MPSS/Height`'s `M` and `htm`, exactly. So the claim is that at
`Me-FOp` the pair `(M, htm)` does not decrease lexicographically. That is what this module checks;
the third component cannot rescue a pair that has gone up.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.LexDepth where

open import Data.Nat.Base using (ℕ; _≤_; _<_; s≤s; z≤n)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∉_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.Height using (M; htm)
```

## The order

Non-strict, since the claim is only that the induction does not go *up* at a structural rule.

```agda
Lex≤ : ℕ × ℕ → ℕ × ℕ → Set
Lex≤ (a , b) (c , d) = a < c ⊎ (a ≡ c × b ≤ d)

Me-FOp-lex : Set
Me-FOp-lex = ∀ Γ {z w α} s b → z ∉ dom Γ → z ∉ fv b → z ∉ fvStack s
           → Lex≤ (M ((z , eqv , α) ∷ Γ) s (b ^ fvar z) , htm ((z , eqv , α) ∷ Γ) (b ^ fvar z))
                  (M Γ (α ∷ s) (lam w b) , htm Γ (lam w b))
```

## The counterexample

`λ⊤. x` with `⊤` on the stack. The configuration depth is `1` on both sides — the stack entry's
`1 + ρ ⊤` before, the bound variable's `1 + ρ ⊤` after. The term depth goes from `0` to `1`.

```agda
lex-fop-false : ¬ Me-FOp-lex
lex-fop-false h
  with h [] {z = 0} {w = Top} {α = Top} [] (bvar 0) (λ ()) (λ ()) (λ ())
... | inj₁ (s≤s ())
... | inj₂ (refl , ())
```

## What this establishes

`(M, htm)` is not lexicographically non-increasing at `Me-FOp`: the first component ties and the
second goes up. So the triple the audit names does not order the diamond's induction at that rule,
whatever its third component. And its first component alone already fails elsewhere — `MPSS/Height`'s
`ht-app-false` is `Me-App` increasing `M`.

This is the audit's fourth bullet under "why the obvious repairs do not work", as code.
