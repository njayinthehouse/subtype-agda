# MPSS, candidate C: `t₆` is not well-formed

`MPSS/Lem6WfCtxRefuted` refutes Lemma 6 for the paper's well-formedness with

    t₆ = (λx≤¬φ₀. x R₀ ⊤) L₀   ↦   L₀ R₀ ⊤ = H ⊤

where `H` is Hurkens' paradox: `t₆` is well-formed by Figure 4 and `H ⊤` is not. For candidate C's
judgement `Γ ∣ s ⊢ t wfˢ` (`MPSS/StackWf`), Lemma 6 is proved (`MPSS/StackWfPreservation`,
`Lem-6ˢ`), so `t₆` and `H ⊤` are well-formed together or not at all. This module shows: not at
all.

`Wc-App` on `H ⊤` asks `H ≤*wfˢ λt.⊤` at the stack `⊤ ∷ []`, which is one layer of the machine
relation by `Thm-3ˢ`. `H` has kind `S` (`MPSS/HurkensTerm`, `Hᵏ`), and a locally closed term of
kind `S` is below no abstraction at any stack (`MPSS/KindingTop`, `S-not-below-lam[]`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfRejects where

open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (proj₁)
open import Relation.Nullary using (¬_)

open import MPSS.Subtyping
open import MPSS.StackWf
open import MPSS.StackWfPreservation using (Lem-6ˢ)
open import MPSS.HurkensTerm using (H; Hᵏ; _·_)
open import MPSS.Lem6WfCtxRefuted using (t₆; step₆)
open import MPSS.KindingTop using (embed; S-not-below-lam[])
open import PSS.Syntax
```

## `H ⊤` is not well-formed

The local closure of `H` is read off the hypothesis (`≤*wfˢ⇒both`, `wfˢ⇒lc`).

```agda
¬wfˢ-H⊤ : ¬ ([] ∣ [] ⊢ H · Top wfˢ)
¬wfˢ-H⊤ (Wc-App d₁ _) =
  S-not-below-lam[] (wfˢ⇒lc (proj₁ (≤*wfˢ⇒both d₁))) (embed Hᵏ) (Thm-3ˢ d₁)
```

## `t₆` is not well-formed

```agda
¬wfˢ-t₆ : ¬ ([] ∣ [] ⊢ t₆ wfˢ)
¬wfˢ-t₆ w = ¬wfˢ-H⊤ (Lem-6ˢ (wfˢ⇒lc w) w step₆)
```

## What this establishes

- `¬wfˢ-H⊤`: `H ⊤` is not well-formed in candidate C, at the empty configuration.
- `¬wfˢ-t₆`: nor is `t₆`, the term that is well-formed by the paper's Figure 4 and whose reduct is
  not. So the counterexample of `MPSS/Lem6WfCtxRefuted` to Lemma 6 is not a term of candidate C:
  the judgement that reads the operand stack rejects it before it steps.

Nothing is assumed.
