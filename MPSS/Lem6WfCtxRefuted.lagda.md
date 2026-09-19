# MPSS: evaluation does not preserve well-formedness, even in the empty context

`MPSS/Conj8WfCtxRefuted` leaves `Lem-6ʷᶜ` and `Preservationʷᶜ` of `MPSS/WfCtx` open. They are
false, by one more application around the same term. With `H = [L₀ R₀]` Hurkens' paradox:

    t₆ = (λx≤¬φ₀. x R₀ ⊤) L₀   ↦   L₀ R₀ ⊤ = H ⊤

- `t₆` is well-formed. Under `x ≤ ¬φ₀` the operator `x R₀` is promoted to `(¬φ₀) R₀`, which reduces
  to `⊥ = λp≤⊤.p`, so it is below `λp≤⊤.⊤` and takes any operand; and `L₀ ≤*wf ¬φ₀`. This is the
  source calculus's *ex falso*: a proof of `⊥` applied to a proposition. (Found by the checker of
  `MPSS/CheckerFns`.)
- `H ⊤` is not well-formed: `Wf-App` wants `H ≤*wf λx≤d.⊤`, a chain of promotions from `H` to an
  abstraction, and there is none (`MPSS/PromotionNoWhnf`, `MPSS/HurkensTerm`).

So the β-step loses well-formedness: the body was well-formed because its parameter could be
promoted to its bound, and the operand that replaces the parameter cannot be.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Lem6WfCtxRefuted where

open import Data.List.Base using ([])
open import Data.Product.Base using (_,_)
open import Data.Bool.Base using (true)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.Unconditional using (Thm-3wf)
open import MPSS.Strip using (ε)
open import MPSS.WfCtx using (Lem-6ʷᶜ; Preservationʷᶜ; wc-nil)
open import MPSS.Conj8NoAbstraction using (NoAbs; no-chain)
open import MPSS.PromotionNoWhnf using (NR⇒NoAbs)
open import MPSS.CheckerFns using (wf?)
open import MPSS.CheckerSound using (wf-sound)
open import MPSS.HurkensTerm
open import MPSS.Conj8WfCtxRefuted using (wf-H; wf-L₀; wf-R₀; wf-¬φ₀)
open import PSS.Syntax
```

## The term and its step

```agda
t₆ : Tm
t₆ = ƛ 9 ¬φ₀ (fvar 9 · R₀ · Top) · L₀

abstract
  wf-t₆ : [] ⊢ t₆ wf
  wf-t₆ = wf-sound 200 300 Pv-Emp refl

lc-fun : ∀ {Γ f v} → Γ ⊢ app f v wf → LC f
lc-fun (Wf-App d _) = ⊑*wf⇒lcˡ d

step₆ : t₆ ↦ (H · Top)
step₆ = E-App (lc-fun wf-t₆) (wf⇒lc wf-L₀)
```

## The reduct is not well-formed

```agda
H-NoAbs : NoAbs H
H-NoAbs = NR⇒NoAbs (wf⇒lc wf-H) (wf-fv wf-H) (H-NR (wf⇒lc wf-H))

¬wf-H⊤ : ¬ ([] ⊢ H · Top wf)
¬wf-H⊤ (Wf-App d₁ _) =
  no-chain H-NoAbs (wf⇒lc (⊑*wf⇒wfʳ d₁)) (_ , _ , ε (Pv-Nil Pv-Emp)) (Thm-3wf d₁)
```

## Lemma 6 and Theorem 5 are false over well-formed contexts

```agda
¬Lem-6ʷᶜ : ¬ Lem-6ʷᶜ
¬Lem-6ʷᶜ l6 = ¬wf-H⊤ (l6 wc-nil wf-t₆ step₆)

¬Preservationʷᶜ : ¬ Preservationʷᶜ
¬Preservationʷᶜ p =
  ¬wf-H⊤ (⊑*wf⇒wfˡ (p wc-nil (Ws-Sub wf-t₆ (Ws-Rfl Pv-Emp) wf-t₆) step₆))
```

## What this establishes

`¬Lem-6ʷᶜ`, `¬Preservationʷᶜ`, nothing assumed: in the empty context a well-formed term takes a
β-step to a term that is not well-formed. Type safety of MPSS in the paper's form — progress and
preservation of the judgements of Figure 4 — is false. What is not excluded is safety in the
sense that a well-formed term never reduces to a stuck one; `H ⊤` is not stuck, it diverges.
