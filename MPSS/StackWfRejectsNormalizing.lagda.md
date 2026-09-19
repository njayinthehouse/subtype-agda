# MPSS, candidate C: a term with a normal form that Figure 4 accepts and the stack-reading judgement rejects

`MPSS/StackWfRejects` shows that the judgement of `MPSS/StackWf` rejects `t₆`, which has no normal
form. One might hope the two judgements agree on terms that have one. They do not:

    (λz≤⊤. ⊤) t₆   ↦   ⊤

is well-formed by Figure 4 (`t₆` is, and `t₆ ≤ ⊤`), reduces to the normal form `⊤` in one step,
and is not `wfˢ`: `Wc-App` asks the operand to be well-formed. The term is not strongly
normalizing — its operand `t₆` diverges — so what is left open is agreement on strongly
normalizing terms. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfRejectsNormalizing where

open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (proj₁)
open import Relation.Nullary using (¬_)

open import MPSS.WellFormed
open import MPSS.StackWf
open import MPSS.StackWfRejects using (¬wfˢ-t₆)
open import MPSS.Lem6WfCtxRefuted using (t₆; wf-t₆)
open import PSS.Reduction using (nf-Top)

K⊤ e : Tm
K⊤ = lam Top Top          -- λz≤⊤. ⊤
e  = app K⊤ t₆

pv : [] prevalid
pv = Pv-Emp

wf-K⊤ : [] ⊢ K⊤ wf
wf-K⊤ = Wf-Fun [] (λ _ → Wf-Top (Pv-Ctx pv (λ ()) lc-Top (λ ()))) (Wf-Top pv)

wf-e : [] ⊢ e wf
wf-e = Wf-App (Ws-Sub wf-K⊤ (Ws-Rfl pv) wf-K⊤)
              (Ws-Sub wf-t₆ (Ws-Lf2 wf-t₆ (Ms-Top (Pv-Nil pv)) (Wf-Top pv) (Ws-Rfl pv)) (Wf-Top pv))

step-e : e ↦ Top
step-e = E-App (wf⇒lc wf-K⊤) (wf⇒lc wf-t₆)

nf-e : NF Top
nf-e = nf-Top

¬wfˢ-e : ¬ ([] ∣ [] ⊢ e wfˢ)
¬wfˢ-e (Wc-App _ d₂) = ¬wfˢ-t₆ (proj₁ (≤*wfˢ⇒both d₂))
```

## What this establishes

`wf-e`, `step-e`, `¬wfˢ-e`: Figure 4 accepts a term whose evaluation can end at once in `⊤`, and
the stack-reading judgement rejects it, because it contains `t₆` as an operand. Agreement of the
two judgements can therefore only be asked of terms all of whose subterms' evaluations end.
