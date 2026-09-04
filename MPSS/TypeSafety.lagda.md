# MPSS: type safety, and exactly what it rests on

Progress and preservation, composed, with every assumption threaded through explicitly. The point
of the module is the signature: the hypotheses of `type-safety` are the complete list of what MPSS
still owes, and nothing else is trusted anywhere beneath it.

| | assumptions |
| --- | --- |
| progress (Theorem 4) | Lemmas 1, 2 |
| preservation (Theorem 5) | Lemmas 1, 2; Proposition 17 repaired; Conjecture 8 |

Progress is the cheaper half by a wide margin. It needs only the commutation results, through
transitivity elimination, and neither Conjecture 8 nor the β-rule. Preservation needs both:
Proposition 17 to re-read an operational step as an equivalence step, and Conjecture 8, which
reaches it through Lemmas 9 and 7 in the β case.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.TypeSafety where

open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.Sum.Base using (_⊎_)

open import MPSS.WellFormed
open import MPSS.Assumed using (Lem-1; Lem-2; Prop-17ʳ; Conj-8)
open import MPSS.Progress using (Thm-4′)
open import MPSS.Preservation using (Thm-5)
open import MPSS.Evaluation using (Lem-6)
open import MPSS.Lemma7 using (Lem-7₀-holds)
open import MPSS.Lemma23 using (Lem-23-holds)

open import PSS.Reduction using (_↦_; NF)
```

## The two halves, composed

```agda
module _ (lem-1 : Lem-1) (lem-2 : Lem-2)
         (prop-17 : Prop-17ʳ) (conj-8 : Conj-8) where

  progress : ∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')
  progress = Thm-4′ lem-1 lem-2

  preservation : ∀ {Γ t t' u}
               → Γ ⊢ t ⊑*wf[ sub-m ] u
               → t ↦ t'
               → Γ ⊢ t' ⊑*wf[ sub-m ] u
  preservation = Thm-5 prop-17 (Lem-6 lem-1 lem-2 prop-17 (Lem-7₀-holds conj-8) Lem-23-holds)

  type-safety : (∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t'))
              × (∀ {Γ t t' u} → Γ ⊢ t ⊑*wf[ sub-m ] u → t ↦ t' → Γ ⊢ t' ⊑*wf[ sub-m ] u)
  type-safety = progress , preservation
```

## What this establishes

Type safety for MPSS, modulo four named statements: Lemmas 1 and 2, the commutation results;
Conjecture 8, the one obligation the paper itself flags; and Proposition 17, which the paper
claims to have proved and does not, so it appears here in the repaired form that `MPSS/Assumed`
justifies. Everything else in the paper's appendix that these two theorems depend on is proved.

The paper says type safety "holds under the assumption that Conjecture 8 holds". That is right
about the conjecture, and incomplete about the rest: on the machine-checked accounting above,
preservation additionally needs the β-rule repaired, since the printed rule makes Proposition 17
false even on well-formed subjects (`MPSS/BetaScopeWf`). Progress is unaffected.
