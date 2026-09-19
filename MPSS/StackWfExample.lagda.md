# MPSS, candidate C: the judgement is inhabited at a redex

A guard against a vacuous theorem: `(λx≤⊤. x) ⊤` is well-formed for the stack-reading judgements
of `MPSS/StackWf`, so `MPSS/StackWfPreservation` applies to a term that steps. Nothing existing is
modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfExample where

open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_,_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.Subtyping
open import MPSS.StackWf

pv₀ : [] ∣ [] prevalid
pv₀ = Pv-Nil Pv-Emp

pv₁ : [] ∣ (Top ∷ []) prevalid
pv₁ = Pv-Sta pv₀ lc-Top (λ ())

pvᵉ : ∀ {x} → ((x , eqv , Top) ∷ []) ∣ [] prevalid
pvᵉ = Pv-Nil (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ()))

id⊤ : Tm
id⊤ = lam Top (bvar 0)

wf-id : [] ∣ (Top ∷ []) ⊢ id⊤ wfˢ
wf-id = Wc-FOp [] (λ _ → Wc-PrE pvᵉ (here refl) (Wc-Top pvᵉ)) (Wc-Top pv₀)

wf-cod : [] ∣ (Top ∷ []) ⊢ lam Top Top wfˢ
wf-cod = Wc-FOp [] (λ _ → Wc-Top pvᵉ) (Wc-Top pv₀)

id≤ : [] ∣ (Top ∷ []) ⊢ id⊤ ≤ lam Top Top
id≤ = As-Left-1 (Ms-FOp {u' = Top} [] (λ _ → Ms-Top pvᵉ)) (As-Refl pv₁)

wf-redex : [] ∣ [] ⊢ app id⊤ Top wfˢ
wf-redex = Wc-App (Wc-Sub (Wc-Rule wf-id wf-cod id≤))
                  (Wc-Sub (Wc-Rule (Wc-Top pv₀) (Wc-Top pv₀) (As-Refl pv₀)))
```
