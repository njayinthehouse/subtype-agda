# MPSS: Lemma 2's case analysis, and what each case actually needs

Every attempt to prove Lemma 2 has failed on the *induction*, never on the statement: no
counterexample has turned up in billions of checked joins, and none turns up at `Ω`, the term
`MPSS/InfiniteBranching` shows is pathological. So the useful thing to pin down is not whether the
cases close — it is **which sub-instance each case closes against**, because that is what a
well-founded ordering would have to justify.

This module takes the diamond as a hypothesis `ih` and discharges the cases from it. That is
circular as a proof and is not offered as one. What it establishes is the *shape*: the case
analysis is complete, and every case is reduced to explicitly named sub-instances, so the residual
question is exactly whether those instances can be well-ordered.

```agda
{-# OPTIONS --safe #-}

module MPSS.DiamondCases where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Assumed using (Lem-2)
open import MPSS.CtxReduce using (↣-eqv; ↣-empty)
open import MPSS.StackPush using (pushᵉ)
```

## The two cases that need nothing at all

`Me-Top` forces both sides to `⊤`, and `Me-Var` forces both to the variable.

```agda
module _ (ih : Lem-2) where

  case-top : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂} → Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
           → Γ₁ ∣ s₁ prevalid → Γ₂ ∣ s₂ prevalid
           → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ Top ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ Top ⟶ᵉ t₃))
  case-top _ _ pv₁ pv₂ = Top , Me-Top pv₁ , Me-Top pv₂

  case-var-var : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x} → Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
               → Γ₁ ∣ s₁ prevalid → Γ₂ ∣ s₂ prevalid
               → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ fvar x ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ fvar x ⟶ᵉ t₃))
  case-var-var _ _ pv₁ pv₂ = _ , Me-Var pv₁ , Me-Var pv₂
```

## The variable cases

Both reduce to the diamond **at the annotation, at the same configuration**. That is the instance
`ht-unfold` orders: `htm Γ α < hvar Γ x`, so the subject strictly shrinks in the one measure that
survives `Me-Pro`.

`Me-Var` against `Me-Pro` is the case with no counterpart in v1, and the one the printed proof has
no induction principle for: the joining derivation is read off the *context reduction* by `↣-eqv`,
so it is a subderivation of neither input.

```agda
  case-pro-pro : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ α α₁ α₂}
               → Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₁ → Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₂
               → Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
               → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ α₁ ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ α₂ ⟶ᵉ t₃))
  case-pro-pro e₁ e₂ c₁ c₂ = ih e₁ e₂ c₁ c₂

  case-var-pro : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x α α₁}
               → Γ₀ prevalid → Γ₀ ∣ s₀ prevalid → Γ₁ ∣ s₁ prevalid
               → x ≐ α ∈ Γ₀
               → Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₁
               → Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
               → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ fvar x ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ α₁ ⟶ᵉ t₃))
  case-var-pro pvc pv₀ pv₁ m e₁ c₁ c₂ with ↣-eqv pvc c₁ m
  ... | α' , m' , e'  with ih (pushᵉ {s = []} e' pv₀) e₁ c₁ c₂
  ...   | t₃ , f₁ , f₂ = t₃ , Me-Pro pv₁ m' f₁ , f₂
```

## The application case, and why the paper's general form is the right one

`Me-App` against `Me-App` needs the operator's join at the stack carrying the *reduced* operand.
That is exactly `Ct-Stk`: the operand's own step is what turns the original configuration into the
one the join has to live at. The two context reductions in Lemma 2's statement are not generality
for its own sake — this case manufactures them.

```agda
  case-app-app : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u v u₁ v₁ u₂ v₂}
               → Γ₀ ∣ (v ∷ s₀) ⊢ u ⟶ᵉ u₁ → Γ₀ ∣ [] ⊢ v ⟶ᵉ v₁
               → Γ₀ ∣ (v ∷ s₀) ⊢ u ⟶ᵉ u₂ → Γ₀ ∣ [] ⊢ v ⟶ᵉ v₂
               → Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
               → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ app u₁ v₁ ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ app u₂ v₂ ⟶ᵉ t₃))
  case-app-app o₁ p₁ o₂ p₂ c₁ c₂
    with ih o₁ o₂ (Ct-Stk c₁ p₁) (Ct-Stk c₂ p₂)
       | ih p₁ p₂ (↣-empty c₁) (↣-empty c₂)
  ... | u₃ , g₁ , g₂ | v₃ , h₁ , h₂ = app u₃ v₃ , Me-App g₁ h₁ , Me-App g₂ h₂
```

## What this establishes

The case analysis, with each case reduced to named sub-instances of the diamond. Taking `ih` as a
hypothesis makes this circular as a proof and it is not offered as one; what it fixes is the
**shape** of the recursion, which is what a well-founded ordering would have to justify.

| case | sub-instance it closes against |
| --- | --- |
| `case-top`, `case-var-var` | none |
| `case-pro-pro` | the annotation, at the same configuration |
| `case-var-pro` | the annotation, at the same configuration |
| `case-app-app` | the operator at the pushed stack, and the operand at the empty stack |

Two things fall out that were not obvious before.

**The context reductions are not free inputs — the induction manufactures them.** In
`case-app-app` the operator's join has to live at the stack carrying the *reduced* operand, and the
reduction that gets it there is `Ct-Stk c p` — built from the rule's own operand premise. The
abstraction cases do the same with `Ct-Ann` and the annotation premise. So the two context
reductions in Lemma 2's statement are not generality for its own sake; drop them and the
application case cannot state its own induction hypothesis. That is a point in the paper's favour:
the general form is forced.

**`Me-Var` against `Me-Pro` is the case with no induction principle, and now it is explicit.** The
joining derivation is read off the context reduction by `↣-eqv`, so it is a subderivation of
neither input, and nothing in the case bounds it. Every other case recurses on premises of the
rules being analysed. This one does not — which is exactly why a measure is needed, and why it has
to be one that `Me-Pro` strictly decreases. `ht-unfold` is that measure on the subject, and
`MPSS/Height` shows what stops it from being one on the whole configuration.
