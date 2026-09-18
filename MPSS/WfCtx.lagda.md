# MPSS: contexts with well-formed annotations, and the statements restated over them

`MPSS/Conj8Refuted` refutes Conjecture 8, Lemmas 6 and 7 and Theorem 5 in a context that is
prevalid and whose annotation is ill-formed. The repair that suggests itself is to ask, of the
logical context a statement is about, that every annotation be well-formed in the entries before
it. This module defines that, `WfCtx`, restates the four statements with it as a hypothesis, and
shows the counterexample's context is excluded.

One choice is made here and should be read as a choice. The premise is put on the **logical
context of the statement**, not inside the reductions: `⟶ᵉ` and `⟶ˢ` keep asking only
prevalidity of the configurations they pass through. They have to — a well-subtyping chain takes
equivalence steps through ill-formed terms, and `Me-App`/`Me-FOp` bind a parameter to whatever
operand is there — so a well-formedness premise in `Pv-EqA` itself would change the reduction
relation, not just the statements. With the premise on the statement's context, every result
the development proves holds as it is, and nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.WfCtx where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.TopLemma using (Top≰lam)
open import MPSS.Unconditional using (Thm-3wf)
open import MPSS.Conjecture8 using (CoCtx; plug)
open import MPSS.Static using (⊑*wf⇒wfʳ)
```

## The condition

```agda
data WfCtx : Ctx → Set where
  wc-nil : WfCtx []
  wc-sub : ∀ {Γ x t} → WfCtx Γ → x ∉ dom Γ → Γ ⊢ t wf → WfCtx ((x , sub , t) ∷ Γ)
  wc-eqv : ∀ {Γ x α} → WfCtx Γ → x ∉ dom Γ → Γ ⊢ α wf → WfCtx ((x , eqv , α) ∷ Γ)

WfCtx⇒prevalid : ∀ {Γ} → WfCtx Γ → Γ prevalid
WfCtx⇒prevalid wc-nil           = Pv-Emp
WfCtx⇒prevalid (wc-sub c x∉ w)  = Pv-Ctx (WfCtx⇒prevalid c) x∉ (wf⇒lc w) (wf-fv w)
WfCtx⇒prevalid (wc-eqv c x∉ w)  = Pv-EqA (WfCtx⇒prevalid c) x∉ (wf⇒lc w) (wf-fv w)
```

## The statements, over such contexts

```agda
Conj-8ʷᶜ : Set
Conj-8ʷᶜ = ∀ {Γ u t} (C : CoCtx) → WfCtx Γ
         → LC u → LC t
         → Γ ⊢ u ≤*wf t → Γ ⊢ plug C u wf → Γ ⊢ plug C t wf
         → Γ ⊢ plug C u ≤*wf plug C t

Lem-6ʷᶜ : Set
Lem-6ʷᶜ = ∀ {Γ t t'} → WfCtx Γ → Γ ⊢ t wf → t ↦ t' → Γ ⊢ t' wf

Preservationʷᶜ : Set
Preservationʷᶜ = ∀ {Γ t t' u} → WfCtx Γ → Γ ⊢ t ⊑*wf[ sub-m ] u → t ↦ t' → Γ ⊢ t' ⊑*wf[ sub-m ] u
```

## The counterexample's context is excluded

`W = ω ω` is not well-formed: the annotation `s s` of `ω`'s inner abstraction would need `s`, which
is bounded by `⊤`, below an abstraction.

```agda
open import MPSS.Conj8Refuted using (W; Γ₀)
open import PSS.Syntax using (fresh; fresh-∉)

var≰lam : ∀ {x s a b} → ¬ (((x , sub , Top) ∷ []) ∣ s ⊢ fvar x ≤ lam a b)
var≰lam (As-Left-1 (Ms-Pro _ (here refl)) d)          = Top≰lam d
var≰lam (As-Left-1 (Ms-Pro _ (there ())) d)
var≰lam (As-Left-1 (Ms-Top _) d)                      = Top≰lam d
var≰lam (As-Left-1 (Ms-Equ _ (Me-Var _)) d)           = var≰lam d
var≰lam (As-Left-1 (Ms-Equ _ (Me-Pro _ (there ()) _)) d)
var≰lam (As-Right d (Me-Fun _ _ _))                   = var≰lam d
var≰lam (As-Right d (Me-FOp _ _ _))                   = var≰lam d

¬wf-W : ¬ ([] ⊢ W wf)
¬wf-W (Wf-App d₁ _) with ⊑*wf⇒wfˡ d₁
... | Wf-Fun L F _ with F (fresh-∉ L)
...   | Wf-Fun _ _ (Wf-App e₁ _) = var≰lam (Thm-3wf e₁)

¬WfCtx-Γ₀ : ¬ WfCtx Γ₀
¬WfCtx-Γ₀ (wc-eqv _ _ w) = ¬wf-W w
```

## What this establishes

`WfCtx`, the four statements over it, and `¬WfCtx-Γ₀`: the context of `MPSS/Conj8Refuted` is not
one of these, so `Conj-8ʷᶜ`, `Lem-6ʷᶜ` and `Preservationʷᶜ` are open. Every theorem of the
development holds over `WfCtx` contexts a fortiori.
