# MPSS: Conjecture 8 over well-formed contexts fails at a well-formed application that no machine chain takes to an abstraction

`MPSS/Conj8Refuted` refutes Conjecture 8 in a context whose annotation is not well-formed.
`MPSS/WfCtx` restates it over contexts with well-formed annotations (`Conj-8ʷᶜ`). This module
isolates, with no particular term in it, what a refutation of
`Conj-8ʷᶜ` in the **empty context** needs:

    f ≤*wf λx≤A.B,   f q wf,   (λx≤A.B) q wf,   (λx≤A.B) q ⟶ᵉ* an abstraction,
    and no chain of promotions from f q ends in an abstraction.

The instance is `u = f`, `t = λx≤A.B`, covariant context `□ q`. The conjecture would give
`f q ≤*wf (λx≤A.B) q`; by Theorem 3 that is a machine chain `f q ⟶ˢ* c ⟵ᵉ* (λx≤A.B) q`; the right
side reduces to an abstraction, so by confluence (`MPSS/Strip`) `c` does, and `f q` reaches an
abstraction by promotions (an equivalence step is a promotion, `Ms-Equ`).

The terms are those of `MPSS/CONJ8.md` §21: `f q` is Hurkens' paradox `[L₀ R₀]`. The hypotheses
are arguments here; they are discharged in `MPSS/Conj8WfCtxRefuted`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conj8NoAbstraction where

open import Data.List.Base using ([])
open import Data.Product.Base using (_,_; ∃-syntax)
open import Relation.Nullary using (¬_)

open import MPSS.WellFormed
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_; strip*)
open import MPSS.Unconditional using (Thm-3wf)
open import MPSS.Conjecture8 using (∙; co-app)
open import MPSS.WfCtx using (Conj-8ʷᶜ; wc-nil)
```

## Chains of promotions at the empty configuration

```agda
infix 3 _⟶ˢ*_
data _⟶ˢ*_ : Tm → Tm → Set where
  εˢ   : ∀ {a} → a ⟶ˢ* a
  _◅ˢ_ : ∀ {a b c} → [] ∣ [] ⊢ a ⟶ˢ b → b ⟶ˢ* c → a ⟶ˢ* c

-- no chain of promotions from v ends in an abstraction
NoAbs : Tm → Set
NoAbs v = ∀ {w b} → ¬ (v ⟶ˢ* lam w b)

NoAbs-step : ∀ {v v′} → NoAbs v → [] ∣ [] ⊢ v ⟶ˢ v′ → NoAbs v′
NoAbs-step na st p = na (st ◅ˢ p)

-- an equivalence chain is a chain of promotions
ᵉ*⇒ˢ* : ∀ {a b} → [] ∣ [] ⊢ a ⟶ᵉ* b → a ⟶ˢ* b
ᵉ*⇒ˢ* (ε _)   = εˢ
ᵉ*⇒ˢ* (d ◅ p) = Ms-Equ (⟶ᵉ-prevalid d) d ◅ˢ ᵉ*⇒ˢ* p
```

## No machine chain to a term that reduces to an abstraction

```agda
Reaches : Tm → Set
Reaches t = ∃[ w ] ∃[ b ] ([] ∣ [] ⊢ t ⟶ᵉ* lam w b)

no-chain : ∀ {v t} → NoAbs v → LC t → Reaches t → ¬ ([] ∣ [] ⊢ v ≤ t)
no-chain na lt (w , b , p) (As-Refl _)      = na (ᵉ*⇒ˢ* p)
no-chain na lt rt          (As-Left-1 st d) = no-chain (NoAbs-step na st) lt rt d
no-chain na lt (w , b , p) (As-Right d e) with strip* lt p e
... | _ , Me-Fun _ _ _ , q = no-chain na (⟶ᵉ-lc lt e) (_ , _ , q) d
```

## The refutation, from its five hypotheses

```agda
refutes : ∀ {f q A B}
        → LC f → LC (lam A B) → LC q
        → [] ⊢ f ≤*wf lam A B
        → [] ⊢ app f q wf
        → [] ⊢ app (lam A B) q wf
        → Reaches (app (lam A B) q)
        → NoAbs (app f q)
        → ¬ Conj-8ʷᶜ
refutes lf lt lq f≤t wf-fq wf-tq rt na c8 =
  no-chain na (lc-app lt lq) rt
           (Thm-3wf (c8 (co-app ∙ _) wc-nil lf lt f≤t wf-fq wf-tq))
```

## What this establishes

`refutes`: in the empty context, `Conj-8ʷᶜ` is false as soon as there are `f`, `q`, `A`, `B`
with `f ≤*wf λx≤A.B`, both applications to `q` well-formed, `(λx≤A.B) q` reducing to an
abstraction, and no chain of promotions from `f q` ending in an abstraction. No such terms are
constructed here; `MPSS/Conj8WfCtxRefuted` supplies them, for Hurkens' paradox.
