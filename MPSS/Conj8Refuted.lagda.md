# MPSS: Conjecture 8 is false as stated

Contexts are only required to be **prevalid**: an annotation has to be locally closed and scoped
in the entries before it, not well-formed (`MPSS/EqvWf` already uses this). So a context may
define a name by a term with no normal form, and the name is well-formed by `Wf-PrE`:

    ω = λs≤⊤. λx≤(s s). (s s)        W = ω ω        Γ₀ = R ≡ W

`W` reduces to `λx≤W.W`, and so does the well-formed `λx≤R.R`. So in `Γ₀` the name `R` is a
recursive function type, `R ≡ λx≤R.R`, and the instance of `MPSS/CONJ8.md` §11 can be stated in
MPSS itself:

    δ = λx≤R. x x        δ ⟶ˢ t′ = λx≤R. R x        context □ δ

Every hypothesis of Conjecture 8 holds — `δ ≤*wf t′`, and `δ δ` and `t′ δ` are well-formed — and
`δ δ ≤*wf t′ δ` does not: by Theorem 3 it would be a machine chain `δ δ ⟶ˢ* c ⟵ᵉ* t′ δ`; `t′ δ`
reduces to the abstraction `λx≤W.W`, so by confluence `c` reduces to an abstraction, and `δ δ`
would reach one by promotions and equivalence steps; but `δ δ` is in the class `Bd` of
`MPSS/AppClass`, which both reductions preserve and which contains no abstraction.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conj8Refuted where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import MPSS.WellFormed
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.AppClass
```

## The terms

```agda
ω W LOO mid Rv δ t′ LRR LRT : Tm
ω   = lam Top (lam (app (bvar 0) (bvar 0)) (app (bvar 1) (bvar 1)))
W   = app ω ω
LOO = lam W W
mid = app (lam Top LOO) ω
Rv  = fvar R
δ   = lam Rv (app (bvar 0) (bvar 0))
t′  = lam Rv (app Rv (bvar 0))
LRR = lam Rv Rv
LRT = lam Rv Top

Γ₀ : Ctx
Γ₀ = (R , eqv , W) ∷ []
```

## Local closure, scoping, prevalidity

```agda
lcω : LC ω
lcω = lc-lam [] lc-Top
        (λ _ → lc-lam [] (lc-app lc-fvar lc-fvar) (λ _ → lc-app lc-fvar lc-fvar))

lcW : LC W
lcW = lc-app lcω lcω

lcLOO : LC LOO
lcLOO = lc-lam [] lcW (λ _ → lcW)

closedW : ∀ {N : List Name} → fv W ⊑ N
closedW ()

closedω : ∀ {N : List Name} → fv ω ⊑ N
closedω ()

closedLOO : ∀ {N : List Name} → fv LOO ⊑ N
closedLOO ()

pvΓ₀ : Γ₀ prevalid
pvΓ₀ = Pv-EqA Pv-Emp (λ ()) lcW closedW
```

## The unfolding of `R`, at any context that defines it

```agda
module Unfold {Γ : Ctx} (mR : R ≐ W ∈ Γ) where

  stepR : ∀ {s} → Γ ∣ s prevalid → Γ ∣ s ⊢ Rv ⟶ᵉ W
  stepR pv = Me-Pro pv mR (⟶ᵉ-refl pv lcW closedW)

-- x x reduces to W where x ≡ ω
selfapp : ∀ {Γ x} → Γ prevalid → x ≐ ω ∈ Γ → Γ ∣ [] ⊢ app (fvar x) (fvar x) ⟶ᵉ W
selfapp {Γ} {x} pv mx =
  Me-App (Me-Pro pv₁ mx (⟶ᵉ-refl pv₁ lcω closedω))
         (Me-Pro (Pv-Nil pv) mx (⟶ᵉ-refl (Pv-Nil pv) lcω closedω))
  where
    pv₁ : Γ ∣ (fvar x ∷ []) prevalid
    pv₁ = Pv-Sta (Pv-Nil pv) lc-fvar (λ { (here refl) → ∈-dom mx })
```

`W` takes one step to `(λs≤⊤. λx≤W.W) ω` — the parameter bound and unfolded under the operand —
at the empty stack and under one more operand, and that takes one step to `λx≤W.W`.

```agda
xx⊑ : ∀ {x} {N : List Name} → x ∈ N → fv (app (fvar x) (fvar x)) ⊑ N
xx⊑ p (here refl)         = p
xx⊑ p (there (here refl)) = p

stepW : ∀ {Γ} → Γ prevalid → Γ ∣ [] ⊢ W ⟶ᵉ mid
stepW {Γ} pv =
  Me-App (Me-FOp (dom Γ) (Me-Top (Pv-Nil pv)) inner) (⟶ᵉ-refl (Pv-Nil pv) lcω closedω)
  where
    inner : ∀ {x} → x ∉ dom Γ
          → ((x , eqv , ω) ∷ Γ) ∣ [] ⊢ lam (app (fvar x) (fvar x)) (app (fvar x) (fvar x)) ⟶ᵉ LOO
    inner {x} x∉ = Me-Fun (x ∷ dom Γ) (selfapp pv′ (here refl)) body
      where
        pv′ : ((x , eqv , ω) ∷ Γ) prevalid
        pv′ = Pv-EqA pv x∉ lcω closedω
        body : ∀ {y} → y ∉ (x ∷ dom Γ)
             → ((y , sub , app (fvar x) (fvar x)) ∷ (x , eqv , ω) ∷ Γ) ∣ [] ⊢ app (fvar x) (fvar x) ⟶ᵉ W
        body {y} y∉ =
          selfapp (Pv-Ctx pv′ y∉ (lc-app lc-fvar lc-fvar) (xx⊑ (here refl))) (there (here refl))

stepWᵃ : ∀ {Γ a} → Γ ∣ (a ∷ []) prevalid → Γ ∣ (a ∷ []) ⊢ W ⟶ᵉ mid
stepWᵃ {Γ} {a} pvs =
  Me-App (Me-FOp (dom Γ) (Me-Top (Pv-Nil pv)) inner) (⟶ᵉ-refl (Pv-Nil pv) lcω closedω)
  where
    pv = prevalid-ctx pvs
    la = prevalid-head-lc pvs
    fa = prevalid-head-fv pvs
    inner : ∀ {x} → x ∉ dom Γ
          → ((x , eqv , ω) ∷ Γ) ∣ (a ∷ []) ⊢ lam (app (fvar x) (fvar x)) (app (fvar x) (fvar x)) ⟶ᵉ LOO
    inner {x} x∉ = Me-FOp (x ∷ dom Γ) (selfapp pv′ (here refl)) body
      where
        pv′ : ((x , eqv , ω) ∷ Γ) prevalid
        pv′ = Pv-EqA pv x∉ lcω closedω
        body : ∀ {y} → y ∉ (x ∷ dom Γ)
             → ((y , eqv , a) ∷ (x , eqv , ω) ∷ Γ) ∣ [] ⊢ app (fvar x) (fvar x) ⟶ᵉ W
        body {y} y∉ = selfapp (Pv-EqA pv′ y∉ la (λ h → there (fa h))) (there (here refl))

stepMid : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ s ⊢ mid ⟶ᵉ LOO
stepMid {Γ} pv =
  Me-Bet {u = LOO} {u' = LOO} [] (λ _ → ⟶ᵉ-refl pv lcLOO closedLOO) (⟶ᵉ-refl (prevalid-nil pv) lcω closedω)
```
