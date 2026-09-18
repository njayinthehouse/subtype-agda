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

## The hypotheses of the instance

In any prevalid context that defines `R`.

```agda
module Hyp {Γ : Ctx} (pv : Γ prevalid) (mR : R ≐ W ∈ Γ) where

  open Unfold

  R∈ : ∀ {N : List Name} → dom Γ ⊑ N → fv Rv ⊑ N
  R∈ f (here refl) = f (∈-dom mR)

  pvx : ∀ {x t} → x ∉ dom Γ → LC t → fv t ⊑ dom Γ → ((x , sub , t) ∷ Γ) prevalid
  pvx x∉ lt ft = Pv-Ctx pv x∉ lt ft

  wfR : Γ ⊢ Rv wf
  wfR = Wf-PrE pv mR

  wfLRR : Γ ⊢ LRR wf
  wfLRR = Wf-Fun (dom Γ) (λ x∉ → Wf-PrE (pvx x∉ lc-fvar (R∈ (λ h → h))) (there mR)) wfR

  wfLRT : Γ ⊢ LRT wf
  wfLRT = Wf-Fun (dom Γ) (λ x∉ → Wf-Top (pvx x∉ lc-fvar (R∈ (λ h → h)))) wfR

  -- λx≤R.R reduces to λx≤W.W in one step
  stepLRR : Γ ∣ [] ⊢ LRR ⟶ᵉ LOO
  stepLRR = Me-Fun (dom Γ) (stepR mR (Pv-Nil pv))
                   (λ x∉ → stepR (there mR) (Pv-Nil (pvx x∉ lc-fvar (R∈ (λ h → h)))))

  -- λx≤W.W is below R, and below λx≤R.R: the right-hand ends of the layers
  LOO⊑R : ∀ {m} → Γ ⊢ LOO ⊑wf[ m ] Rv
  LOO⊑R = Ws-Rgh (Ws-Rgh (Ws-Rgh (Ws-Rfl pv) (stepMid (Pv-Nil pv))) (stepW pv)) (stepR mR (Pv-Nil pv))

  R≤LRR : Γ ⊢ Rv ≤*wf LRR
  R≤LRR = Ws-Sub wfR
            (Ws-Lf1 (stepR mR (Pv-Nil pv)) (Ws-Lf1 (stepW pv) (Ws-Lf1 (stepMid (Pv-Nil pv))
               (Ws-Rgh (Ws-Rfl pv) stepLRR))))
            wfLRR

  LRR≤LRT : Γ ⊢ LRR ≤*wf LRT
  LRR≤LRT = Ws-Sub wfLRR
              (Ws-Lf2 wfLRR (Ms-Fun {u' = Top} (dom Γ)
                               (λ x∉ → Ms-Top (Pv-Nil (pvx x∉ lc-fvar (R∈ (λ h → h))))))
                      wfLRT (Ws-Rfl pv))
              wfLRT

  R≤LRT : Γ ⊢ Rv ≤*wf LRT
  R≤LRT = Ws-Trs R≤LRR wfLRR LRR≤LRT
```

`x x` is well-formed under `x ≤ R`, so `δ` is; `δ` promotes to `t′`; and `t′` is below `R`, because
its body `R x` reduces to `W` under the operand `x`.

```agda
module Hyp₂ {Γ : Ctx} (pv : Γ prevalid) (mR : R ≐ W ∈ Γ) where

  open Unfold
  open Hyp pv mR public

  module _ {x : Name} (x∉ : x ∉ dom Γ) where

    Γx : Ctx
    Γx = (x , sub , Rv) ∷ Γ

    pv′ : Γx prevalid
    pv′ = pvx x∉ lc-fvar (R∈ (λ h → h))

    open Hyp pv′ (there mR) using () renaming (wfR to wfR′; R≤LRT to R≤LRT′)

    wf-x : Γx ⊢ fvar x wf
    wf-x = Wf-PrS pv′ (here refl)

    x≤R : Γx ⊢ fvar x ≤*wf Rv
    x≤R = Ws-Sub wf-x (Ws-Lf2 wf-x (Ms-Pro (Pv-Nil pv′) (here refl)) wfR′ (Ws-Rfl pv′)) wfR′

    wf-xx : Γx ⊢ app (fvar x) (fvar x) wf
    wf-xx = Wf-App (Ws-Trs x≤R wfR′ R≤LRT′) x≤R

    wf-Rx : Γx ⊢ app Rv (fvar x) wf
    wf-Rx = Wf-App R≤LRT′ x≤R

    xx⟶Rx : Γx ∣ [] ⊢ app (fvar x) (fvar x) ⟶ˢ app Rv (fvar x)
    xx⟶Rx = Ms-App (Ms-Pro (Pv-Sta (Pv-Nil pv′) lc-fvar (λ { (here refl) → here refl })) (here refl))

  wfδ : Γ ⊢ δ wf
  wfδ = Wf-Fun (dom Γ) (λ x∉ → wf-xx x∉) wfR

  wft′ : Γ ⊢ t′ wf
  wft′ = Wf-Fun (dom Γ) (λ x∉ → wf-Rx x∉) wfR

  -- the hypothesis u ≤*wf t of the instance
  δ≤t′ : Γ ⊢ δ ≤*wf t′
  δ≤t′ = Ws-Sub wfδ
           (Ws-Lf2 wfδ (Ms-Fun {u' = app Rv (bvar 0)} (dom Γ) (λ x∉ → xx⟶Rx x∉)) wft′ (Ws-Rfl pv))
           wft′

  -- t′ reduces to λx≤W.W: the annotation unfolds, and the body R x unfolds R under the operand x
  -- and contracts
  e₁ : Γ ∣ [] ⊢ t′ ⟶ᵉ lam W (app W (bvar 0))
  e₁ = Me-Fun (dom Γ) (stepR mR (Pv-Nil pv))
         (λ x∉ → Me-App (stepR (there mR) (Pv-Sta (Pv-Nil (pv′ x∉)) lc-fvar (λ { (here refl) → here refl })))
                         (Me-Var (Pv-Nil (pv′ x∉))))

  pvW : ∀ {x} → x ∉ dom Γ → ((x , sub , W) ∷ Γ) prevalid
  pvW x∉ = pvx x∉ lcW closedW

  pvWx : ∀ {x} → x ∉ dom Γ → ((x , sub , W) ∷ Γ) ∣ (fvar x ∷ []) prevalid
  pvWx x∉ = Pv-Sta (Pv-Nil (pvW x∉)) lc-fvar (λ { (here refl) → here refl })

  reflW : Γ ∣ [] ⊢ W ⟶ᵉ W
  reflW = ⟶ᵉ-refl (Pv-Nil pv) lcW closedW

  e₂ : Γ ∣ [] ⊢ lam W (app W (bvar 0)) ⟶ᵉ lam W (app mid (bvar 0))
  e₂ = Me-Fun (dom Γ) reflW (λ x∉ → Me-App (stepWᵃ (pvWx x∉)) (Me-Var (Pv-Nil (pvW x∉))))

  e₃ : Γ ∣ [] ⊢ lam W (app mid (bvar 0)) ⟶ᵉ lam W (app LOO (bvar 0))
  e₃ = Me-Fun (dom Γ) reflW (λ x∉ → Me-App (stepMid (pvWx x∉)) (Me-Var (Pv-Nil (pvW x∉))))

  e₄ : Γ ∣ [] ⊢ lam W (app LOO (bvar 0)) ⟶ᵉ LOO
  e₄ = Me-Fun {u' = W} (dom Γ) reflW
         (λ x∉ → Me-Bet {u = W} {u' = W} [] (λ _ → ⟶ᵉ-refl (Pv-Nil (pvW x∉)) lcW closedW)
                        (Me-Var (Pv-Nil (pvW x∉))))

  t′≤R : Γ ⊢ t′ ≤*wf Rv
  t′≤R = Ws-Sub wft′ (Ws-Lf1 e₁ (Ws-Lf1 e₂ (Ws-Lf1 e₃ (Ws-Lf1 e₄ LOO⊑R)))) wfR

  δ≤R : Γ ⊢ δ ≤*wf Rv
  δ≤R = Ws-Trs δ≤t′ wft′ t′≤R

  δ≤LRT : Γ ⊢ δ ≤*wf LRT
  δ≤LRT = Ws-Sub wfδ
            (Ws-Lf2 wfδ (Ms-Fun {u' = Top} (dom Γ) (λ x∉ → Ms-Top (Pv-Nil (pv′ x∉)))) wfLRT (Ws-Rfl pv))
            wfLRT

  t′≤LRT : Γ ⊢ t′ ≤*wf LRT
  t′≤LRT = Ws-Sub wft′
             (Ws-Lf2 wft′ (Ms-Fun {u' = Top} (dom Γ) (λ x∉ → Ms-Top (Pv-Nil (pv′ x∉)))) wfLRT (Ws-Rfl pv))
             wfLRT

  -- the two plugs of the instance
  wf-δδ : Γ ⊢ app δ δ wf
  wf-δδ = Wf-App δ≤LRT δ≤R

  wf-t′δ : Γ ⊢ app t′ δ wf
  wf-t′δ = Wf-App t′≤LRT δ≤R
```
