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

## The right-hand plug reduces to an abstraction

```agda
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_; strip*)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Unconditional using (Thm-3wf)
open import MPSS.Assumed using (Conj-8)
open import MPSS.Conjecture8 using (∙; co-app)

module H₀ = Hyp₂ pvΓ₀ (here refl)

lcδ : LC δ
lcδ = lc-lam [] lc-fvar (λ _ → lc-app lc-fvar lc-fvar)

lct′ : LC t′
lct′ = lc-lam [] lc-fvar (λ _ → lc-app lc-fvar lc-fvar)

fvδ : fv δ ⊑ dom Γ₀
fvδ (here refl) = here refl

pv[] : Γ₀ ∣ [] prevalid
pv[] = Pv-Nil pvΓ₀

pv[δ] : Γ₀ ∣ (δ ∷ []) prevalid
pv[δ] = Pv-Sta pv[] lcδ fvδ

reflδ : Γ₀ ∣ [] ⊢ δ ⟶ᵉ δ
reflδ = ⟶ᵉ-refl pv[] lcδ fvδ

lcWδ : LC (app W δ)
lcWδ = lc-app lcW lcδ

fvWδ : fv (app W δ) ⊑ dom Γ₀
fvWδ (here refl) = here refl

r₁ : Γ₀ ∣ [] ⊢ app t′ δ ⟶ᵉ app (lam Rv (app W δ)) δ
r₁ = Me-App (Me-FOp {u' = app W δ} (dom Γ₀) (⟶ᵉ-refl pv[] lc-fvar (λ { (here refl) → here refl })) body) reflδ
  where
    body : ∀ {x} → x ∉ dom Γ₀ → ((x , eqv , δ) ∷ Γ₀) ∣ [] ⊢ app Rv (fvar x) ⟶ᵉ app W δ
    body {x} x∉ =
      Me-App (Unfold.stepR (there (here refl)) (Pv-Sta (Pv-Nil pvx′) lc-fvar (λ { (here refl) → here refl })))
             (Me-Pro (Pv-Nil pvx′) (here refl) (⟶ᵉ-refl (Pv-Nil pvx′) lcδ (λ h → there (fvδ h))))
      where
        pvx′ : ((x , eqv , δ) ∷ Γ₀) prevalid
        pvx′ = Pv-EqA pvΓ₀ x∉ lcδ fvδ

r₂ : Γ₀ ∣ [] ⊢ app (lam Rv (app W δ)) δ ⟶ᵉ app W δ
r₂ = Me-Bet {u = app W δ} {u' = app W δ} [] (λ _ → ⟶ᵉ-refl pv[] lcWδ fvWδ) reflδ

r₃ : Γ₀ ∣ [] ⊢ app W δ ⟶ᵉ app mid δ
r₃ = Me-App (stepWᵃ pv[δ]) reflδ

r₄ : Γ₀ ∣ [] ⊢ app mid δ ⟶ᵉ app LOO δ
r₄ = Me-App (stepMid pv[δ]) reflδ

r₅ : Γ₀ ∣ [] ⊢ app LOO δ ⟶ᵉ W
r₅ = Me-Bet {u = W} {u' = W} [] (λ _ → ⟶ᵉ-refl pv[] lcW closedW) reflδ

right : Γ₀ ∣ [] ⊢ app t′ δ ⟶ᵉ* LOO
right = r₁ ◅ r₂ ◅ r₃ ◅ r₄ ◅ r₅ ◅ stepW pvΓ₀ ◅ stepMid pv[] ◅ ε pv[]
```

## The left-hand plug never reaches one

```agda
okΓ₀ : CtxOK Γ₀
okΓ₀ (here refl) p = ⊥-elim (p refl)

nsΓ₀ : NoSub Γ₀
nsΓ₀ (there ())

Bd-δδ : Bd (app δ δ)
Bd-δδ = b-app cδ cδ
  where
    cδ : Cl δ
    cδ = c-lam (b-app c-bvar c-bvar)

presᵉ* : ∀ {t t″} → Bd t → Γ₀ ∣ [] ⊢ t ⟶ᵉ* t″ → Bd t″
presᵉ* bd (ε _)   = bd
presᵉ* bd (e ◅ p) = presᵉ* (presᵉ-Bd okΓ₀ [] bd e) p

Reaches : Tm → Set
Reaches t = ∃[ w ] ∃[ b ] (Γ₀ ∣ [] ⊢ t ⟶ᵉ* lam w b)

no-chain : ∀ {v t} → Bd v → LC t → Reaches t → ¬ (Γ₀ ∣ [] ⊢ v ≤ t)
no-chain bd lt (w , b , p) (As-Refl _)       = Bd-lam (presᵉ* bd p)
no-chain bd lt rt          (As-Left-1 st d)  = no-chain (presˢ-Bd okΓ₀ nsΓ₀ [] bd st) lt rt d
no-chain bd lt (w , b , p) (As-Right d e) with strip* lt p e
... | _ , Me-Fun _ _ _ , q = no-chain bd (⟶ᵉ-lc lt e) (_ , _ , q) d
```

## Conjecture 8 is false

```agda
¬Conj-8 : ¬ Conj-8
¬Conj-8 c8 =
  no-chain Bd-δδ (lc-app lct′ lcδ) (_ , _ , right)
           (Thm-3wf (c8 (co-app ∙ δ) lcδ lct′ H₀.δ≤t′ H₀.wf-δδ H₀.wf-t′δ))
```


## Evaluation does not preserve well-formedness either

Lemma 6 of the paper, `Lem-6` of `MPSS/Preservation`, is what preservation rests on, and the
development proves it from Conjecture 8. In the same context it is false outright:

    g = λx≤R. (x δ) δ        g δ  ↦  (δ δ) δ

`g δ` is well-formed — under `x ≤ R` the application `x δ` promotes to `R δ`, which reduces to `W`,
as `R` does — and `(δ δ) δ` is not: its well-formedness would put `δ δ` below an abstraction.

```agda
open import MPSS.Preservation using (Lem-6)
open import MPSS.Static using (⊑*wf⇒wfʳ)

module Hyp₃ {Γ : Ctx} (pv : Γ prevalid) (mR : R ≐ W ∈ Γ) where

  open Hyp₂ pv mR public

  fvδ′ : fv δ ⊑ dom Γ
  fvδ′ (here refl) = ∈-dom mR

  pvs : Γ ∣ (δ ∷ []) prevalid
  pvs = Pv-Sta (Pv-Nil pv) lcδ fvδ′

  rδ : Γ ∣ [] ⊢ δ ⟶ᵉ δ
  rδ = ⟶ᵉ-refl (Pv-Nil pv) lcδ fvδ′

  wf-Rδ : Γ ⊢ app Rv δ wf
  wf-Rδ = Wf-App R≤LRT δ≤R

  -- R δ reduces to W, and so does R
  Rδ≤R : Γ ⊢ app Rv δ ≤*wf Rv
  Rδ≤R = Ws-Sub wf-Rδ
           (Ws-Lf1 (Me-App (Unfold.stepR mR pvs) rδ)
           (Ws-Lf1 (Me-App (stepWᵃ pvs) rδ)
           (Ws-Lf1 (Me-App (stepMid pvs) rδ)
           (Ws-Lf1 (Me-Bet {u = W} {u' = W} [] (λ _ → ⟶ᵉ-refl (Pv-Nil pv) lcW closedW) rδ)
           (Ws-Rgh (Ws-Rfl pv) (Unfold.stepR mR (Pv-Nil pv)))))))
           wfR

g : Tm
g = lam Rv (app (app (bvar 0) δ) δ)

lcg : LC g
lcg = lc-lam [] lc-fvar (λ _ → lc-app (lc-app lc-fvar lcδ) lcδ)

module G {Γ : Ctx} (pv : Γ prevalid) (mR : R ≐ W ∈ Γ) where

  open Hyp₃ pv mR

  module _ {x : Name} (x∉ : x ∉ dom Γ) where

    open Hyp₃ (pv′ x∉) (there mR) using ()
      renaming (δ≤R to δ≤R′; wf-Rδ to wf-Rδ′; Rδ≤R to Rδ≤R′; R≤LRT to R≤LRT′; wfR to wfR′)

    wf-xδ : Γx x∉ ⊢ app (fvar x) δ wf
    wf-xδ = Wf-App (Ws-Trs (x≤R x∉) wfR′ R≤LRT′) δ≤R′

    xδ≤LRT : Γx x∉ ⊢ app (fvar x) δ ≤*wf LRT
    xδ≤LRT =
      Ws-Trs (Ws-Sub wf-xδ
                (Ws-Lf2 wf-xδ
                   (Ms-App (Ms-Pro (Pv-Sta (Pv-Nil (pv′ x∉)) lcδ (λ h → there (fvδ′ h))) (here refl)))
                   wf-Rδ′ (Ws-Rfl (pv′ x∉)))
                wf-Rδ′)
             wf-Rδ′
             (Ws-Trs Rδ≤R′ wfR′ R≤LRT′)

    wf-body : Γx x∉ ⊢ app (app (fvar x) δ) δ wf
    wf-body = Wf-App xδ≤LRT δ≤R′

  wfg : Γ ⊢ g wf
  wfg = Wf-Fun (dom Γ) (λ x∉ → wf-body x∉) wfR

  wf-gδ : Γ ⊢ app g δ wf
  wf-gδ = Wf-App
            (Ws-Sub wfg
               (Ws-Lf2 wfg (Ms-Fun {u' = Top} (dom Γ) (λ x∉ → Ms-Top (Pv-Nil (pv′ x∉)))) wfLRT (Ws-Rfl pv))
               wfLRT)
            δ≤R

¬wf-δδδ : ¬ (Γ₀ ⊢ app (app δ δ) δ wf)
¬wf-δδδ (Wf-App d₁ _) =
  no-chain Bd-δδ (wf⇒lc (⊑*wf⇒wfʳ d₁)) (_ , _ , ε pv[]) (Thm-3wf d₁)

¬Lem-6 : ¬ Lem-6
¬Lem-6 lem-6 = ¬wf-δδδ (lem-6 (G.wf-gδ pvΓ₀ (here refl)) (E-App lcg lcδ))
```

Lemma 7 goes with it, since `MPSS/Preservation17` proves Lemma 6 from it and from nothing else
that is assumed.

```agda
open import MPSS.Evaluation using (Lem-7₀)
open import MPSS.Preservation17 using (Lem-6ʷ)

¬Lem-7 : ¬ Lem-7₀
¬Lem-7 lem-7 = ¬Lem-6 (Lem-6ʷ lem-7)
```

## Nor is subtyping preserved: Theorem 5, as stated, is false

Preservation is stated for an arbitrary logical context too. With `g δ ≤*wf g δ` by reflexivity
and `g δ ↦ (δ δ) δ`, its conclusion would make `(δ δ) δ` well-formed.

```agda
Preservation : Set
Preservation = ∀ {Γ t t' u} → Γ ⊢ t ⊑*wf[ sub-m ] u → t ↦ t' → Γ ⊢ t' ⊑*wf[ sub-m ] u

¬Thm-5 : ¬ Preservation
¬Thm-5 thm-5 = ¬wf-δδδ (⊑*wf⇒wfˡ (thm-5 (Ws-Sub w (Ws-Rfl pvΓ₀) w) (E-App lcg lcδ)))
  where w = G.wf-gδ pvΓ₀ (here refl)
```

## What this establishes

`¬Conj-8`, `¬Lem-6`, `¬Lem-7` and `¬Thm-5`: Conjecture 8, Lemmas 6 and 7 and Theorem 5 (preservation), as the paper
states them — for an arbitrary logical context — are false. The counterexamples live in the one
prevalid context `R ≡ ω ω`, whose annotation is not well-formed. `Preservation` is the second
component of `type-safety` in `MPSS/Preservation17`, which is proved there from `Conj-8`: from a
false hypothesis. They say nothing yet about contexts with well-formed annotations,
or about closed programs; there `MPSS/CONJ8.md` §11 applies — the same instances fail as soon as
any well-formed term behaves as `R` does here.
