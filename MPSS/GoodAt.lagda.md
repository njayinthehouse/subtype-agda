# MPSS: goodness at a well-formed target, spines, and closure under a head reduction

`MPSS/Reducible` indexes `Good` by an accessibility proof. The fundamental lemma
(`MPSS/CONJ8.md` §17) meets targets it has no such proof for in hand — images under a
substitution, reducts, applied targets — so this module takes, as a **parameter**, that every
well-formed term is ranked, and packages goodness with the target's well-formedness.

**The parameter is false in full MPSS** (`MPSS/CONJ8.md` §14: the type of the polymorphic identity
applied to itself is well-formed and not ranked). A theorem under it says nothing until it is
relativized to a class of terms closed under what the proof uses; the calls to `rk` below and in
`MPSS/Fundamental` are the list of closure properties such a class needs. This module and the
next check that the reducibility argument closes, which is the part that was in doubt.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

open import MPSS.WellFormed
open import MPSS.DomainOrder using (Ranked)

module MPSS.GoodAt (rk : ∀ {Γ T} → Γ ⊢ T wf → Ranked Γ T) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Induction.WellFounded using (Acc; acc)

open import MPSS.DomainOrder using (_◁ᵈ_; ▷-dom; ▷-app)
open import MPSS.Reducible
open import MPSS.ReducibleMore
open import MPSS.Conjecture8 using (op-wf)
open import MPSS.Conjecture8Star using (app-wf-mid)
open import MPSS.Conj8Reduction using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; app-e*; arg-wf)
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.Weakening using (wf-weaken)
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.TopLemma using (Top≰lam)
open import MPSS.Unconditional using (Thm-3wf)
```

## Goodness at a well-formed target

```agda
G : Ctx → Tm → Tm → Set
G Γ m T = Σ (Γ ⊢ T wf) (λ w → Good (rk w) m)

G-wf : ∀ {Γ m T} → G Γ m T → Γ ⊢ m wf
G-wf (w , g) = good-wf (rk w) g

G-wfʳ : ∀ {Γ m T} → G Γ m T → Γ ⊢ T wf
G-wfʳ (w , _) = w

G-≤ : ∀ {Γ m T} → G Γ m T → Γ ⊢ m ≤*wf T
G-≤ (w , g) = good-≤ (rk w) g

G-trans : ∀ {Γ m T T′} → G Γ m T → G Γ T T′ → G Γ m T′
G-trans (w , g) (w′ , g′) = w′ , good-trans (rk w) (rk w′) g g′

G-expand* : ∀ {Γ p p′ T} → Γ ⊢ p wf → Γ ∣ [] ⊢ p ⟶ᵉ* p′ → G Γ p′ T → G Γ p T
G-expand* wp L (w , g) = w , good-expand* (rk w) wp L g

G-join : ∀ {Γ p c t} → Γ ⊢ p wf → Γ ∣ [] ⊢ p ⟶ᵉ* c → Γ ∣ [] ⊢ t ⟶ᵉ* c → Γ ⊢ t wf → G Γ p t
G-join wp L R wt = wt , good-join (rk wt) wp L R wt

G-cast : ∀ {Γ m T′ c T} → G Γ m T′ → Γ ∣ [] ⊢ T′ ⟶ᵉ* c → Γ ∣ [] ⊢ T ⟶ᵉ* c → Γ ⊢ T wf → G Γ m T
G-cast (w′ , g) L R w = w , good-cast (rk w′) (rk w) w′ L R w g

G-top : ∀ {Γ m} → Γ ⊢ m wf → G Γ m Top
G-top wm = wT , good-top (rk wT) wm
  where wT = Wf-Top (wf⇒prevalid wm)

G-weaken : ∀ (Δ : Ctx) {Γ m T} → (Δ ++ Γ) prevalid → G Γ m T → G (Δ ++ Γ) m T
G-weaken Δ pv (w , g) = w′ , good-weaken Δ (rk w) (rk w′) pv g
  where w′ = wf-weaken [] Δ pv w
```

Applying a good term to a good operand, and introducing goodness from its clause on operands.

```agda
good-app : ∀ {Γ T m v d} (a : Ranked Γ T) → Good a m
         → (w : Γ ⊢ app T v wf) → Γ ⊢ T ≤*wf lam d Top
         → (b : Ranked Γ d) → Good b v → (c : Ranked Γ (app T v))
         → Good c (app m v)
good-app (acc rs) (_ , _ , h) w e b gv c =
  good-irr (rs (▷-app [] w)) c (proj₂ (h [] w e (good-irr b (rs (▷-dom [] w e)) gv)))

G-app : ∀ {Γ m T v d} → G Γ m T → Γ ⊢ app T v wf → Γ ⊢ T ≤*wf lam d Top → G Γ v d
      → G Γ (app m v) (app T v)
G-app (wT , g) w e (wd , gv) = w , good-app (rk wT) g w e (rk wd) gv (rk w)

dom-wf : ∀ {Γ T d} → Γ ⊢ T ≤*wf lam d Top → Γ ⊢ d wf
dom-wf e with ⊑*wf⇒wfʳ e
... | Wf-Fun _ _ wd = wd

good-intro : ∀ {Γ T m} (a : Ranked Γ T) → Γ ⊢ m wf → Γ ⊢ m ≤*wf T
           → (∀ (Δ : Ctx) {v d} (w : (Δ ++ Γ) ⊢ app T v wf) → (Δ ++ Γ) ⊢ T ≤*wf lam d Top
                → (b : Ranked (Δ ++ Γ) d) → Good b v → (c : Ranked (Δ ++ Γ) (app T v))
                → ((Δ ++ Γ) ⊢ app m v ≤*wf app T v) × Good c (app m v))
           → Good a m
good-intro (acc rs) wm d h = wm , d , λ Δ w e gv → h Δ w e (rs (▷-dom Δ w e)) gv (rs (▷-app Δ w))

G-intro : ∀ {Γ T m} → Γ ⊢ m wf → Γ ⊢ T wf → Γ ⊢ m ≤*wf T
        → (∀ (Δ : Ctx) {v d} → (Δ ++ Γ) ⊢ app T v wf → (Δ ++ Γ) ⊢ T ≤*wf lam d Top
             → G (Δ ++ Γ) v d → G (Δ ++ Γ) (app m v) (app T v))
        → G Γ m T
G-intro wm wT d h = wT , good-intro (rk wT) wm d (λ Δ w e b gv c →
  let wd = dom-wf e
      r  = h Δ w e (wd , good-irr b (rk wd) gv)
  in G-≤ r , good-irr (rk (proj₁ r)) c (proj₂ r))
```

A variable is good at its bound.

```agda
G-var : ∀ {Γ x T} → Γ prevalid → x ≤ T ∈ Γ → Γ ⊢ T wf → G Γ (fvar x) T
G-var {Γ} {x} {T} pv m wT =
  wT , neutral-good Q (λ Δ q → ∈-++⁺ʳ Δ q) (rk wT) m (λ q pv′ → Ms-Pro pv′ q) (Wf-PrS pv m) wT
  where
    Q : Ctx → Set
    Q Γ′ = x ≤ T ∈ Γ′
```

## Spines

```agda
app* : Tm → Stack → Tm
app* u []      = u
app* u (v ∷ s) = app* (app u v) s

spine-head : ∀ {Γ H} s → Γ ⊢ app* H s wf → Γ ⊢ H wf
spine-head []      w = w
spine-head (v ∷ s) w = op-wf (spine-head s w)

spine-e* : ∀ {Γ H H′} s → Γ ⊢ app* H s wf → Γ ∣ [] ⊢ H ⟶ᵉ* H′ → Γ ∣ [] ⊢ app* H s ⟶ᵉ* app* H′ s
spine-e* []      w L = L
spine-e* (v ∷ s) w L = spine-e* s w (app-e* (arg-wf (spine-head s w)) L)

reduct*-≤ : ∀ {Γ H H′} → Γ ⊢ H′ wf → Γ ∣ [] ⊢ H ⟶ᵉ* H′ → Γ ⊢ H wf → Γ ⊢ H′ ≤*wf H
reduct*-≤ wH′ L wH = join-≤ wH′ εᵉ L wH

spine-reduct-wf : ∀ {Γ H H′} s → Γ ⊢ app* H s wf → Γ ∣ [] ⊢ H ⟶ᵉ* H′ → Γ ⊢ H′ wf
                → Γ ⊢ app* H′ s wf
spine-reduct-wf []      w L wH′ = wH′
spine-reduct-wf (v ∷ s) w L wH′ =
  spine-reduct-wf s w (app-e* (arg-wf wHv) L) (app-wf-mid (reduct*-≤ wH′ L (op-wf wHv)) wH′ wHv)
  where wHv = spine-head s w
```

The operands of a well-formed spine, each good at a domain of the head it is applied to.

```agda
data Ops (Γ : Ctx) : Tm → Stack → Set where
  o-nil  : ∀ {H} → Γ ⊢ H wf → Ops Γ H []
  o-cons : ∀ {H v d s} → Γ ⊢ H ≤*wf lam d Top → G Γ v d → Ops Γ (app H v) s → Ops Γ H (v ∷ s)

ops-head : ∀ {Γ H s} → Ops Γ H s → Γ ⊢ H wf
ops-head (o-nil w)      = w
ops-head (o-cons e _ _) = ⊑*wf⇒wfˡ e

ops-wf : ∀ {Γ H s} → Ops Γ H s → Γ ⊢ app* H s wf
ops-wf (o-nil w)        = w
ops-wf (o-cons _ _ ops) = ops-wf ops

spine-good : ∀ {Γ m H s} → G Γ m H → Ops Γ H s → G Γ (app* m s) (app* H s)
spine-good g (o-nil _)          = g
spine-good g (o-cons e gv ops)  = spine-good (G-app g (ops-head ops) e gv) ops

ops-reduct : ∀ {Γ H H′ s} → Γ ∣ [] ⊢ H ⟶ᵉ* H′ → Γ ⊢ H′ wf → Ops Γ H s → Ops Γ H′ s
ops-reduct L wH′ (o-nil _) = o-nil wH′
ops-reduct L wH′ (o-cons e gv ops) =
  o-cons (Ws-Trs H′≤H wH e) gv
         (ops-reduct (app-e* (arg-wf wHv) L) (app-wf-mid H′≤H wH′ wHv) ops)
  where
    wH   = ⊑*wf⇒wfˡ e
    wHv  = ops-head ops
    H′≤H = reduct*-≤ wH′ L wH

ops-top : ∀ {Γ v s} {A : Set} → Ops Γ Top (v ∷ s) → A
ops-top (o-cons e _ _) = ⊥-elim (Top≰lam (Thm-3wf e))
```

An equivalence step at a stack is a step of the spine at the empty stack.

```agda
frame-e : ∀ {Γ a b} s → Γ ∣ s ⊢ a ⟶ᵉ b → Γ ∣ [] ⊢ app* a s ⟶ᵉ app* b s
frame-e []      d = d
frame-e (v ∷ s) d with ⟶ᵉ-prevalid d
... | Pv-Sta pv lv fvv = frame-e s (Me-App d (⟶ᵉ-refl (Pv-Nil (prevalid-ctx pv)) lv fvv))
```

## Closure under a reduction of both heads

If the heads of two well-formed spines reduce, and the spines of the reducts are good, so are
the spines. This is how a β-step at the head is absorbed.

```agda
head-close : ∀ {Γ H H₁ H′ H′₁} s
           → Γ ⊢ app* H s wf → Γ ∣ [] ⊢ H ⟶ᵉ* H₁
           → Γ ⊢ app* H′ s wf → Γ ∣ [] ⊢ H′ ⟶ᵉ* H′₁
           → G Γ (app* H₁ s) (app* H′₁ s)
           → G Γ (app* H s) (app* H′ s)
head-close s wA L wA′ R g =
  G-cast (G-expand* wA (spine-e* s wA L) g) εᵉ (spine-e* s wA′ R) wA′
```

## What this establishes

Goodness packaged with the target's well-formedness, its closure properties in that form,
application and introduction, the base case for a variable, and the spine lemmas the promotion
lemma uses at a non-empty stack.
