# MPSS: hereditary liftability, by recursion on the domain order

Groundwork for a provable variant of Conjecture 8 (`MPSS/CONJ8.md` §15–16). The variant is for
targets that are accessible in the domain order of `MPSS/DomainOrder` — it excludes, for instance,
the type of the polymorphic identity, where the order cycles — and its proof has to be by
reducibility: a rank induction on the conjecture itself meets uses at pairs of unrelated rank
(`CONJ8.md` §9, §13), whereas a predicate *defined* by recursion on the rank can be *used* at any
rank.

`Good a m`, for `a : Ranked Γ T`: `m` is well-formed, below `T`, and — in every extension of the
context, for every operand `v` that is good at the domain of `T` — `m v` is below `T v` and good
at `T v`. It is Conjecture 8 for spines, made hereditary.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Reducible where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc)

open import MPSS.WellFormed
open import MPSS.DomainOrder using (_▷ᵈ_; _◁ᵈ_; ▷-dom; ▷-app; Ranked)

Good : ∀ {p : Ctx × Tm} → Acc _◁ᵈ_ p → Tm → Set
Good {Γ , T} (acc rs) m =
    (Γ ⊢ m wf)
  × (Γ ⊢ m ≤*wf T)
  × (∀ (Δ : Ctx) {v d}
       (w : (Δ ++ Γ) ⊢ app T v wf) (e : (Δ ++ Γ) ⊢ T ≤*wf lam d Top)
     → Good (rs (▷-dom Δ w e)) v
     → ((Δ ++ Γ) ⊢ app m v ≤*wf app T v) × Good (rs (▷-app Δ w)) (app m v))

good-wf : ∀ {Γ T m} (a : Ranked Γ T) → Good a m → Γ ⊢ m wf
good-wf (acc _) g = proj₁ g

good-≤ : ∀ {Γ T m} (a : Ranked Γ T) → Good a m → Γ ⊢ m ≤*wf T
good-≤ (acc _) g = proj₁ (proj₂ g)
```

## It does not depend on the accessibility proof

```agda
good-irr : ∀ {p : Ctx × Tm} (a b : Acc _◁ᵈ_ p) {m} → Good a m → Good b m
good-irr {Γ , T} (acc rs) (acc rs′) (wm , d , h) =
  wm , d , λ Δ w e gv →
    let gv′ = good-irr (rs′ (▷-dom Δ w e)) (rs (▷-dom Δ w e)) gv
        r   = h Δ w e gv′
    in proj₁ r , good-irr (rs (▷-app Δ w)) (rs′ (▷-app Δ w)) (proj₂ r)
```

## Terms that promote to the target at every stack are good

The base case of the reducibility argument. If `m ⟶ˢ T` holds at every stack, in every context of
a family `Q` closed under extension — a variable and its bound, with `Q Γ′` = "`x ≤ T ∈ Γ′`" —
then `m` is good at `T`: `m v ⟶ˢ T v` is `Ms-App` over the step at the stack `v ∷ s`, between
well-formed terms (`app-wf-mid`), and `m v`, `T v` are again such a pair.

```agda
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Weakening using (⊑*wf-weaken)
open import MPSS.Subst.Base using (dom-++)
open import MPSS.Conjecture8Star using (app-wf-mid)

Steps : (Ctx → Set) → Tm → Tm → Set
Steps Q m T = ∀ {Γ′ s} → Q Γ′ → Γ′ ∣ s prevalid → Γ′ ∣ s ⊢ m ⟶ˢ T

one : ∀ {Q : Ctx → Set} {Γ m T} → Q Γ → Steps Q m T → Γ ⊢ m wf → Γ ⊢ T wf → Γ ⊢ m ≤*wf T
one q st wm wT =
  Ws-Sub wm (Ws-Lf2 wm (st q (Pv-Nil (wf⇒prevalid wm))) wT (Ws-Rfl (wf⇒prevalid wm))) wT

arg-wf′ : ∀ {Γ f v} → Γ ⊢ app f v wf → Γ ⊢ v wf
arg-wf′ (Wf-App _ d₂) = ⊑*wf⇒wfˡ d₂

neutral-good : ∀ (Q : Ctx → Set) (Q-ext : ∀ (Δ : Ctx) {Γ} → Q Γ → Q (Δ ++ Γ))
               {Γ T m} (a : Ranked Γ T) → Q Γ → Steps Q m T
             → Γ ⊢ m wf → Γ ⊢ T wf → Good a m
neutral-good Q Q-ext {Γ} {T} {m} (acc rs) q st wm wT =
  wm , m≤T , λ Δ {v} w e gv →
    let wv   = arg-wf′ w
        Q′   : Ctx → Set
        Q′ Γ′ = Q Γ′ × (fv v ⊑ dom Γ′)
        ext′ : ∀ (Δ′ : Ctx) {Γ′} → Q′ Γ′ → Q′ (Δ′ ++ Γ′)
        ext′ Δ′ {Γ′} (q₀ , f) = Q-ext Δ′ q₀ , λ h → subst (_ ∈_) (sym (dom-++ Δ′ Γ′)) (∈-++⁺ʳ (dom Δ′) (f h))
        q′   : Q′ (Δ ++ Γ)
        q′   = Q-ext Δ q , wf-fv wv
        st′  : Steps Q′ (app m v) (app T v)
        st′  = λ { (q₀ , f) pv → Ms-App (st q₀ (Pv-Sta pv (wf⇒lc wv) f)) }
        m≤TΔ = ⊑*wf-weaken [] Δ (wf⇒prevalid w) m≤T
        wmv  = app-wf-mid m≤TΔ (⊑*wf⇒wfˡ m≤TΔ) w
    in one {Q′} q′ st′ wmv w , neutral-good Q′ ext′ (rs (▷-app Δ w)) q′ st′ wmv w
  where
    m≤T = one {Q} q st wm wT
```

## Goodness is closed under equivalence expansion on the left

If `m ⟶ᵉ m′` with `m` well-formed and `m′` good at `T`, then `m` is good at `T`: the step goes
under the operand by `app-e`, and a layer absorbs it. This is what lets the abstraction case of
the fundamental lemma go through a β-step.

```agda
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.Conj8Reduction using (app-e)

expand-≤ : ∀ {Γ m m′ T} → Γ ⊢ m wf → Γ ∣ [] ⊢ m ⟶ᵉ m′ → Γ ⊢ m′ wf → Γ ⊢ m′ ≤*wf T → Γ ⊢ m ≤*wf T
expand-≤ wm e wm′ d =
  Ws-Trs (Ws-Sub wm (Ws-Lf1 e (Ws-Rfl (wf⇒prevalid wm))) wm′) wm′ d

good-expand : ∀ {Γ T m m′} (a : Ranked Γ T)
            → Γ ⊢ m wf → Γ ∣ [] ⊢ m ⟶ᵉ m′ → Good a m′ → Good a m
good-expand {Γ} {T} {m} {m′} (acc rs) wm e (wm′ , d′ , h) =
  wm , m≤T , λ Δ {v} w e′ gv →
    let r    = h Δ w e′ gv
        pvΔ  = wf⇒prevalid w
        eΔ   = ⟶ᵉ-weaken [] Δ (Pv-Nil pvΔ) e
        m≤TΔ = ⊑*wf-weaken [] Δ pvΔ m≤T
        wmv  = app-wf-mid m≤TΔ (⊑*wf⇒wfˡ m≤TΔ) w
        ev   = app-e (arg-wf′ w) eΔ
        gm′v = proj₂ r
        am   = rs (▷-app Δ w)
    in expand-≤ wmv ev (good-wf am gm′v) (proj₁ r) , good-expand am wmv ev gm′v
  where
    m≤T = expand-≤ wm e wm′ d′
```

## Goodness composes

If `m` is good at `T` and `T` is good at `T′`, then `m` is good at `T′`: the case of `Ws-Trs`. An
operand good at the domain of `T′` is good at the domain of `T` — the same domain, reached through
`T ≤*wf T′` — up to the accessibility proof, which does not matter.

```agda
good-trans : ∀ {Γ T T′ m} (a : Ranked Γ T) (b : Ranked Γ T′)
           → Good a m → Good b T → Good b m
good-trans {Γ} {T} {T′} {m} (acc rs) (acc rs′) (wm , m≤T , h) (wT , T≤T′ , h′) =
  wm , Ws-Trs m≤T wT T≤T′ , λ Δ {v} w′ e′ gv →
    let pvΔ   = wf⇒prevalid w′
        T≤T′Δ = ⊑*wf-weaken [] Δ pvΔ T≤T′
        wTΔ   = ⊑*wf⇒wfˡ T≤T′Δ
        w     = app-wf-mid T≤T′Δ wTΔ w′
        e     = Ws-Trs T≤T′Δ (⊑*wf⇒wfˡ e′) e′
        gv₀   = good-irr (rs′ (▷-dom Δ w′ e′)) (rs (▷-dom Δ w e)) gv
        r     = h Δ w e gv₀
        r′    = h′ Δ w′ e′ gv
    in Ws-Trs (proj₁ r) w (proj₁ r′)
     , good-trans (rs (▷-app Δ w)) (rs′ (▷-app Δ w′)) (proj₂ r) (proj₂ r′)
```

## A well-formed reduct of the target is good at it

The case of `Ws-Rgh`: if `T ⟶ᵉ T′` with both well-formed, then `T′` is good at `T`, and with
`good-trans` whatever is good at `T′` is good at `T`.

```agda
reduct-≤ : ∀ {Γ T T′} → Γ ⊢ T′ wf → Γ ∣ [] ⊢ T ⟶ᵉ T′ → Γ ⊢ T wf → Γ ⊢ T′ ≤*wf T
reduct-≤ wT′ e wT = Ws-Sub wT′ (Ws-Rgh (Ws-Rfl (wf⇒prevalid wT)) e) wT

good-reduct : ∀ {Γ T T′} (a : Ranked Γ T)
            → Γ ⊢ T wf → Γ ∣ [] ⊢ T ⟶ᵉ T′ → Γ ⊢ T′ wf → Good a T′
good-reduct {Γ} {T} {T′} (acc rs) wT e wT′ =
  wT′ , T′≤T , λ Δ {v} w e′ gv →
    let pvΔ   = wf⇒prevalid w
        T′≤TΔ = ⊑*wf-weaken [] Δ pvΔ T′≤T
        wT′v  = app-wf-mid T′≤TΔ (⊑*wf⇒wfˡ T′≤TΔ) w
        ev    = app-e (arg-wf′ w) (⟶ᵉ-weaken [] Δ (Pv-Nil pvΔ) e)
    in reduct-≤ wT′v ev w , good-reduct (rs (▷-app Δ w)) w ev wT′v
  where
    T′≤T = reduct-≤ wT′ e wT
```

## Two well-formed terms that join by equivalence steps

Inside a layer only the ends and the promotion points are well-formed; the equivalence steps
between them pass through terms that need not be. So the closure that a layer needs is for
*chains*: if `p` and `t` are well-formed and `p ⟶ᵉ* c ⟵ᵉ* t`, then `p` is good at `t`. Under an
operand both chains go to `c v` by `app-e*`, and `p v`, `t v` join again.

```agda
open import MPSS.Conj8Reduction using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; app-e*)

lf1* : ∀ {Γ a a′ b} → Γ ∣ [] ⊢ a ⟶ᵉ* a′ → Γ ⊢ a′ ⊑wf[ sub-m ] b → Γ ⊢ a ⊑wf[ sub-m ] b
lf1* εᵉ       d = d
lf1* (e ◅ᵉ p) d = Ws-Lf1 e (lf1* p d)

rgh* : ∀ {Γ v b c} → Γ ∣ [] ⊢ b ⟶ᵉ* c → Γ ⊢ v ⊑wf[ sub-m ] c → Γ ⊢ v ⊑wf[ sub-m ] b
rgh* εᵉ       d = d
rgh* (e ◅ᵉ p) d = Ws-Rgh (rgh* p d) e

weaken* : ∀ (Δ : Ctx) {Γ a b} → (Δ ++ Γ) prevalid → Γ ∣ [] ⊢ a ⟶ᵉ* b → (Δ ++ Γ) ∣ [] ⊢ a ⟶ᵉ* b
weaken* Δ pv εᵉ       = εᵉ
weaken* Δ pv (e ◅ᵉ p) = ⟶ᵉ-weaken [] Δ (Pv-Nil pv) e ◅ᵉ weaken* Δ pv p

join-≤ : ∀ {Γ p c t} → Γ ⊢ p wf → Γ ∣ [] ⊢ p ⟶ᵉ* c → Γ ∣ [] ⊢ t ⟶ᵉ* c → Γ ⊢ t wf → Γ ⊢ p ≤*wf t
join-≤ wp L R wt = Ws-Sub wp (lf1* L (rgh* R (Ws-Rfl (wf⇒prevalid wp)))) wt

good-join : ∀ {Γ p c t} (a : Ranked Γ t)
          → Γ ⊢ p wf → Γ ∣ [] ⊢ p ⟶ᵉ* c → Γ ∣ [] ⊢ t ⟶ᵉ* c → Γ ⊢ t wf → Good a p
good-join {Γ} {p} {c} {t} (acc rs) wp L R wt =
  wp , p≤t , λ Δ {v} w e′ gv →
    let pvΔ  = wf⇒prevalid w
        p≤tΔ = ⊑*wf-weaken [] Δ pvΔ p≤t
        wpv  = app-wf-mid p≤tΔ (⊑*wf⇒wfˡ p≤tΔ) w
        wv   = arg-wf′ w
        Lv   = app-e* wv (weaken* Δ pvΔ L)
        Rv   = app-e* wv (weaken* Δ pvΔ R)
    in join-≤ wpv Lv Rv w , good-join (rs (▷-app Δ w)) wpv Lv Rv w
  where
    p≤t = join-≤ wp L R wt
```

## What this establishes

The definition, its two projections, its independence of the accessibility proof, the base
case (a term that promotes to the target at every stack — a variable and its bound — is good at
it), and three closure properties: equivalence expansion on the left, composition, and a
well-formed reduct of the target.
The fundamental lemma — every well-formed term below a ranked target is good at it, under good
substitutions — is owed.
