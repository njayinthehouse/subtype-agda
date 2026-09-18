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

## What this establishes

The definition, its two projections, and its independence of the accessibility proof. The
fundamental lemma — every well-formed term below a ranked target is good at it, under good
substitutions — is owed.
