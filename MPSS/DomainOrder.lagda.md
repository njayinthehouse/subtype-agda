# MPSS: the domain order on bounds, and the step of the recursion that descends in it

`MPSS/CONJ8.md` §9 found, by running the recursion of Conjecture 8, that the bound of each round
is the domain of the bound of the round before. This module states the order and proves the one
fact that makes it the recursion's order:

> if an abstraction `λx≤w.u` is below a term `T`, and `T v` is well-formed, then `T` is below an
> abstraction `λd.⊤` whose domain `d` is `≡wf` to `w`, and the operand is below the bound:
> `v ≤*wf w`.

So when `MPSS/PushWf` narrows the parameter of an abstraction that meets an operand — in the
chain to a target `T`, under the operand `T` is applied to — the pair it asks Conjecture 8 for is
`(v, w)` with `w` the domain of `T`.

The conditional form of Conjecture 8 is stated at the end as a type and **not proved here**; what
is owed is listed in `MPSS/CONJ8.md` §10.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.DomainOrder where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Induction.WellFounded using (Acc)

open import MPSS.WellFormed
open import MPSS.Static using (Lem-15; Lem-16; ⊑*wf⇒wfʳ)
open import MPSS.Unconditional using (Lem-10)
open import MPSS.Assumed using (Conj-8)
open import MPSS.Conjecture8 using (CoCtx; plug)
```

## The order

A target steps down to its domain, and to itself applied — in any extension of its context, since
the recursion goes under binders.

```agda
infix 4 _▷ᵈ_
data _▷ᵈ_ : (Ctx × Tm) → (Ctx × Tm) → Set where

  ▷-dom : ∀ {Γ T d} (Δ : Ctx) {v}
        → (Δ ++ Γ) ⊢ app T v wf
        → (Δ ++ Γ) ⊢ T ≤*wf lam d Top
        → (Γ , T) ▷ᵈ (Δ ++ Γ , d)

  ▷-app : ∀ {Γ T} (Δ : Ctx) {v}
        → (Δ ++ Γ) ⊢ app T v wf
        → (Γ , T) ▷ᵈ (Δ ++ Γ , app T v)

-- accessibility is for the converse: everything a target steps down to
_◁ᵈ_ : (Ctx × Tm) → (Ctx × Tm) → Set
q ◁ᵈ p = p ▷ᵈ q

Ranked : Ctx → Tm → Set
Ranked Γ T = Acc _◁ᵈ_ (Γ , T)
```

## The step

```agda
domain-step : ∀ {Γ T w u v}
            → Γ ⊢ lam w u ≤*wf T
            → Γ ⊢ app T v wf
            → ∃[ d ] ((Γ ⊢ T ≤*wf lam d Top) × (Γ ⊢ w ⊑wf[ eqv-m ] d) × (Γ ⊢ v ≤*wf w))
domain-step {Γ} {T} {w} {u} {v} below (Wf-App {t = d} T≤ v≤d)
  with ⊑*wf⇒wfˡ below | ⊑*wf⇒wfʳ T≤
... | Wf-Fun _ _ ww | Wf-Fun _ _ wd =
  d , T≤ , w≋d , Ws-Trs v≤d wd (Ws-Sub wd (Lem-16 (Lem-15 w≋d)) ww)
  where
    w≋d : Γ ⊢ w ⊑wf[ eqv-m ] d
    w≋d = Lem-10 (Ws-Trs below (⊑*wf⇒wfʳ below) T≤)
```

## The conditional form of the conjecture — a statement, not a theorem

Conjecture 8 at the pairs whose targets, under every prefix of the covariant context, are
accessible in the domain order.

```agda
Conj-8ʳ : Set
Conj-8ʳ = ∀ {Γ u t} (C : CoCtx)
        → (∀ (C′ : CoCtx) → Γ ⊢ plug C′ t wf → Ranked Γ (plug C′ t))
        → LC u → LC t
        → Γ ⊢ u ≤*wf t
        → Γ ⊢ plug C u wf
        → Γ ⊢ plug C t wf
        → Γ ⊢ plug C u ≤*wf plug C t
```

## What this establishes

`domain-step`, and the definitions. `Conj-8ʳ` is only declared.
