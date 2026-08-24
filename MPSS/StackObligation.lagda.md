# Testing the fix: does a typing obligation on the stack suffice?

The gap is that at stack `α :: s` nothing records that `α` is below the annotation it will meet.
`Pv-Sta` demands only scoping. The proposal is to record the obligation — either in prevalidity
or as an extra premise on `Ms-FOp`.

Whether that helps reduces to one question, which needs no rule change to ask. `Ms-Fun` binds the
parameter `x ≤ t`; `Ms-FOp` binds it `x ≡ α`. If the obligation `α ≤ t` were available, could a
body derivation under `x ≤ t` be replayed under `x ≡ α`?

**Single-step: no. Multi-step: yes.** That difference is the answer, and it is why the obligation
alone is not enough.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackObligation where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.Subtyping
```

## Chains of promotion

```agda
infix 3 _∣_⊢_⟶ˢ*_
data _∣_⊢_⟶ˢ*_ : Ctx → Stack → Tm → Tm → Set where
  εˢ   : ∀ {Γ s t} → Γ ∣ s ⊢ t ⟶ˢ* t
  _◅ˢ_ : ∀ {Γ s t u v} → Γ ∣ s ⊢ t ⟶ˢ u → Γ ∣ s ⊢ u ⟶ˢ* v → Γ ∣ s ⊢ t ⟶ˢ* v
```

## A context with a genuine chain of bounds

`y ≤ Top` and `z ≤ y`, so `z` really is below `y` and the two are distinct. That is the smallest
setting in which the question has teeth: with only `Top` around, `Ms-Top` trivialises everything.

```agda
-- y = 0, z = 1, and the parameter will be x = 2
Γ₂ : Ctx
Γ₂ = (1 , sub , fvar 0) ∷ (0 , sub , Top) ∷ []

pv₂ : Γ₂ prevalid
pv₂ = Pv-Ctx (Pv-Ctx Pv-Emp (λ ()) lc-Top (λ ())) 1∉ lc-fvar fv-y
  where
    1∉ : 1 ∉ (0 ∷ [])
    1∉ (here ())
    fv-y : fv (fvar 0) ⊑ (0 ∷ [])
    fv-y (here refl) = here refl

fv-in : ∀ {n} → n ∈ (1 ∷ 0 ∷ []) → n ∈ dom Γ₂
fv-in h = h

Γsub Γeqv : Ctx
Γsub = (2 , sub , fvar 0) ∷ Γ₂     -- x ≤ y
Γeqv = (2 , eqv , fvar 1) ∷ Γ₂     -- x ≡ z

pv-sub : Γsub prevalid
pv-sub = Pv-Ctx pv₂ 2∉ lc-fvar (λ { (here refl) → there (here refl) })
  where
    2∉ : 2 ∉ dom Γ₂
    2∉ (here ())
    2∉ (there (here ()))

pv-eqv : Γeqv prevalid
pv-eqv = Pv-EqA pv₂ 2∉ lc-fvar (λ { (here refl) → here refl })
  where
    2∉ : 2 ∉ dom Γ₂
    2∉ (here ())
    2∉ (there (here ()))
```

The obligation holds: `z` is below `y`.

```agda
obligation : Γ₂ ∣ [] ⊢ fvar 1 ≤ fvar 0
obligation = As-Left-1 (Ms-Pro (Pv-Nil pv₂) (here refl)) (As-Refl (Pv-Nil pv₂))
```

## Under `x ≤ y`, the parameter reaches `y` in one step

```agda
under-sub : Γsub ∣ [] ⊢ fvar 2 ⟶ˢ fvar 0
under-sub = Ms-Pro (Pv-Nil pv-sub) (here refl)
```

## Under `x ≡ z`, it cannot — even though `z ≤ y`

`Ms-Pro` is blocked because the two lookups are disjoint: `x`'s annotation is an equivalence one.
`Ms-Top` lands on `Top`. `Ms-Equ` can only unfold `x` to `z`, and `z` cannot equivalence-reduce
further, since *its* annotation is a subtype annotation.

```agda
no-eqv-step : ¬ (Γeqv ∣ [] ⊢ fvar 2 ⟶ˢ fvar 0)
no-eqv-step (Ms-Pro _ (there (here ())))
no-eqv-step (Ms-Pro _ (there (there (here ()))))
no-eqv-step (Ms-Equ _ (Me-Pro _ (here refl) d)) = inner d
  where
    inner : ¬ (Γeqv ∣ [] ⊢ fvar 1 ⟶ᵉ fvar 0)
    inner (Me-Pro _ (there (here ())) _)
    inner (Me-Pro _ (there (there (here ()))) _)
no-eqv-step (Ms-Equ _ (Me-Pro _ (there (here ())) _))
no-eqv-step (Ms-Equ _ (Me-Pro _ (there (there (here ()))) _))
```

So replaying a single step is impossible:

```agda
single-step-narrowing-false :
  ¬ (∀ {Γ x t α s b b'}
     → Γ ∣ [] ⊢ α ≤ t
     → ((x , sub , t) ∷ Γ) ∣ s ⊢ b ⟶ˢ b'
     → ((x , eqv , α) ∷ Γ) ∣ s ⊢ b ⟶ˢ b')
single-step-narrowing-false narrow = no-eqv-step (narrow obligation under-sub)
```

## But the chain does go through

`x` unfolds to `z`, and `z` promotes to `y`. The information is not lost — it just takes two steps
where the rule needs one.

```agda
multi-step-ok : Γeqv ∣ [] ⊢ fvar 2 ⟶ˢ* fvar 0
multi-step-ok =
  Ms-Equ (Pv-Nil pv-eqv) (Me-Pro (Pv-Nil pv-eqv) (here refl) (Me-Var (Pv-Nil pv-eqv)))
  ◅ˢ (Ms-Pro (Pv-Nil pv-eqv) (there (here refl)) ◅ˢ εˢ)
```

## What this establishes

Recording the obligation on the stack is **necessary but not sufficient**.

It is necessary: without `α ≤ t`, the parameter under `Ms-FOp` may be pinned to something not
below the annotation at all, and then nothing recovers the unapplied fact.

It is not sufficient: even *with* `α ≤ t` in hand, the replay costs an extra step. Under
`x ≤ t` the parameter reaches the annotation by one `Ms-Pro`; under `x ≡ α` it must first unfold
to `α` and then promote, which is two. `Ms-Fun` and `Ms-FOp` both have a **single** reduction as
their premise, so a two-step replay does not fit the rule.

This is the same single-step-versus-multi-step mismatch v1 identifies as the reason Hutchins'
argument fails: "Hutchins' system requires that we have `v ≤ t` to do the β-reduction, so we can
complete the diagram in multiple steps, but unfortunately this is not the required global
commutativity for the type safety."

So the fix has to reach the shape of the rules, not only their side conditions.
