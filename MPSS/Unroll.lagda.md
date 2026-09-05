# MPSS: unrolling the stack into the binders, and where that recursion goes

`AUDIT.md` records the most promising measure not covered by `MPSS/Height`: unroll the stack into
the binders, so that the two rules in tension are reconciled by construction.

> `D Γ s (app a b) = max (D Γ (b::s) a) (1 + D Γ [] b)`
> `D Γ (α::s) (λw.b) = max (D Γ [] w) (D (Γ, z ≡ α) s (b ^ z))`
> `D Γ [] (λw.b) = max (D Γ [] w) (D (Γ, z ≤ w) [] (b ^ z))`
> `D Γ s x = 1 + D Γ s α` for `x ≡ α ∈ Γ`, and `0` for a subtype-annotated or unbound `x`

The audit says it "fails at the definition rather than at a case": the variable clause recurses on
the annotation at the *same* stack, and nothing orders that call. That was an observation about
what Agda would accept. This module turns it into a theorem: **the recursion diverges**, and the
configuration it diverges on is the one `MPSS/InfiniteBranching` found — `Ω = (λ⊤. x x)(λ⊤. x x)`
at the empty context and the empty stack.

The same walk is the one the "positional measure" argument in `../PLAN.md` claimed always
terminates. It does not, and the reason is visible in the trace below: `Me-FOp` binds the parameter
to the *stack head*, not to the binder's annotation, and after one unfolding the stack head is a
variable whose annotation is the subtree the walk is already inside. The walk returns.

The audit also names the one repair: charge the annotation at the empty stack instead. That
version, `D′`, does not diverge here — but it no longer decreases at `Me-Pro`, which is what the
measure was for. Both facts are checked below.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Unroll where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _<_; s≤s)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import MPSS.WellFormed
open import MPSS.Develop using (lookupEqv)
open import MPSS.InfiniteBranching
  using (ω; Ω; Unfolds; here!; chain; ToΩ; isω; isvar; toΩ-unf; unf-dom; lc-ω)
open import PSS.Syntax using (fresh; fresh-∉)
open import Data.Nat.Properties using (_≟_)
```

## The measure, with fuel

`D` is written with fuel so that it is a total function whose value is `nothing` exactly when the
recursion has not bottomed out. A configuration on which every fuel returns `nothing` is one the
unfuelled recursion never finishes on.

```agda
_⊔ᵐ_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
just m  ⊔ᵐ just n  = just (m ⊔ n)
just _  ⊔ᵐ nothing = nothing
nothing ⊔ᵐ _       = nothing

sucᵐ : Maybe ℕ → Maybe ℕ
sucᵐ (just n) = just (suc n)
sucᵐ nothing  = nothing

D : ℕ → Ctx → Stack → Tm → Maybe ℕ
D zero    Γ s t = nothing
D (suc n) Γ s (bvar _)  = just 0
D (suc n) Γ s Top       = just 0
D (suc n) Γ s (fvar x) with lookupEqv Γ x
... | nothing = just 0
... | just α  = sucᵐ (D n Γ s α)
D (suc n) Γ s (app a b) = D n Γ (b ∷ s) a ⊔ᵐ sucᵐ (D n Γ [] b)
D (suc n) Γ []      (lam w b) =
  D n Γ [] w ⊔ᵐ D n ((fresh (dom Γ) , sub , w) ∷ Γ) [] (b ^ fvar (fresh (dom Γ)))
D (suc n) Γ (α ∷ s) (lam w b) =
  D n Γ [] w ⊔ᵐ D n ((fresh (dom Γ) , eqv , α) ∷ Γ) s (b ^ fvar (fresh (dom Γ)))
```

## Looking a variable up agrees with membership

Prevalidity binds each name once, so the first equivalence entry for a name is the only one.

```agda
lookup-∈ : ∀ {Γ x α} → Γ prevalid → x ≐ α ∈ Γ → lookupEqv Γ x ≡ just α
lookup-∈ {(x , eqv , α) ∷ Γ} pv (here refl) with x ≟ x
... | yes _ = refl
... | no  q = ⊥-elim (q refl)
lookup-∈ {(y , sub , w) ∷ Γ} (Pv-Ctx pv _ _ _) (there m) = lookup-∈ pv m
lookup-∈ {(y , eqv , β) ∷ Γ} {x} (Pv-EqA pv y∉ _ _) (there m) with x ≟ y
... | yes refl = ⊥-elim (y∉ (∈-dom m))
... | no  _    = lookup-∈ pv m
```

## Absorption

```agda
⊔ᵐ-nothingˡ : ∀ y → nothing ⊔ᵐ y ≡ nothing
⊔ᵐ-nothingˡ (just _) = refl
⊔ᵐ-nothingˡ nothing  = refl

⊔ᵐ-nothingʳ : ∀ x → x ⊔ᵐ nothing ≡ nothing
⊔ᵐ-nothingʳ (just _) = refl
⊔ᵐ-nothingʳ nothing  = refl
```

## The walk on Ω never ends

The invariant is `MPSS/InfiniteBranching`'s: the stack head is `ω` or a variable that unfolds to
it, and the subject is a self-application of a variable that unfolds to it. Three mutually
recursive statements, one per shape the walk passes through, by induction on the fuel.

```agda
toΩ-lc : ∀ {Γ α} → ToΩ Γ α → LC α
toΩ-lc isω       = lc-ω
toΩ-lc (isvar _) = lc-fvar

toΩ-fv : ∀ {Γ α} → ToΩ Γ α → fv α ⊑ dom Γ
toΩ-fv isω       = λ ()
toΩ-fv (isvar u) = λ { (here refl) → unf-dom u }

mutual
  -- the subject `z z` at the empty stack: `Me-App` pushes `z`, and the operator diverges
  div-app : ∀ n {Γ z} → Γ prevalid → Unfolds Γ z
          → D n Γ [] (app (fvar z) (fvar z)) ≡ nothing
  div-app zero    pv u = refl
  div-app (suc n) {Γ} {z} pv u
    rewrite div-var n pv (isvar u) u = ⊔ᵐ-nothingˡ (sucᵐ (D n Γ [] (fvar z)))

  -- a variable that unfolds to ω, with a handle on ω at the stack head: `Me-Pro` unfolds it
  div-var : ∀ n {Γ α y} → Γ prevalid → ToΩ Γ α → Unfolds Γ y
          → D n Γ (α ∷ []) (fvar y) ≡ nothing
  div-var zero    pv tα u = refl
  div-var (suc n) pv tα (here! m)  rewrite lookup-∈ pv m | div-ω n pv tα     = refl
  div-var (suc n) pv tα (chain m u) rewrite lookup-∈ pv m | div-var n pv tα u = refl

  -- ω itself with a handle on the stack: `Me-FOp` binds a fresh parameter to that handle,
  -- and the body is again `z z` at the empty stack, one binding deeper
  div-ω : ∀ n {Γ α} → Γ prevalid → ToΩ Γ α → D n Γ (α ∷ []) ω ≡ nothing
  div-ω zero    pv tα = refl
  div-ω (suc n) {Γ} {α} pv tα
    rewrite div-app n {(fresh (dom Γ) , eqv , α) ∷ Γ}
                    (Pv-EqA pv (fresh-∉ (dom Γ)) (toΩ-lc tα) (toΩ-fv tα))
                    (toΩ-unf tα)
    = ⊔ᵐ-nothingʳ _
```

```agda
D-Ω : ∀ n → D n [] [] Ω ≡ nothing
D-Ω zero    = refl
D-Ω (suc n) rewrite div-ω n Pv-Emp isω = ⊔ᵐ-nothingˡ (sucᵐ (D n [] [] ω))
```

So there is no `n` at which `D` returns a value on `Ω`: the recursion the definition describes is
infinite there. `D` is not a measure because it is not a function.

## The trace, and what it says about the positional argument

Written out, the walk `D` takes from `Ω` is:

| step | configuration | rule |
| --- | --- | --- |
| 0 | `ε ; nil ⊢ ω ω` | `Me-App` pushes the operand |
| 1 | `ε ; ω ⊢ ω` | `Me-FOp` binds `x ≡ ω` |
| 2 | `x ≡ ω ; nil ⊢ x x` | `Me-App` pushes `x` |
| 3 | `x ≡ ω ; x ⊢ x` | `Me-Pro` unfolds `x` |
| 4 | `x ≡ ω ; x ⊢ ω` | `Me-FOp` binds `y ≡ x` |
| 5 | `x ≡ ω, y ≡ x ; nil ⊢ y y` | `Me-App` pushes `y` |
| 6 | `x ≡ ω, y ≡ x ; y ⊢ y` | `Me-Pro` unfolds `y` to `x` |
| 7 | `x ≡ ω, y ≡ x ; y ⊢ x` | `Me-Pro` unfolds `x` |
| 8 | `x ≡ ω, y ≡ x ; y ⊢ ω` | as step 4, one binding deeper |

`../PLAN.md`'s retracted section argued that a recursion of this shape terminates because every
subject is a position in one of finitely many fixed trees, and a jump "from an occurrence of a
variable bound by an enclosing binder to that binder's annotation" lands in a subtree disjoint from
the one it left and can never return. Two things in the trace contradict it.

The binding at step 1 is not to the binder's annotation. `Me-FOp` binds `x` to the **stack head**,
which is the operand of the enclosing application — `ω`, the root's right subtree — not to `⊤`, the
annotation of the abstraction being entered. So the jump at step 3 goes from the operator's body to
the operand subtree, a sibling, not an ancestor's annotation.

And at step 7 the walk is inside that operand subtree — it entered it at step 4 — and unfolds `x`
to `ω`, the *root of the subtree it is already in*. That is the return the argument said could not
happen. It happens because the annotation of `y` is `x`, a variable the walk itself introduced, which
is not a position in any fixed tree.

So the positional argument does not give a measure, and the retraction that rested on it is
withdrawn in `../PLAN.md`.

## The repair, and what it costs

Charging the annotation at the empty stack is what the audit proposes instead. `D′` differs from
`D` in the variable clause only.

```agda
D′ : ℕ → Ctx → Stack → Tm → Maybe ℕ
D′ zero    Γ s t = nothing
D′ (suc n) Γ s (bvar _)  = just 0
D′ (suc n) Γ s Top       = just 0
D′ (suc n) Γ s (fvar x) with lookupEqv Γ x
... | nothing = just 0
... | just α  = sucᵐ (D′ n Γ [] α)
D′ (suc n) Γ s (app a b) = D′ n Γ (b ∷ s) a ⊔ᵐ sucᵐ (D′ n Γ [] b)
D′ (suc n) Γ []      (lam w b) =
  D′ n Γ [] w ⊔ᵐ D′ n ((fresh (dom Γ) , sub , w) ∷ Γ) [] (b ^ fvar (fresh (dom Γ)))
D′ (suc n) Γ (α ∷ s) (lam w b) =
  D′ n Γ [] w ⊔ᵐ D′ n ((fresh (dom Γ) , eqv , α) ∷ Γ) s (b ^ fvar (fresh (dom Γ)))
```

It does bottom out on the configuration `D` diverged on — the stack is dropped at every unfolding,
so `ω` under an equivalence binding is measured at `nil`, where its own binder is a subtype one and
its body costs nothing.

```agda
Γ₀ : Ctx
Γ₀ = (0 , eqv , ω) ∷ []

D′-var : D′ 20 Γ₀ (ω ∷ []) (fvar 0) ≡ just 2
D′-var = refl

D′-ω : D′ 20 Γ₀ (ω ∷ []) ω ≡ just 3
D′-ω = refl
```

But those two values are the wrong way round. `Me-Pro` unfolds `x` to `ω` at the stack `ω :: nil`,
and the measure must strictly decrease across that step: the annotation's value at the current stack
must be below the variable's. Here the variable is worth `2` and its annotation, at that stack, `3`.
The variable was charged for `ω` at the empty stack, where `ω` is cheap; the annotation is measured
at the stack it actually meets, where `Me-FOp` gives its parameter an equivalence binding and the
body unfolds.

```agda
D′-dec-pro-false
  : ¬ (∀ {n v w} → D′ n Γ₀ (ω ∷ []) (fvar 0) ≡ just v
                 → D′ n Γ₀ (ω ∷ []) ω ≡ just w → w < v)
D′-dec-pro-false h with h {20} D′-var D′-ω
... | s≤s (s≤s ())
```

The fuel is not doing any work in that statement: both sides return a value at fuel `20`, and any
function satisfying `D′`'s equations agrees with a fuelled run wherever the run returns a value.

## What this establishes

`D-Ω`: the stack-unrolling measure `D` has no value at `Ω`, for any fuel — its recursion is
infinite there. That is the "fails at the definition" of the audit made into a theorem, and it is
the same three rules as `MPSS/InfiniteBranching`: `Me-App` pushes, `Me-FOp` binds the parameter to
what was pushed, `Me-Pro` unfolds it back to a term whose body does the same.

The trace refutes the positional-measure argument of `../PLAN.md`: `Me-FOp` binds to the stack
head rather than the binder's annotation, and after one unfolding the walk re-enters the root of
the subtree it is in.

`D′-dec-pro-false`: charging the annotation at the empty stack gives a value here, and loses the
one property the measure exists for. A variable must cost strictly more than its annotation at
whatever stack is current, and the stack is unbounded relative to the context.
