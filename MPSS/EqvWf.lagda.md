# MPSS: equivalence reduction does not preserve well-formedness

`MPSS/AUDIT` records that closing Lemma 23's `Wf-App` case needs a statement the paper never
makes:

> If `Γ ⊢ u wf` and `Γ;nil ⊢ u ⟶≡ v` then `Γ ⊢ v wf`.

It is false, and the reason is structural rather than incidental. Contexts are only ever required
to be **prevalid** — every annotation locally closed and scoped in the entries before it — and
prevalidity says nothing about an annotation being *well-formed*. `Me-Pro` replaces a variable by
a reduct of its equivalence annotation, and `Wf-PrE` calls that variable well-formed on the
strength of the annotation merely existing. So a context may hold an ill-formed annotation, and
one `Me-Pro` step exposes it.

The witness is the smallest one: `x ≡ Top Top`, with `Top Top` locally closed and closed, hence a
legal annotation, but not well-formed, since `Wf-App` would need `Top` below an abstraction.

That last step is Theorem 11, so the refutation is stated as a consequence of Lemmas 1 and 2,
like Theorem 11 itself. Nothing weaker will do: `Ws-Trs` lets a well-subtyping chain pass through
an arbitrary intermediate term, so ruling out `Γ ⊢ Top ≤*wf λy≤t.Top` really does require
collapsing the chain first.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.EqvWf where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.WellFormed
open import MPSS.Assumed using (Lem-1; Lem-2)
open import MPSS.Progress using (Thm-11wf)
```

## The statement

```agda
Wf-⟶ᵉ : Set
Wf-⟶ᵉ = ∀ {Γ u v} → Γ ⊢ u wf → Γ ∣ [] ⊢ u ⟶ᵉ v → Γ ⊢ v wf
```

## The witness

A single equivalence annotation, whose value is a legal but ill-formed term.

```agda
bad : Tm
bad = app Top Top

Γ₀ : Ctx
Γ₀ = (0 , eqv , bad) ∷ []

ctx₀ : Γ₀ prevalid
ctx₀ = Pv-EqA Pv-Emp (λ ()) (lc-app lc-Top lc-Top) (λ ())

pv₀ : Γ₀ ∣ [] prevalid
pv₀ = Pv-Nil ctx₀
```

The variable is well-formed, on the strength of the annotation existing.

```agda
w₀ : Γ₀ ⊢ fvar 0 wf
w₀ = Wf-PrE ctx₀ (here refl)
```

`Me-Pro` unfolds it. The annotation reduces to itself: `Me-App` takes the operator premise at the
pushed stack `Top :: nil`, which is prevalid because `Top` is closed.

```agda
pvₛ : Γ₀ ∣ (Top ∷ []) prevalid
pvₛ = Pv-Sta pv₀ lc-Top (λ ())

step : Γ₀ ∣ [] ⊢ fvar 0 ⟶ᵉ bad
step = Me-Pro pv₀ (here refl) (Me-App (Me-Top pvₛ) (Me-Top pv₀))
```

But the reduct is not well-formed: `Wf-App` would place `Top` below an abstraction.

```agda
no-wf : Lem-1 → Lem-2 → ¬ (Γ₀ ⊢ bad wf)
no-wf lem-1 lem-2 (Wf-App d₁ _) = Thm-11wf lem-1 lem-2 d₁
```

## The refutation

```agda
Wf-⟶ᵉ-false : Lem-1 → Lem-2 → ¬ Wf-⟶ᵉ
Wf-⟶ᵉ-false lem-1 lem-2 h = no-wf lem-1 lem-2 (h w₀ step)
```

## What this establishes

The *naive* route to Lemma 23 is closed — the one that narrows a well-subtyping chain step by
step and so needs each intermediate to be well-formed. The paper does not take that route: its
Lemma 7 accumulates the equivalence steps as reduction sequences in an existential diagram, which
needs well-formedness only at the chain's endpoints and at the `Ws-Lf2` nodes, where it is a
premise. So this is not evidence against Lemma 23.

What it does establish stands on its own. More broadly it says that MPSS's well-formedness
judgement is not stable under the very reduction its subtyping relation is built from, and the
cause is that contexts carry a scoping condition where they would need a typing one. `Ws-Lf2`
already compensates for this by hand, carrying well-formedness of both sides as premises; the gap
in Lemma 23 is exactly the place where `Ws-Lf1` and `Ws-Rgh` would need the same compensation and
do not have it.

Two things this does *not* say. It is not a counterexample to Lemma 23, which the paper's own
technique may well establish. And it is not independent of the commutation results, since
Theorem 11 is what rules out the reduct.
