# The assumed repair of Proposition 17 is itself refuted

`MPSS/Assumed` carries `Prop-17ʳ`: for every prevalid `Γ;s`, locally closed `u` scoped in
`dom Γ`, if `u ↦ v` then `Γ;s ⊢ u ⟶ᵉ v`. Its instance at the empty stack is exactly the
statement `Prop-17` that `MPSS/BetaScope` refutes, and the refutation survives well-formedness
(`MPSS/BetaScopeWf`). So `Prop-17ʳ` is uninhabited, and every result that takes it as an
argument — Lemma 6, Theorem 5, Proposition 27 and `type-safety` in `MPSS/Unconditional` — is
proved from a false hypothesis.

The scoping premise `fv u ⊑ dom Γ` does not touch the failure: the redex body is opened with a
name the context does not bind, and `Me-Bet` reduces that body at `Γ;s` regardless of how `u`
itself is scoped. The repair the audit identifies is to the rule `Me-Bet`, not to the statement,
and a statement over the unrepaired `⟶ᵉ` cannot carry it.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Prop17Refuted where

open import Relation.Nullary using (¬_)

open import MPSS.Assumed using (Prop-17ʳ)
open import MPSS.BetaScope using (Prop-17; prop-17-false)
open import MPSS.BetaScopeWf using (Γ₀; R; pv₀; lc-A; lc-T; R↦; no-step)
open import MPSS.WellFormed
open import Data.List.Base using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Empty using (⊥)
```

## Through `MPSS/BetaScope`

```agda
Prop-17ʳ⇒Prop-17 : Prop-17ʳ → Prop-17
Prop-17ʳ⇒Prop-17 p pv lc sc st = p pv lc sc st

¬Prop-17ʳ : ¬ Prop-17ʳ
¬Prop-17ʳ p = prop-17-false (Prop-17ʳ⇒Prop-17 p)
```

## Through `MPSS/BetaScopeWf`, on the well-formed witness

```agda
lc-R : LC R
lc-R = lc-app lc-A lc-T

fv-R : fv R ⊑ dom Γ₀
fv-R (here refl) = here refl

¬Prop-17ʳ-wf : ¬ Prop-17ʳ
¬Prop-17ʳ-wf p = no-step (p (Pv-Nil pv₀) lc-R fv-R R↦)
```
