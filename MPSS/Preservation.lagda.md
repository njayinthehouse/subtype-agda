# MPSS: Proposition 27 and Theorem 5 — preservation

> **Proposition 27 (Reduction preserves subtyping derivation).** Let `Γ;s` be an extended
> context, and `u`, `u′`, `v` terms with `Γ ⊢ u ≤*wf v`, `u ↦ u′` and `Γ ⊢ u′ wf`. Then
> `Γ ⊢ u′ ≤*wf v`.
>
> **Theorem 5 (Preservation).** Let `Γ` be a logical context and `t`, `t′`, `u` terms. If
> `Γ ⊢ t ≤*wf u` and `t ↦ t′`, then `Γ ⊢ t′ ≤*wf u`.

Proposition 27 *is* Theorem 5, with the well-formedness of the reduct assumed instead of derived.
That is what makes it provable on its own: Lemma 6 is the only thing Theorem 5 adds, and the
circularity one might fear — Theorem 5 through Lemma 6 through Proposition 27 — does not arise,
because Proposition 27 never derives the reduct's well-formedness.

Both proofs turn on the same step, and it is the step that needs Proposition 17: the operational
step `t ↦ t′` has to be re-read as an equivalence step `Γ;nil ⊢ t ⟶≡ t′` before `Ws-Rgh` can
consume it. That is why preservation, unlike progress, inherits the β-rule defect. The repaired
form is assumed from `MPSS/Assumed`.

**A slip in the paper's Proposition 27.** It writes "by rule `Ws-Rfl` and `Ws-Lf1`, we have
`Γ ⊢ u′ ≤wf u`". `Ws-Lf1` moves the *left*-hand side, so from `u ⟶≡ u′` it yields `Γ ⊢ u ≤wf u′`,
the wrong way round. The rule that gives the stated conclusion is `Ws-Rgh`, which moves the
right-hand side — and which is what the paper's own proof of Theorem 5 cites for the same step.
The conclusion is correct and is derived below with `Ws-Rgh`; only the citation is wrong.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Preservation where

open import Data.List.Base using (List; []; _∷_)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Assumed using (Prop-17ʳ)

open import PSS.Reduction using (_↦_)
```

## Pushing an equivalence step along the left, statically

Proposition 27's argument has nothing to do with the operational semantics: it works for any
equivalence step, in either mode. Isolating it first makes the proposition a corollary and makes
the lemma available elsewhere.

`Ws-Rfl` gives `u′ ⊑wf u′`; `Ws-Rgh` walks the right-hand side back along `u ⟶≡ u′` to give
`u′ ⊑wf u`; `Ws-Sub` lifts that to the transitive closure, and `Ws-Trs` composes it with the
derivation in hand. The one thing it needs beyond the step is the reduct's well-formedness, which
`Ws-Sub` demands.

Note that this is *not* the static counterpart of `push≡` in `MPSS/Transitivity`, which needs both
commutation results. It is cheaper because `Ws-Rgh` can absorb the step on the right rather than
having to commute it past whatever the derivation does next.

```agda
push≡*wf : ∀ {Γ u u' v m}
         → Γ ∣ [] ⊢ u ⟶ᵉ u'
         → Γ ⊢ u ⊑*wf[ m ] v
         → Γ ⊢ u' wf
         → Γ ⊢ u' ⊑*wf[ m ] v
push≡*wf {Γ} {u} {u'} e d w' = Ws-Trs (Ws-Sub w' u'⊑u wu) wu d
  where
    wu : Γ ⊢ u wf
    wu = ⊑*wf⇒wfˡ d

    u'⊑u = Ws-Rgh (Ws-Rfl (wf⇒prevalid wu)) e
```

## Proposition 27

Proposition 17 turns the operational step into an equivalence step, and the lemma above does the
rest.

```agda
Prop-27 : Prop-17ʳ
        → ∀ {Γ u u' v}
        → Γ ⊢ u ⊑*wf[ sub-m ] v
        → u ↦ u'
        → Γ ⊢ u' wf
        → Γ ⊢ u' ⊑*wf[ sub-m ] v
Prop-27 prop-17 {Γ} {u} d st w' = push≡*wf e d w'
  where
    wu = ⊑*wf⇒wfˡ d
    e  = prop-17 (Pv-Nil (wf⇒prevalid wu)) (wf⇒lc wu) (wf-fv wu) st
```

## Theorem 5

Exactly Proposition 27, with Lemma 6 supplying the missing premise.

```agda
Lem-6 : Set
Lem-6 = ∀ {Γ t t'} → Γ ⊢ t wf → t ↦ t' → Γ ⊢ t' wf

Thm-5 : Prop-17ʳ → Lem-6
      → ∀ {Γ t t' u}
      → Γ ⊢ t ⊑*wf[ sub-m ] u
      → t ↦ t'
      → Γ ⊢ t' ⊑*wf[ sub-m ] u
Thm-5 prop-17 lem-6 d st = Prop-27 prop-17 d st (lem-6 (⊑*wf⇒wfˡ d) st)
```

## What this establishes

`push≡*wf`, which needs nothing assumed at all; Proposition 27, modulo the repaired Proposition
17; and Theorem 5 modulo that and Lemma 6. Neither needs Conjecture 8 directly — the conjecture enters one level down, in Lemma 7, which
Lemma 6 uses for the β case.
