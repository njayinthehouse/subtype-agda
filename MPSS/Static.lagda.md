# MPSS: the static-side propositions

v2's Propositions 12, 13 and 14 and Lemmas 15 and 16 — the results relating the well-formed
judgements of Figure 4 to the bare subtyping of Figure 3, and the two facts about
well-equivalence that the β case of preservation uses. None needs substitution or commutation,
so they come first.

> **Proposition 12 (Well-formedness extraction).** If `Γ ⊢ u ≤*wf v` then both `Γ ⊢ u wf` and
> `Γ ⊢ v wf`.
>
> **Proposition 13 (From well-subtyping to subtyping).** If `Γ ⊢ u ≤wf v` then `Γ; nil ⊢ u ≤ v`.
>
> **Proposition 14 (From well-equivalence to equivalence).** If `Γ ⊢ u ≡wf v` then
> `Γ; nil ⊢ u ≡ v`.
>
> **Lemma 15.** If `Γ ⊢ u ≡wf v` then `Γ ⊢ v ≡wf u`.
>
> **Lemma 16.** If `Γ ⊢ u ≡wf v` then `Γ ⊢ u ≤wf v`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Static where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
```

## Well-equivalence

The paper writes `≡wf` for the equivalence reading of the mode-indexed relation.

```agda
infix 3 _⊢_≋wf_

_⊢_≋wf_ : Ctx → Tm → Tm → Set
Γ ⊢ u ≋wf t = Γ ⊢ u ⊑wf[ eqv-m ] t
```

## Proposition 12

The left half is `⊑*wf⇒wfˡ` in `MPSS/WellFormed`; the right half is its mirror.

```agda
⊑*wf⇒wfʳ : ∀ {Γ u m t} → Γ ⊢ u ⊑*wf[ m ] t → Γ ⊢ t wf
⊑*wf⇒wfʳ (Ws-Sub _ _ w) = w
⊑*wf⇒wfʳ (Ws-Trs _ _ d) = ⊑*wf⇒wfʳ d

Prop-12 : ∀ {Γ u m t} → Γ ⊢ u ⊑*wf[ m ] t → (Γ ⊢ u wf) × (Γ ⊢ t wf)
Prop-12 d = ⊑*wf⇒wfˡ d , ⊑*wf⇒wfʳ d
```

## Propositions 13 and 14

Forgetting the well-formedness premises turns a well-subtyping derivation into a subtyping one
at the empty stack. The only rule that is not literally the corresponding one is the left step in
the subtyping reading: `Ws-Lf1` takes an equivalence step where `As-Left-1` demands a promotion,
and `Ms-Equ` bridges them.

```agda
⊑wf⇒⊲ : ∀ {Γ u m t} → Γ ⊢ u ⊑wf[ m ] t → Γ ∣ [] ⊢ u ⊲[ m ] t
⊑wf⇒⊲ (Ws-Rfl pv)                    = As-Refl (Pv-Nil pv)
⊑wf⇒⊲ {m = sub-m} (Ws-Lf1 e d)       = As-Left-1 (Ms-Equ (⟶ᵉ-prevalid e) e) (⊑wf⇒⊲ d)
⊑wf⇒⊲ {m = eqv-m} (Ws-Lf1 e d)       = As-Left-2 e (⊑wf⇒⊲ d)
⊑wf⇒⊲ (Ws-Lf2 _ st _ d)              = As-Left-1 st (⊑wf⇒⊲ d)
⊑wf⇒⊲ (Ws-Rgh d e)                   = As-Right (⊑wf⇒⊲ d) e

Prop-13 : ∀ {Γ u t} → Γ ⊢ u ≤wf t → Γ ∣ [] ⊢ u ≤ t
Prop-13 = ⊑wf⇒⊲

Prop-14 : ∀ {Γ u t} → Γ ⊢ u ≋wf t → Γ ∣ [] ⊢ u ≋ t
Prop-14 = ⊑wf⇒⊲
```

The transitive closure transfers likewise.

```agda
⊑*wf⇒⊲* : ∀ {Γ u m t} → Γ ⊢ u ⊑*wf[ m ] t → Γ ∣ [] ⊢ u ⊲*[ m ] t
⊑*wf⇒⊲* (Ws-Sub _ d _)   = Ast-Sub (⊑wf⇒⊲ d)
⊑*wf⇒⊲* (Ws-Trs d₁ _ d₂) = Ast-Trans (⊑*wf⇒⊲* d₁) (⊑*wf⇒⊲* d₂)
```

## Lemma 15

Well-equivalence is symmetric, and the proof is a swap of the two one-sided rules: a step on the
left becomes a step on the right and conversely. `Ws-Lf2` cannot occur, since it is available
only in the subtyping reading.

```agda
Lem-15 : ∀ {Γ u t} → Γ ⊢ u ≋wf t → Γ ⊢ t ≋wf u
Lem-15 (Ws-Rfl pv)    = Ws-Rfl pv
Lem-15 (Ws-Lf1 e d)   = Ws-Rgh (Lem-15 d) e
Lem-15 (Ws-Rgh d e)   = Ws-Lf1 e (Lem-15 d)
```

## Lemma 16

Well-equivalence is contained in well-subtyping. Every rule of the equivalence reading is
available in the subtyping reading at the same premises.

```agda
Lem-16 : ∀ {Γ u t} → Γ ⊢ u ≋wf t → Γ ⊢ u ≤wf t
Lem-16 (Ws-Rfl pv)    = Ws-Rfl pv
Lem-16 (Ws-Lf1 e d)   = Ws-Lf1 e (Lem-16 d)
Lem-16 (Ws-Rgh d e)   = Ws-Rgh (Lem-16 d) e
```

Their transitive versions, which is how the β case of Lemma 6 consumes them: from
`Γ ⊢ t ≋wf z` it gets `Γ ⊢ z ≤*wf t`, given both terms well-formed.

```agda
Lem-15* : ∀ {Γ u t} → Γ ⊢ u ⊑*wf[ eqv-m ] t → Γ ⊢ t ⊑*wf[ eqv-m ] u
Lem-15* (Ws-Sub w d w′)   = Ws-Sub w′ (Lem-15 d) w
Lem-15* (Ws-Trs d₁ w d₂)  = Ws-Trs (Lem-15* d₂) w (Lem-15* d₁)

Lem-16* : ∀ {Γ u t} → Γ ⊢ u ⊑*wf[ eqv-m ] t → Γ ⊢ u ≤*wf t
Lem-16* (Ws-Sub w d w′)   = Ws-Sub w (Lem-16 d) w′
Lem-16* (Ws-Trs d₁ w d₂)  = Ws-Trs (Lem-16* d₁) w (Lem-16* d₂)
```

## What this establishes

Propositions 12, 13 and 14, and Lemmas 15 and 16, together with the transitive forms of the last
two. `Prop-13` and `Prop-14` are the bridge from Figure 4's static system to Figure 3's subtyping,
which is what lets the inversion lemma be proved by transitivity elimination on the bare
relation; `Lem-15*` and `Lem-16*` turn the inversion lemma's conclusion `t ≡wf z` into the
`z ≤*wf t` that substitution needs.
