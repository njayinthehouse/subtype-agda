# MPSS: the diamond cannot be weakened to confluence

Before looking for a cleverer proof of Lemma 2, it is worth asking for less. The natural weakening
is to let the two sides meet after *several* steps rather than one — ordinary confluence instead of
the diamond. It is the weaker statement, and it is what one normally proves.

It does not work here, and this module says why.

```agda
{-# OPTIONS --safe #-}

module MPSS.WeakDiamond where

open import Data.Product.Base using (_×_; _,_; ∃-syntax)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Congruence using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; _++ᵉ_; ⟶ᵉ*-prevalid)
```

## The weakened statement

```agda
Conf : Set
Conf = ∀ {Γ s t₀ t₁ t₂}
     → Γ ∣ s ⊢ t₀ ⟶ᵉ t₁
     → Γ ∣ s ⊢ t₀ ⟶ᵉ t₂
     → ∃[ t₃ ] ((Γ ∣ s ⊢ t₁ ⟶ᵉ* t₃) × (Γ ∣ s ⊢ t₂ ⟶ᵉ* t₃))
```

## What survives

Both places a chain has to be folded back into a subtyping derivation are fine. `As-Right` absorbs
a chain on the right, and `As-Left-2` absorbs one on the left, each by plain induction.

```agda
right* : ∀ {Γ s v a b m} → Γ ∣ s ⊢ v ⊲[ m ] b → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s ⊢ v ⊲[ m ] a
right* d (εᵉ _)   = d
right* d (e ◅ᵉ c) = As-Right (right* d c) e

left2* : ∀ {Γ s a b t} → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s ⊢ b ⊲[ eqv-m ] t → Γ ∣ s ⊢ a ⊲[ eqv-m ] t
left2* (εᵉ _)   d = d
left2* (e ◅ᵉ c) d = As-Left-2 e (left2* c d)
```

## What does not

`push≡` is the only consumer of the diamond, and its `As-Left-2` case is where the weakening has to
pay. Given `e : u ⟶≡ u′` and `As-Left-2 e₁ d`, confluence returns chains rather than steps, so the
right-hand chain has to be pushed through `d` — and pushing a *chain* means iterating `push≡`:

> `push≡ e (As-Left-2 e₁ d) with conf e e₁` — `... | _ , eˡ , eʳ = left2* eˡ (push≡* eʳ d)`
> — and the chain is consumed by
> `push≡* (εᵉ _) d = d` — `push≡* (e ◅ᵉ c) d = push≡* c (push≡ e d)`

Agda rejects it, and the rejection is not an artefact — the single-step `push≡` of
`MPSS/Transitivity` compiles, so the weakening is what breaks it:

> `Termination checking failed for the following functions: push≡, push≡*`
> — *Problematic calls* include `push≡* c (push≡ e d)`, where the chain shrinks but the derivation
> `d` being descended is replaced by `push≡ e d`.

`push≡` does not preserve the size of the derivation it transforms. At `As-Refl` it returns
`As-Right (As-Refl pv) e`, one node larger; at `As-Left-2` it prefixes one `As-Left-2` per step of
the joining chain, so the count of left-steps — the one quantity the other three cases leave
alone — grows by the chain's length. Iterating it therefore has no structural measure, and the
derivation `d` that the recursion would need to descend is exactly the one being enlarged.

Nor can the gap be closed the usual way. Newman's lemma turns weak confluence into confluence for a
*terminating* relation, and `⟶≡` is reflexive — `Me-Var` and `Me-Top` are steps — so it terminates
nowhere and Newman does not apply.

## What this establishes

Lemma 2's one-step form is not a convenience of presentation: the metatheory needs it as stated.
Confluence would not do, because `push≡` consumes joins one step at a time and grows the derivation
it is pushed through, and no termination argument recovers the difference.

This is worth knowing in both directions. It closes off the easiest-looking escape, and it explains
why the paper states a *diamond* for a reflexive simultaneous reduction rather than confluence for
a small-step one — that is the standard Tait–Martin-Löf arrangement, and the strength of the
statement is doing real work downstream.
