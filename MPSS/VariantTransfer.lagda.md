# MPSS: Theorem 3 for the machine relation, unconditionally

Transitivity elimination for `⊲` on chains with local closure recorded, with nothing assumed:
`MPSS/VariantCommutation` supplies Lemma 1′, `MPSS/VariantTransitivity` turns it and the proven
diamond `Lem-2′` into Theorem 3 for `⊲′`, and `MPSS/VariantMachine` carries the result across to
`⊲`, which is the same relation on locally closed terms.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantTransfer where

open import MPSS.WellFormed
open import MPSS.VariantMachine
open import MPSS.VariantCommutation using (Lem-1′)
open import MPSS.VariantTransitivity
open import MPSS.Congruence using (_∣_⊢_⊲*ᴸ[_]_)
```

## Theorem 3 for `⊲′`, with its hypothesis discharged

```agda
Thm-3′-unconditional : ∀ {Γ s u v m} → Γ ∣ s ⊢ u ⊲′*ᴸ[ m ] v → Γ ∣ s ⊢ u ⊲′[ m ] v
Thm-3′-unconditional = Thm-3′ Lem-1′
```

## Theorem 3 for `⊲`

```agda
Thm-3ᴸ : ∀ {Γ s u v m} → Γ ∣ s ⊢ u ⊲*ᴸ[ m ] v → Γ ∣ s ⊢ u ⊲[ m ] v
Thm-3ᴸ d = ⊲′⊆⊲ (Thm-3′-unconditional (⊲*ᴸ⊆⊲′*ᴸ d))
```

## What this establishes

`Thm-3ᴸ`: **transitivity elimination for MPSS's machine relation**, on the transitive closure
that records local closure of the intermediate terms — the closure `MPSS/Congruence` and the
downstream results use — proved from the variant's diamond and commutation, with no assumption.
This is v2's Theorem 3 in the form the development consumes; `Lem-1` and `Lem-2` of
`MPSS/Assumed` are no longer needed for it.
