# MPSS: transitivity elimination for the machine relation over the variant

`MPSS/Transitivity` transcribed to `⊲′` (`MPSS/VariantMachine`): pushing an equivalence step
along the left of a derivation, transitivity of the single-step relation, and Theorem 3. The
diamond it spends is the proven `Lem-2′` (`MPSS/VariantDiamond`); the commutation lemma it spends
is a module parameter, `Lem-1′`, discharged by `MPSS/VariantCommutation`. Local closure of the
source term is carried because both lemmas ask for it; the well-formed chains the downstream
results use record it (`MPSS/Congruence`, `MPSS/VariantMachine`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantTransitivity where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)

open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-lc)
open import MPSS.VariantCtx
open import MPSS.VariantSub
open import MPSS.VariantMachine
open import MPSS.VariantDiamond using (Lem-2′)
```

## The commutation lemma, as the statement the rest consumes

```agda
Lem-1′-Set : Set
Lem-1′-Set = ∀ {Γ s Γ' s' t₀ t₁ t₂} → LC t₀
           → Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁
           → Γ ∣ s ⊢ t₀ ⟶ˢ′ t₂
           → Γ ∣ s ↣′ Γ' ∣ s'
           → ∃[ t₃ ] ((Γ ∣ s ⊢ t₂ ⟶ᵉ′ t₃) × (Γ' ∣ s' ⊢ t₁ ⟶ˢ′ t₃))

module _ (lem-1′ : Lem-1′-Set) where
```

## Pushing an equivalence step along the left

```agda
  push≡′ : ∀ {Γ s u u' t m} → LC u
         → Γ ∣ s ⊢ u ⟶ᵉ′ u'
         → Γ ∣ s ⊢ u ⊲′[ m ] t
         → Γ ∣ s ⊢ u' ⊲′[ m ] t
  push≡′ lu e (As-Refl′ pv)     = As-Right′ (As-Refl′ pv) e
  push≡′ lu e (As-Right′ d e₁)  = As-Right′ (push≡′ lu e d) e₁
  push≡′ lu e (As-Left-1′ st d) with lem-1′ lu e st Ct-Refl′
  ... | _ , eʳ , stʳ            = As-Left-1′ stʳ (push≡′ (⟶ˢ′-lc lu st) eʳ d)
  push≡′ lu e (As-Left-2′ e₁ d) with Lem-2′ lu e e₁ Ct-Refl′ Ct-Refl′
  ... | _ , eˡ , eʳ             = As-Left-2′ eˡ (push≡′ (⟶ᵉ′-lc lu e₁) eʳ d)
```

## Transitivity of the single-step relation

```agda
  ⊲′-trans : ∀ {Γ s v u t m} → LC u
           → Γ ∣ s ⊢ v ⊲′[ m ] u
           → Γ ∣ s ⊢ u ⊲′[ m ] t
           → Γ ∣ s ⊢ v ⊲′[ m ] t
  ⊲′-trans lu (As-Refl′ _)      d₂ = d₂
  ⊲′-trans lu (As-Left-1′ st d) d₂ = As-Left-1′ st (⊲′-trans lu d d₂)
  ⊲′-trans lu (As-Left-2′ e d)  d₂ = As-Left-2′ e (⊲′-trans lu d d₂)
  ⊲′-trans lu (As-Right′ d e)   d₂ = ⊲′-trans (⟶ᵉ′-lc lu e) d (push≡′ lu e d₂)
```

## Theorem 3, on chains with local closure recorded

```agda
  Thm-3′ : ∀ {Γ s u v m} → Γ ∣ s ⊢ u ⊲′*ᴸ[ m ] v → Γ ∣ s ⊢ u ⊲′[ m ] v
  Thm-3′ (subᴸ′ _ _ d)     = d
  Thm-3′ (trsᴸ′ d₁ lu d₂)  = ⊲′-trans lu (Thm-3′ d₁) (Thm-3′ d₂)
```

## What this establishes

`push≡′`, `⊲′-trans` and `Thm-3′`, from `Lem-2′` (proved) and `Lem-1′` (a parameter here,
proved in `MPSS/VariantCommutation`).
