# MPSS: the strip property and confluence of the original equivalence reduction

Two consequences of the mixed diamond (`MPSS/MixedDiamond`) for the original relation `⟶ᵉ` on
its own. Peeling one of two original steps into a chain of variant steps (`MPSS/Peel`) and
joining the chain against the other step link by link gives the **strip property**: two
one-step reducts are joined by *one* original step from one of them and a chain of original
steps from the other, at any reduced configuration on the chain's side. The strip property
gives confluence of `⟶ᵉ*` at a fixed configuration by the usual tiling.

Neither is the one-step diamond `Lem-2` of `MPSS/Assumed`, which stays open; they are what the
mixed diamond yields for the original relation without a reassembly of residuals.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Strip where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.CtxPrevalid using (↣-prevalid)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-lc)
open import MPSS.VariantCtx
open import MPSS.VariantChain using (_∣_⊢_⟶ᵉ′*_; ε′; _◅′_; ⁺→*)
open import MPSS.Peel using (to-chain)
open import MPSS.MixedDiamond using (Lem-2ᵐ)
```

## Chains of original steps

```agda
infixr 5 _◅_
infix 3 _∣_⊢_⟶ᵉ*_
data _∣_⊢_⟶ᵉ*_ : Ctx → Stack → Tm → Tm → Set where
  ε   : ∀ {Γ s a} → Γ ∣ s prevalid → Γ ∣ s ⊢ a ⟶ᵉ* a
  _◅_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ b → Γ ∣ s ⊢ b ⟶ᵉ* c → Γ ∣ s ⊢ a ⟶ᵉ* c

_++_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s ⊢ b ⟶ᵉ* c → Γ ∣ s ⊢ a ⟶ᵉ* c
ε _     ++ q = q
(d ◅ p) ++ q = d ◅ (p ++ q)

⟶ᵉ*-lc : ∀ {Γ s a b} → LC a → Γ ∣ s ⊢ a ⟶ᵉ* b → LC b
⟶ᵉ*-lc la (ε _)   = la
⟶ᵉ*-lc la (d ◅ p) = ⟶ᵉ*-lc (⟶ᵉ-lc la d) p
```

## A variant chain against an original step

The chain's side stays at the configuration it was derived at; the step's side may reduce.

```agda
strip′ : ∀ {Γ₀ s₀ Γ₂ s₂ a b c} → LC a
       → Γ₀ ∣ s₀ ⊢ a ⟶ᵉ′* b → Γ₀ ∣ s₀ ⊢ a ⟶ᵉ c → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
       → ∃[ m ] ((Γ₀ ∣ s₀ ⊢ b ⟶ᵉ m) × (Γ₂ ∣ s₂ ⊢ c ⟶ᵉ* m))
strip′ la (ε′ pv)   d c₂ = _ , d , ε (↣-prevalid pv c₂)
strip′ la (v ◅′ vs) d c₂ with Lem-2ᵐ la v d Ct-Refl′ c₂
... | m₁ , f₁ , f₂ with strip′ (⟶ᵉ′-lc la v) vs f₁ c₂
...   | m , g₁ , g₂ = m , g₁ , (f₂ ◅ g₂)
```

## The strip property

```agda
strip : ∀ {Γ₀ s₀ Γ₂ s₂ a b c} → LC a
      → Γ₀ ∣ s₀ ⊢ a ⟶ᵉ b → Γ₀ ∣ s₀ ⊢ a ⟶ᵉ c → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
      → ∃[ m ] ((Γ₀ ∣ s₀ ⊢ b ⟶ᵉ m) × (Γ₂ ∣ s₂ ⊢ c ⟶ᵉ* m))
strip la d₁ d₂ c₂ = strip′ la (⁺→* (to-chain la d₁)) d₂ c₂
```

## Confluence at a fixed configuration

A chain against a step is joined by one step from the chain's end; then chains against chains.

```agda
strip* : ∀ {Γ s a b c} → LC a
       → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s ⊢ a ⟶ᵉ c
       → ∃[ m ] ((Γ ∣ s ⊢ b ⟶ᵉ m) × (Γ ∣ s ⊢ c ⟶ᵉ* m))
strip* la (ε _)    d = _ , d , ε (⟶ᵉ-prevalid d)
strip* la (d₁ ◅ p) d with strip la d₁ d Ct-Refl
... | m₁ , f₁ , f₂ with strip* (⟶ᵉ-lc la d₁) p f₁
...   | m , g₁ , g₂ = m , g₁ , (f₂ ++ g₂)

confluent : ∀ {Γ s a b c} → LC a
          → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s ⊢ a ⟶ᵉ* c
          → ∃[ m ] ((Γ ∣ s ⊢ b ⟶ᵉ* m) × (Γ ∣ s ⊢ c ⟶ᵉ* m))
confluent la p (ε pv)    = _ , ε (⟶ᵉ*-prevalid′ pv p) , p
  where
    ⟶ᵉ*-prevalid′ : ∀ {Γ s a b} → Γ ∣ s prevalid → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s prevalid
    ⟶ᵉ*-prevalid′ pv _ = pv
confluent la p (d ◅ q) with strip* la p d
... | m₁ , f₁ , f₂ with confluent (⟶ᵉ-lc la d) f₂ q
...   | m , g₁ , g₂ = m , (f₁ ◅ g₁) , g₂
```

## What this establishes

`strip`: for the original equivalence reduction, two one-step reducts of a locally closed term
are joined by **one** original step from the first and a chain of original steps from the
second, the latter at any reduction of the configuration. `confluent`: `⟶ᵉ*` is confluent at
every configuration. Both are corollaries of the mixed diamond and `MPSS/Peel`.

Confluence of `⟶ᵉ*` was already available through the variant (`MPSS/VariantDiamond` with
`MPSS/Peel` and `MPSS/EmptyStackPro`, since the two closures coincide); the strip property is
what the mixed diamond adds beyond it. The one-step diamond for two original steps remains
open.
