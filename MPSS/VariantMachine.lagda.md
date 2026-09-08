# MPSS: the machine relation over the variant is the machine relation

`⊲′` is Figure 3's relation `⊲` (`MPSS/Subtyping`) with the variant reductions `⟶ˢ′` and `⟶ᵉ′`
in place of `⟶ˢ` and `⟶ᵉ`. Since `⊲` is closed under chains of steps on both sides
(`As-Left-1`, `As-Left-2`, `As-Right`), and each original step is a chain of variant steps
(`MPSS/Peel`, `MPSS/VariantSub`), the two relations coincide on locally closed terms. So any
theorem about `⊲′` — in particular transitivity elimination proved from the variant's diamond — is
a theorem about `⊲`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantMachine where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)

open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-lc)
open import MPSS.VariantChain using (_∣_⊢_⟶ᵉ′*_; ε′; _◅′_)
open import MPSS.VariantSub
open import MPSS.Peel using (⟶ᵉ⊆⟶ᵉ′*)
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
```

## The relation

```agda
infix 3 _∣_⊢_⊲′[_]_
data _∣_⊢_⊲′[_]_ : Ctx → Stack → Tm → Mode → Tm → Set where

  As-Refl′   : ∀ {Γ s t m}
             → Γ ∣ s prevalid
             → Γ ∣ s ⊢ t ⊲′[ m ] t

  As-Left-1′ : ∀ {Γ s v v' t}
             → Γ ∣ s ⊢ v ⟶ˢ′ v'
             → Γ ∣ s ⊢ v' ⊲′[ sub-m ] t
             → Γ ∣ s ⊢ v  ⊲′[ sub-m ] t

  As-Left-2′ : ∀ {Γ s v v' t}
             → Γ ∣ s ⊢ v ⟶ᵉ′ v'
             → Γ ∣ s ⊢ v' ⊲′[ eqv-m ] t
             → Γ ∣ s ⊢ v  ⊲′[ eqv-m ] t

  As-Right′  : ∀ {Γ s v t t' m}
             → Γ ∣ s ⊢ v ⊲′[ m ] t'
             → Γ ∣ s ⊢ t ⟶ᵉ′ t'
             → Γ ∣ s ⊢ v ⊲′[ m ] t
```

## Each way

A variant derivation is an original one, step by step.

```agda
⊲′⊆⊲ : ∀ {Γ s v m t} → Γ ∣ s ⊢ v ⊲′[ m ] t → Γ ∣ s ⊢ v ⊲[ m ] t
⊲′⊆⊲ (As-Refl′ pv)      = As-Refl pv
⊲′⊆⊲ (As-Left-1′ st d)  = As-Left-1 (⟶ˢ′⊆⟶ˢ st) (⊲′⊆⊲ d)
⊲′⊆⊲ (As-Left-2′ e d)   = As-Left-2 (⟶ᵉ′⊆⟶ᵉ e) (⊲′⊆⊲ d)
⊲′⊆⊲ (As-Right′ d e)    = As-Right (⊲′⊆⊲ d) (⟶ᵉ′⊆⟶ᵉ e)
```

An original derivation is a variant one, each step unfolded into its chain. Local closure of the
two endpoints is needed to unfold, and is carried along: a left step's target and a right step's
source are locally closed when its other end is.

```agda
chain-left-1 : ∀ {Γ s v v' t} → Γ ∣ s ⊢ v ⟶ˢ′* v' → Γ ∣ s ⊢ v' ⊲′[ sub-m ] t → Γ ∣ s ⊢ v ⊲′[ sub-m ] t
chain-left-1 (εˢ′ _)     d = d
chain-left-1 (st ◅ˢ′ p)  d = As-Left-1′ st (chain-left-1 p d)

chain-left-2 : ∀ {Γ s v v' t} → Γ ∣ s ⊢ v ⟶ᵉ′* v' → Γ ∣ s ⊢ v' ⊲′[ eqv-m ] t → Γ ∣ s ⊢ v ⊲′[ eqv-m ] t
chain-left-2 (ε′ _)    d = d
chain-left-2 (e ◅′ p)  d = As-Left-2′ e (chain-left-2 p d)

chain-right : ∀ {Γ s v t t' m} → Γ ∣ s ⊢ v ⊲′[ m ] t' → Γ ∣ s ⊢ t ⟶ᵉ′* t' → Γ ∣ s ⊢ v ⊲′[ m ] t
chain-right d (ε′ _)    = d
chain-right d (e ◅′ p)  = As-Right′ (chain-right d p) e

⊲⊆⊲′ : ∀ {Γ s v m t} → LC v → LC t → Γ ∣ s ⊢ v ⊲[ m ] t → Γ ∣ s ⊢ v ⊲′[ m ] t
⊲⊆⊲′ lv lt (As-Refl pv)      = As-Refl′ pv
⊲⊆⊲′ lv lt (As-Left-1 st d)  = chain-left-1 (⟶ˢ⊆⟶ˢ′* lv st) (⊲⊆⊲′ (⟶ˢ-lc lv st) lt d)
⊲⊆⊲′ lv lt (As-Left-2 e d)   = chain-left-2 (⟶ᵉ⊆⟶ᵉ′* lv e) (⊲⊆⊲′ (⟶ᵉ-lc lv e) lt d)
⊲⊆⊲′ lv lt (As-Right d e)    = chain-right (⊲⊆⊲′ lv (⟶ᵉ-lc lt e) d) (⟶ᵉ⊆⟶ᵉ′* lt e)
```

## The transitive closures

`MPSS/Congruence` records that `Ast-Trans` does not carry the local closure of the intermediate
term, and works with `⊲*ᴸ`, the closure with that information restored; the well-formed chain
`⊑*wf` supplies it. The same closure over `⊲′` transfers both ways.

```agda
infix 3 _∣_⊢_⊲′*ᴸ[_]_
data _∣_⊢_⊲′*ᴸ[_]_ (Γ : Ctx) (s : Stack) : Tm → Mode → Tm → Set where
  subᴸ′ : ∀ {a c m} → LC a → LC c → Γ ∣ s ⊢ a ⊲′[ m ] c → Γ ∣ s ⊢ a ⊲′*ᴸ[ m ] c
  trsᴸ′ : ∀ {a u c m} → Γ ∣ s ⊢ a ⊲′*ᴸ[ m ] u → LC u → Γ ∣ s ⊢ u ⊲′*ᴸ[ m ] c
        → Γ ∣ s ⊢ a ⊲′*ᴸ[ m ] c

open import MPSS.Congruence using (_∣_⊢_⊲*ᴸ[_]_; subᴸ; trsᴸ)

⊲*ᴸ⊆⊲′*ᴸ : ∀ {Γ s a m c} → Γ ∣ s ⊢ a ⊲*ᴸ[ m ] c → Γ ∣ s ⊢ a ⊲′*ᴸ[ m ] c
⊲*ᴸ⊆⊲′*ᴸ (subᴸ la lc d)   = subᴸ′ la lc (⊲⊆⊲′ la lc d)
⊲*ᴸ⊆⊲′*ᴸ (trsᴸ d₁ lu d₂) = trsᴸ′ (⊲*ᴸ⊆⊲′*ᴸ d₁) lu (⊲*ᴸ⊆⊲′*ᴸ d₂)

⊲′*ᴸ⊆⊲*ᴸ : ∀ {Γ s a m c} → Γ ∣ s ⊢ a ⊲′*ᴸ[ m ] c → Γ ∣ s ⊢ a ⊲*ᴸ[ m ] c
⊲′*ᴸ⊆⊲*ᴸ (subᴸ′ la lc d)   = subᴸ la lc (⊲′⊆⊲ d)
⊲′*ᴸ⊆⊲*ᴸ (trsᴸ′ d₁ lu d₂) = trsᴸ (⊲′*ᴸ⊆⊲*ᴸ d₁) lu (⊲′*ᴸ⊆⊲*ᴸ d₂)
```

## What this establishes

On locally closed terms, `⊲` and `⊲′` are the same relation, and so are their transitive closures
with local closure recorded. Transitivity elimination for `⊲′` — from the variant's diamond and
commutation, with the state-size measure `../PLAN.md` describes — therefore gives transitivity
elimination for `⊲` on the well-formed chains the downstream results use.
