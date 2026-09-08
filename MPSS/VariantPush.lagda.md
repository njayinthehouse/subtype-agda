# MPSS: relabelling and stack-monotonicity for the variant relation

`relabelᵉ′` and `pushᵉ′` are `MPSS/StackPush`'s `relabelᵉ` and `pushᵉ` for the variant `⟶ᵉ′`
(`MPSS/EmptyStackPro`), clause by clause. In `Me-Pro′` the premise is at the empty stack and is
left alone: relabelling changes the context only, and pushing changes the stack only.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantPush where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)

open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-prevalid)
open import MPSS.StackPush using (prevalid-cons; prevalid-relabelˢ; ≐-relabel)
```

## Relabelling

```agda
relabelᵉ′ : ∀ (Δ : Ctx) {Γ x t α s u v}
          → ((x , eqv , α) ∷ Γ) prevalid
          → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ᵉ′ v
          → (Δ ++ (x , eqv , α) ∷ Γ) ∣ s ⊢ u ⟶ᵉ′ v
relabelᵉ′ Δ pe (Me-Var′ pv)       = Me-Var′ (prevalid-relabelˢ Δ pe pv)
relabelᵉ′ Δ pe (Me-Top′ pv)       = Me-Top′ (prevalid-relabelˢ Δ pe pv)
relabelᵉ′ Δ pe (Me-TAp′ pv)       = Me-TAp′ (prevalid-relabelˢ Δ pe pv)
relabelᵉ′ Δ pe (Me-Pro′ pv m d)   =
  Me-Pro′ (prevalid-relabelˢ Δ pe pv) (≐-relabel Δ m) (relabelᵉ′ Δ pe d)
relabelᵉ′ Δ pe (Me-App′ d e)      = Me-App′ (relabelᵉ′ Δ pe d) (relabelᵉ′ Δ pe e)
relabelᵉ′ Δ pe (Me-Bet′ {u' = u'} L F e)    =
  Me-Bet′ {u' = u'} L (λ x∉ → relabelᵉ′ Δ pe (F x∉)) (relabelᵉ′ Δ pe e)
relabelᵉ′ Δ pe (Me-Fun′ {t = t′} {u' = u'} L d F) =
  Me-Fun′ {u' = u'} L (relabelᵉ′ Δ pe d)
          (λ {y} y∉ → relabelᵉ′ ((y , sub , t′) ∷ Δ) pe (F y∉))
relabelᵉ′ Δ pe (Me-FOp′ {α = β} {u' = u'} L d F) =
  Me-FOp′ {u' = u'} L (relabelᵉ′ Δ pe d)
          (λ {y} y∉ → relabelᵉ′ ((y , eqv , β) ∷ Δ) pe (F y∉))
```

## Stack-monotonicity

```agda
pushᵉ′ : ∀ {Γ s s′ u v}
       → Γ ∣ s ⊢ u ⟶ᵉ′ v
       → Γ ∣ (s ++ s′) prevalid
       → Γ ∣ (s ++ s′) ⊢ u ⟶ᵉ′ v
pushᵉ′ (Me-Var′ _)       pv = Me-Var′ pv
pushᵉ′ (Me-Top′ _)       pv = Me-Top′ pv
pushᵉ′ (Me-TAp′ _)       pv = Me-TAp′ pv
pushᵉ′ (Me-Pro′ _ m d)   pv = Me-Pro′ pv m d
pushᵉ′ {s = s} (Me-App′ {v = w} d e) pv =
  Me-App′ (pushᵉ′ d (Pv-Sta pv (prevalid-head-lc pv₀) (prevalid-head-fv pv₀))) e
  where
    pv₀ = ⟶ᵉ′-prevalid d
pushᵉ′ (Me-Bet′ {u' = u'} L F e)   pv = Me-Bet′ {u' = u'} L (λ x∉ → pushᵉ′ (F x∉) pv) e
pushᵉ′ {s′ = []} (Me-Fun′ L d F) pv = Me-Fun′ L d F
pushᵉ′ {Γ} {s′ = α ∷ s″} (Me-Fun′ {t = t} {u = u} {u' = u'} L d F) pv =
  Me-FOp′ {u' = u'} (L ++ dom Γ) d body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , eqv , α) ∷ Γ) ∣ s″ ⊢ (u ^ fvar x) ⟶ᵉ′ (u' ^ fvar x)
    body {x} x∉ =
      pushᵉ′ (relabelᵉ′ [] pe (F (∉-++ˡ x∉))) pv′
      where
        pe : ((x , eqv , α) ∷ Γ) prevalid
        pe = Pv-EqA (prevalid-ctx pv) (∉-++ʳ L x∉) (prevalid-head-lc pv) (prevalid-head-fv pv)
        pv′ : ((x , eqv , α) ∷ Γ) ∣ s″ prevalid
        pv′ = prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                            (prevalid-head-lc pv) (prevalid-head-fv pv)
pushᵉ′ {Γ} {s = α ∷ s₀} {s′} (Me-FOp′ {u = u} {u' = u'} L d F) pv =
  Me-FOp′ {u' = u'} (L ++ dom Γ) d body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , eqv , α) ∷ Γ) ∣ (s₀ ++ s′) ⊢ (u ^ fvar x) ⟶ᵉ′ (u' ^ fvar x)
    body {x} x∉ =
      pushᵉ′ (F (∉-++ˡ x∉))
             (prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                            (prevalid-head-lc pv) (prevalid-head-fv pv))
```

## What this establishes

`relabelᵉ′` and `pushᵉ′`: the variant relation is insensitive to the kind of a binding it never
reads, and is stack-monotone. Both are what the floating substitution lemma and the chain
congruences for the variant consume.
