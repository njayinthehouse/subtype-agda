# MPSS: local closure for both reductions

Prerequisites for everything in v2's §3 and §4: both reductions preserve local closure, and the
bound looked up by `Ms-Pro` or `Me-Pro` is itself locally closed.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Scope where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.Reduction
open import PSS.Syntax using (open-lc; subst-lc)
```

## Local closure is preserved

`Me-Pro` and `Ms-Pro` both replace a variable by a context bound, so both need the bound to be
locally closed — which prevalidity supplies.

```agda
⟶ᵉ-lc : ∀ {Γ s u v} → LC u → Γ ∣ s ⊢ u ⟶ᵉ v → LC v
⟶ᵉ-lc lu (Me-Var _)        = lc-fvar
⟶ᵉ-lc lu (Me-Top _)        = lc-Top
⟶ᵉ-lc lu (Me-TAp _)        = lc-Top
⟶ᵉ-lc lu (Me-Pro pv m d)   =
  ⟶ᵉ-lc (prevalid-bound-lc (prevalid-ctx pv) m) d
⟶ᵉ-lc (lc-app lu lv) (Me-App d e) = lc-· (⟶ᵉ-lc lu d) (⟶ᵉ-lc lv e)
  where lc-· = lc-app
⟶ᵉ-lc (lc-lam L₀ lt F₀) (Me-Fun L d F) =
  lc-lam (L₀ ++ L) (⟶ᵉ-lc lt d)
         (λ x∉ → ⟶ᵉ-lc (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
⟶ᵉ-lc (lc-lam L₀ lt F₀) (Me-FOp L d F) =
  lc-lam (L₀ ++ L) (⟶ᵉ-lc lt d)
         (λ x∉ → ⟶ᵉ-lc (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
⟶ᵉ-lc (lc-app (lc-lam L₀ lt F₀) lv) (Me-Bet {t = t} {u' = u'} L F e) =
  open-lc {t} {u'} lam-u' (⟶ᵉ-lc lv e)
  where
    lam-u' : LC (lam t u')
    lam-u' = lc-lam (L ++ L₀) lt
                    (λ {x} x∉ → ⟶ᵉ-lc (F₀ (∉-++ʳ L x∉)) (F (∉-++ˡ x∉)))

⟶ˢ-lc : ∀ {Γ s u v} → LC u → Γ ∣ s ⊢ u ⟶ˢ v → LC v
⟶ˢ-lc lu (Ms-Pro pv m)  = prevalid-bound-lc (prevalid-ctx pv) m
⟶ˢ-lc lu (Ms-Top _)     = lc-Top
⟶ˢ-lc lu (Ms-Equ _ e)   = ⟶ᵉ-lc lu e
⟶ˢ-lc (lc-app lu lv) (Ms-App d) = lc-app (⟶ˢ-lc lu d) lv
⟶ˢ-lc (lc-lam L₀ lt F₀) (Ms-Fun L F) =
  lc-lam (L₀ ++ L) lt (λ x∉ → ⟶ˢ-lc (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
⟶ˢ-lc (lc-lam L₀ lt F₀) (Ms-FOp L F) =
  lc-lam (L₀ ++ L) lt (λ x∉ → ⟶ˢ-lc (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
```

## What this establishes

Local closure is preserved by both of v2's reductions. `Me-Pro` and `Ms-Pro` are the cases that
need prevalidity, since they replace a variable by a context bound; `Me-Bet` is the case that
needs `open-lc`, as in v1.

**Owed.** Reflexivity of `⟶ᵉ` (v1's Lemma 2.2 analogue) does *not* follow from local closure
alone here, unlike in v1. `Me-App` pushes the operand onto the stack, so `Pv-Sta` demands the
operand be scoped in the context — reflexivity therefore needs `fv t ⊑ dom Γ` as a premise, and
with it a free-variable-under-opening lemma for the binder cases. That is a consequence of
`Me-App` being stack-aware where v1's `Cr-App` was not, and is recorded rather than assumed.
