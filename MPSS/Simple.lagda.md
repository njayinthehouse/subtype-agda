# MPSS: the promotion steps that push and narrow verbatim

The plan's push lemma moves a promotion step taken at `Γˢ ∣ s₀` to `Γᵉ ∣ s₀ ++ s`, where
`Γˢ ▷ Γᵉ` narrows some subtype entries to equivalence entries. Every rule transfers by itself
except two: `Ms-Pro` on a narrowed variable (the entry it reads is gone), and `Ms-Fun` at a stack
that becomes non-empty (the rule no longer applies, and `Ms-FOp` binds the parameter
differently). This module isolates the rest.

Rather than a predicate on a `⟶ˢ` derivation — which cannot be case-split, since `Ms-FOp`'s
conclusion determines its body only under an opening — the simple steps are given as their own
judgement `Γˢ ∣ Γᵉ ∣ s ⊢ a ⇢ a′`, indexed by **both** contexts: the `Ms-Pro` rule demands the
entry it reads exist on both sides. It maps into `⟶ˢ` at `Γˢ` (`⇢⇒⟶ˢ`) and pushes into `⟶ˢ` at
`Γᵉ` with a deeper stack (`⇢-push`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Simple where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import MPSS.WellFormed
open import MPSS.Narrow
open import MPSS.StackPush using (pushᵉ; prevalid-cons)
```

## Simple promotion

```agda
infix 3 _∣_∣_⊢_⇢_
data _∣_∣_⊢_⇢_ : Ctx → Ctx → Stack → Tm → Tm → Set where

  s-pro : ∀ {Γˢ Γᵉ s x t}
        → Γˢ ∣ s prevalid
        → x ≤ t ∈ Γˢ
        → x ≤ t ∈ Γᵉ
        → Γˢ ∣ Γᵉ ∣ s ⊢ fvar x ⇢ t

  s-top : ∀ {Γˢ Γᵉ s u}
        → Γˢ ∣ s prevalid
        → Γˢ ∣ Γᵉ ∣ s ⊢ u ⇢ Top

  s-equ : ∀ {Γˢ Γᵉ s u v}
        → Γˢ ∣ s prevalid
        → Γˢ ∣ s ⊢ u ⟶ᵉ v
        → Γˢ ∣ Γᵉ ∣ s ⊢ u ⇢ v

  s-app : ∀ {Γˢ Γᵉ s u u′ v}
        → Γˢ ∣ Γᵉ ∣ (v ∷ s) ⊢ u ⇢ u′
        → Γˢ ∣ Γᵉ ∣ s ⊢ app u v ⇢ app u′ v

  s-fop : ∀ {Γˢ Γᵉ s α t u u′} (L : List Name)
        → (∀ {x} → x ∉ L
             → ((x , eqv , α) ∷ Γˢ) ∣ ((x , eqv , α) ∷ Γᵉ) ∣ s ⊢ (u ^ fvar x) ⇢ (u′ ^ fvar x))
        → Γˢ ∣ Γᵉ ∣ (α ∷ s) ⊢ lam t u ⇢ lam t u′
```

## A simple step is a promotion step at the left context

```agda
⇢⇒⟶ˢ : ∀ {Γˢ Γᵉ s a a′} → Γˢ ∣ Γᵉ ∣ s ⊢ a ⇢ a′ → Γˢ ∣ s ⊢ a ⟶ˢ a′
⇢⇒⟶ˢ (s-pro pv m _)         = Ms-Pro pv m
⇢⇒⟶ˢ (s-top pv)             = Ms-Top pv
⇢⇒⟶ˢ (s-equ pv e)           = Ms-Equ pv e
⇢⇒⟶ˢ (s-app d)              = Ms-App (⇢⇒⟶ˢ d)
⇢⇒⟶ˢ (s-fop {u′ = u′} L F)  = Ms-FOp {u' = u′} L (λ x∉ → ⇢⇒⟶ˢ (F x∉))
```

## And it pushes to the right context at a deeper stack

```agda
⇢-push : ∀ {Γˢ Γᵉ s₀ s a a′}
       → Γˢ ▷ Γᵉ
       → Γˢ ∣ Γᵉ ∣ s₀ ⊢ a ⇢ a′
       → Γᵉ ∣ (s₀ ++ s) prevalid
       → Γᵉ ∣ (s₀ ++ s) ⊢ a ⟶ˢ a′
⇢-push n (s-pro _ _ k)  pv = Ms-Pro pv k
⇢-push n (s-top _)      pv = Ms-Top pv
⇢-push n (s-equ _ e)    pv = Ms-Equ pv (pushᵉ (⟶ᵉ-▷ n e) pv)
⇢-push n (s-app d)      pv =
  Ms-App (⇢-push n d (Pv-Sta pv (prevalid-head-lc pv₀)
                                (λ h → subst (_ ∈_) (▷-dom n) (prevalid-head-fv pv₀ h))))
  where pv₀ = ⟶ˢ-prevalid (⇢⇒⟶ˢ d)
⇢-push {Γᵉ = Γᵉ} {s = s} n (s-fop {s = s₀} {α = α} {u = u} {u′ = u′} L F) pv =
  Ms-FOp {u' = u′} (L ++ dom Γᵉ) body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γᵉ)
         → ((x , eqv , α) ∷ Γᵉ) ∣ (s₀ ++ s) ⊢ (u ^ fvar x) ⟶ˢ (u′ ^ fvar x)
    body {x} x∉ =
      ⇢-push (n-keep n) (F (∉-++ˡ x∉))
             (prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                            (prevalid-head-lc pv) (prevalid-head-fv pv))
```

## What this establishes

The judgement `⇢` of promotion steps that avoid the two hard cases, with both directions: it is
a promotion step at the unnarrowed context (`⇢⇒⟶ˢ`), and it pushes to the narrowed context at
any deeper stack (`⇢-push`). Together with `Right-push` in `MPSS/Frame` for equivalence runs,
this is the stack-insensitive half of the push lemma; what the plan's recursion must still handle
is `Ms-Pro` on a narrowed variable and `Ms-Fun`.
