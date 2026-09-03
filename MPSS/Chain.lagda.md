# MPSS: well-subtyping at a stack

The Conjecture 8 plan (`../PLAN.md`, third pass) restates the conjecture over a stack, so that
its application case disappears: `Co[u] v` at stack `s` is `Co[u]` at stack `v :: s`. For that,
well-subtyping has to be available *at a stack*. This module defines it and relates it to v2's
stack-free judgements of Figure 4.

A term applied to a stack:

> `a · nil = a`, `a · (v :: s) = (a v) · s`

A chain at stack `s` is exactly a `≤wf` derivation whose steps are taken at `s` rather than at
`nil`, and whose well-formedness side conditions are about the *applied* terms `a · s`. At the
empty stack it is `≤wf` itself. The point of the definition is the lemma `◁-app` below: a chain
at `v :: s` **is** a chain of the applications at `s`, by `Ms-App`/`Me-App` — which is the
application congruence that is hard for the stack-free relation, obtained here by construction.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Chain where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.StackPush using (⟶ᵉ-refl)
```

## Applying a term to a stack

```agda
infixl 7 _·_
_·_ : Tm → Stack → Tm
a · []      = a
a · (v ∷ s) = app a v · s
```

## Lifting a step through the stack

A step at stack `s` is a step of the applied term at the empty stack. For `⟶ᵉ`, `Me-App` needs the
operand to reduce, and it reduces to itself because prevalidity scopes it.

```agda
liftˢ : ∀ {Γ s a a′} → Γ ∣ s ⊢ a ⟶ˢ a′ → Γ ∣ [] ⊢ a · s ⟶ˢ a′ · s
liftˢ {s = []}    d = d
liftˢ {s = v ∷ s} d = liftˢ {s = s} (Ms-App d)

liftᵉ : ∀ {Γ s a a′} → Γ ∣ s ⊢ a ⟶ᵉ a′ → Γ ∣ [] ⊢ a · s ⟶ᵉ a′ · s
liftᵉ {s = []}    d = d
liftᵉ {s = v ∷ s} d =
  liftᵉ {s = s} (Me-App d (⟶ᵉ-refl (prevalid-nil pv) (prevalid-head-lc pv) (prevalid-head-fv pv)))
  where
    pv = ⟶ᵉ-prevalid d
```

## Chains at a stack

The rules are Figure 4's `Ws-*`, with the reductions at `s` and the well-formedness premises on
the applied terms.

```agda
infix 3 _∣_⊢_◁_ _∣_⊢_◁*_

data _∣_⊢_◁_ : Ctx → Stack → Tm → Tm → Set where

  c-refl : ∀ {Γ s a}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢ a ◁ a

  c-lf1  : ∀ {Γ s a a′ c}
         → Γ ∣ s ⊢ a ⟶ᵉ a′
         → Γ ∣ s ⊢ a′ ◁ c
         → Γ ∣ s ⊢ a ◁ c

  c-lf2  : ∀ {Γ s a a′ c}
         → Γ ⊢ a · s wf
         → Γ ∣ s ⊢ a ⟶ˢ a′
         → Γ ⊢ a′ · s wf
         → Γ ∣ s ⊢ a′ ◁ c
         → Γ ∣ s ⊢ a ◁ c

  c-rgh  : ∀ {Γ s a c c′}
         → Γ ∣ s ⊢ a ◁ c′
         → Γ ∣ s ⊢ c ⟶ᵉ c′
         → Γ ∣ s ⊢ a ◁ c

data _∣_⊢_◁*_ : Ctx → Stack → Tm → Tm → Set where

  c-sub : ∀ {Γ s a c}
        → Γ ⊢ a · s wf
        → Γ ∣ s ⊢ a ◁ c
        → Γ ⊢ c · s wf
        → Γ ∣ s ⊢ a ◁* c

  c-trs : ∀ {Γ s a b c}
        → Γ ∣ s ⊢ a ◁* b
        → Γ ⊢ b · s wf
        → Γ ∣ s ⊢ b ◁* c
        → Γ ∣ s ⊢ a ◁* c
```

## At the empty stack, this is `≤wf`

Both directions are immediate, since `a · nil = a`.

```agda
≤wf⇒◁ : ∀ {Γ a c} → Γ ⊢ a ≤wf c → Γ ∣ [] ⊢ a ◁ c
≤wf⇒◁ (Ws-Rfl pv)         = c-refl (Pv-Nil pv)
≤wf⇒◁ (Ws-Lf1 e d)        = c-lf1 e (≤wf⇒◁ d)
≤wf⇒◁ (Ws-Lf2 w st w′ d)  = c-lf2 w st w′ (≤wf⇒◁ d)
≤wf⇒◁ (Ws-Rgh d e)        = c-rgh (≤wf⇒◁ d) e

≤*wf⇒◁* : ∀ {Γ a c} → Γ ⊢ a ≤*wf c → Γ ∣ [] ⊢ a ◁* c
≤*wf⇒◁* (Ws-Sub w d w′)   = c-sub w (≤wf⇒◁ d) w′
≤*wf⇒◁* (Ws-Trs d₁ w d₂)  = c-trs (≤*wf⇒◁* d₁) w (≤*wf⇒◁* d₂)
```

## A chain at any stack is well-subtyping of the applied terms

```agda
◁⇒≤wf : ∀ {Γ s a c} → Γ ∣ s ⊢ a ◁ c → Γ ⊢ a · s ≤wf c · s
◁⇒≤wf (c-refl pv)         = Ws-Rfl (prevalid-ctx pv)
◁⇒≤wf (c-lf1 e d)         = Ws-Lf1 (liftᵉ e) (◁⇒≤wf d)
◁⇒≤wf (c-lf2 w st w′ d)   = Ws-Lf2 w (liftˢ st) w′ (◁⇒≤wf d)
◁⇒≤wf (c-rgh d e)         = Ws-Rgh (◁⇒≤wf d) (liftᵉ e)

◁*⇒≤*wf : ∀ {Γ s a c} → Γ ∣ s ⊢ a ◁* c → Γ ⊢ a · s ≤*wf c · s
◁*⇒≤*wf (c-sub w d w′)    = Ws-Sub w (◁⇒≤wf d) w′
◁*⇒≤*wf (c-trs d₁ w d₂)   = Ws-Trs (◁*⇒≤*wf d₁) w (◁*⇒≤*wf d₂)
```

## The application congruence, by construction

A chain at `v :: s` is a chain of the applications at `s`. Every step transfers by `Ms-App` or
`Me-App`, and the side conditions are literally the same terms, since `(a v) · s = a · (v :: s)`.

```agda
◁-app : ∀ {Γ s v a c} → Γ ∣ (v ∷ s) ⊢ a ◁ c → Γ ∣ s ⊢ app a v ◁ app c v
◁-app (c-refl pv)         = c-refl (prevalid-pop pv)
◁-app (c-lf1 e d)         = c-lf1 (Me-App e (⟶ᵉ-refl (prevalid-nil pv) (prevalid-head-lc pv)
                                                        (prevalid-head-fv pv)))
                                  (◁-app d)
  where pv = ⟶ᵉ-prevalid e
◁-app (c-lf2 w st w′ d)   = c-lf2 w (Ms-App st) w′ (◁-app d)
◁-app (c-rgh d e)         = c-rgh (◁-app d)
                                  (Me-App e (⟶ᵉ-refl (prevalid-nil pv) (prevalid-head-lc pv)
                                                      (prevalid-head-fv pv)))
  where pv = ⟶ᵉ-prevalid e

◁*-app : ∀ {Γ s v a c} → Γ ∣ (v ∷ s) ⊢ a ◁* c → Γ ∣ s ⊢ app a v ◁* app c v
◁*-app (c-sub w d w′)     = c-sub w (◁-app d) w′
◁*-app (c-trs d₁ w d₂)    = c-trs (◁*-app d₁) w (◁*-app d₂)
```

## Concatenation, and the prevalidity a chain carries

```agda
◁-prevalid : ∀ {Γ s a c} → Γ ∣ s ⊢ a ◁ c → Γ ∣ s prevalid
◁-prevalid (c-refl pv)        = pv
◁-prevalid (c-lf1 e _)        = ⟶ᵉ-prevalid e
◁-prevalid (c-lf2 _ st _ _)   = ⟶ˢ-prevalid st
◁-prevalid (c-rgh d _)        = ◁-prevalid d

◁*-prevalid : ∀ {Γ s a c} → Γ ∣ s ⊢ a ◁* c → Γ ∣ s prevalid
◁*-prevalid (c-sub _ d _)     = ◁-prevalid d
◁*-prevalid (c-trs d _ _)     = ◁*-prevalid d
```

Prepending steps to a single-layer chain, and the unit chains.

```agda
◁-lf1* : ∀ {Γ s a a′ c} → Γ ∣ s ⊢ a ⟶ᵉ a′ → Γ ∣ s ⊢ a′ ◁ c → Γ ∣ s ⊢ a ◁ c
◁-lf1* = c-lf1

step-◁* : ∀ {Γ s a a′}
        → Γ ⊢ a · s wf → Γ ∣ s ⊢ a ⟶ˢ a′ → Γ ⊢ a′ · s wf
        → Γ ∣ s ⊢ a ◁* a′
step-◁* w st w′ = c-sub w (c-lf2 w st w′ (c-refl (⟶ˢ-prevalid st))) w′

estep-◁* : ∀ {Γ s a a′}
         → Γ ⊢ a · s wf → Γ ∣ s ⊢ a ⟶ᵉ a′ → Γ ⊢ a′ · s wf
         → Γ ∣ s ⊢ a ◁* a′
estep-◁* w e w′ = c-sub w (c-lf1 e (c-refl (⟶ᵉ-prevalid e))) w′

rstep-◁* : ∀ {Γ s a a′}
         → Γ ⊢ a · s wf → Γ ∣ s ⊢ a′ ⟶ᵉ a → Γ ⊢ a′ · s wf
         → Γ ∣ s ⊢ a ◁* a′
rstep-◁* w e w′ = c-sub w (c-rgh (c-refl (⟶ᵉ-prevalid e)) e) w′
```

## What this establishes

- `_·_`, `liftˢ`, `liftᵉ`: applying a term to a stack, and a step at a stack is a step of the
  applied term at `nil`.
- `◁`, `◁*`: Figure 4's well-subtyping at a stack. At `nil` they are `≤wf`/`≤*wf` (`≤wf⇒◁`,
  `≤*wf⇒◁*`), and at any stack they yield `≤wf`/`≤*wf` of the applied terms (`◁⇒≤wf`,
  `◁*⇒≤*wf`).
- `◁-app`, `◁*-app`: **the application congruence at the level of chains is definitional.** This
  is why the plan restates Conjecture 8 at a stack: what remains is to *produce* a chain at a
  stack from a derivation at `nil`, which is the push lemma, and to wrap chains under binders.
