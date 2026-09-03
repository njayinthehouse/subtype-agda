# MPSS: chains with an external side condition

`MPSS/Chain` states well-subtyping at a stack with side conditions `Γ ⊢ a · s wf` on the applied
term. Inside a binder that is the wrong condition: when a chain for the body of `λx≤w.b` at stack
`α :: s′` is built under `x ≡ α`, what the outer `≤*wf` derivation will need is well-formedness of
the *wrapped* term `(λx≤w.b) · (α :: s′)` in the outer context, not of `b · s′` under `x ≡ α` —
and the two are not inter-derivable without inverting well-formedness through a β-step.

So the side condition is made a parameter. A chain `Γ ∣ s ⊢[ P ] a ◁ c` has honest reduction
steps at the inner extended context `Γ ∣ s`, and its well-formedness premises are `P a` for an
arbitrary predicate `P` on inner terms. Wrapping a chain moves `P` along: under an application
`P` becomes `P ∘ (_ v)`, under a binder it becomes `P ∘ (λx≤w. close x _)`. At the top, `P` is
`Γ ⊢ _ wf` at the empty stack, and the chain is a `≤*wf` derivation.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Frame where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.StackPush using (⟶ᵉ-refl; pushᵉ)
```

## The chains

The extended context and the side condition are parameters: every step of a chain is taken at
the same `Γ ∣ s`.

```agda
infix 3 _∣_⊢[_]_◁_ _∣_⊢[_]_◁*_

data _∣_⊢[_]_◁_ (Γ : Ctx) (s : Stack) (P : Tm → Set) : Tm → Tm → Set where

  c-refl : ∀ {a}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢[ P ] a ◁ a

  c-lf1  : ∀ {a a′ c}
         → Γ ∣ s ⊢ a ⟶ᵉ a′
         → Γ ∣ s ⊢[ P ] a′ ◁ c
         → Γ ∣ s ⊢[ P ] a ◁ c

  c-lf2  : ∀ {a a′ c}
         → P a
         → Γ ∣ s ⊢ a ⟶ˢ a′
         → P a′
         → Γ ∣ s ⊢[ P ] a′ ◁ c
         → Γ ∣ s ⊢[ P ] a ◁ c

  c-rgh  : ∀ {a c c′}
         → Γ ∣ s ⊢[ P ] a ◁ c′
         → Γ ∣ s ⊢ c ⟶ᵉ c′
         → Γ ∣ s ⊢[ P ] a ◁ c

data _∣_⊢[_]_◁*_ (Γ : Ctx) (s : Stack) (P : Tm → Set) : Tm → Tm → Set where

  c-sub : ∀ {a c}
        → P a
        → Γ ∣ s ⊢[ P ] a ◁ c
        → P c
        → Γ ∣ s ⊢[ P ] a ◁* c

  c-trs : ∀ {a b c}
        → Γ ∣ s ⊢[ P ] a ◁* b
        → P b
        → Γ ∣ s ⊢[ P ] b ◁* c
        → Γ ∣ s ⊢[ P ] a ◁* c
```

## At the top these are Figure 4's judgements

```agda
Wf : Ctx → Tm → Set
Wf Γ a = Γ ⊢ a wf

≤wf⇒◁ : ∀ {Γ a c} → Γ ⊢ a ≤wf c → Γ ∣ [] ⊢[ Wf Γ ] a ◁ c
≤wf⇒◁ (Ws-Rfl pv)         = c-refl (Pv-Nil pv)
≤wf⇒◁ (Ws-Lf1 e d)        = c-lf1 e (≤wf⇒◁ d)
≤wf⇒◁ (Ws-Lf2 w st w′ d)  = c-lf2 w st w′ (≤wf⇒◁ d)
≤wf⇒◁ (Ws-Rgh d e)        = c-rgh (≤wf⇒◁ d) e

≤*wf⇒◁* : ∀ {Γ a c} → Γ ⊢ a ≤*wf c → Γ ∣ [] ⊢[ Wf Γ ] a ◁* c
≤*wf⇒◁* (Ws-Sub w d w′)   = c-sub w (≤wf⇒◁ d) w′
≤*wf⇒◁* (Ws-Trs d₁ w d₂)  = c-trs (≤*wf⇒◁* d₁) w (≤*wf⇒◁* d₂)

◁⇒≤wf : ∀ {Γ a c} → Γ ∣ [] ⊢[ Wf Γ ] a ◁ c → Γ ⊢ a ≤wf c
◁⇒≤wf (c-refl pv)         = Ws-Rfl (prevalid-ctx pv)
◁⇒≤wf (c-lf1 e d)         = Ws-Lf1 e (◁⇒≤wf d)
◁⇒≤wf (c-lf2 w st w′ d)   = Ws-Lf2 w st w′ (◁⇒≤wf d)
◁⇒≤wf (c-rgh d e)         = Ws-Rgh (◁⇒≤wf d) e

◁*⇒≤*wf : ∀ {Γ a c} → Γ ∣ [] ⊢[ Wf Γ ] a ◁* c → Γ ⊢ a ≤*wf c
◁*⇒≤*wf (c-sub w d w′)    = Ws-Sub w (◁⇒≤wf d) w′
◁*⇒≤*wf (c-trs d₁ w d₂)   = Ws-Trs (◁*⇒≤*wf d₁) w (◁*⇒≤*wf d₂)
```

## Changing the side condition

```agda
◁-mono : ∀ {Γ s P Q a c} → (∀ {z} → P z → Q z) → Γ ∣ s ⊢[ P ] a ◁ c → Γ ∣ s ⊢[ Q ] a ◁ c
◁-mono f (c-refl pv)        = c-refl pv
◁-mono f (c-lf1 e d)        = c-lf1 e (◁-mono f d)
◁-mono f (c-lf2 p st p′ d)  = c-lf2 (f p) st (f p′) (◁-mono f d)
◁-mono f (c-rgh d e)        = c-rgh (◁-mono f d) e

◁*-mono : ∀ {Γ s P Q a c} → (∀ {z} → P z → Q z) → Γ ∣ s ⊢[ P ] a ◁* c → Γ ∣ s ⊢[ Q ] a ◁* c
◁*-mono f (c-sub p d p′)    = c-sub (f p) (◁-mono f d) (f p′)
◁*-mono f (c-trs d₁ p d₂)   = c-trs (◁*-mono f d₁) (f p) (◁*-mono f d₂)
```

## Wrapping under an application

A chain at `v :: s` with side condition `P ∘ (_ v)` is a chain of the applications at `s` with
side condition `P`. The steps transfer by `Ms-App`/`Me-App`; the side conditions are literally
the same.

```agda
App : (Tm → Set) → Tm → Tm → Set
App P v z = P (app z v)

◁-app : ∀ {Γ s P v a c} → Γ ∣ (v ∷ s) ⊢[ App P v ] a ◁ c → Γ ∣ s ⊢[ P ] app a v ◁ app c v
◁-app (c-refl pv)         = c-refl (prevalid-pop pv)
◁-app (c-lf1 e d)         =
  c-lf1 (Me-App e (⟶ᵉ-refl (prevalid-nil pv) (prevalid-head-lc pv) (prevalid-head-fv pv)))
        (◁-app d)
  where pv = ⟶ᵉ-prevalid e
◁-app (c-lf2 p st p′ d)   = c-lf2 p (Ms-App st) p′ (◁-app d)
◁-app (c-rgh d e)         =
  c-rgh (◁-app d)
        (Me-App e (⟶ᵉ-refl (prevalid-nil pv) (prevalid-head-lc pv) (prevalid-head-fv pv)))
  where pv = ⟶ᵉ-prevalid e

◁*-app : ∀ {Γ s P v a c} → Γ ∣ (v ∷ s) ⊢[ App P v ] a ◁* c → Γ ∣ s ⊢[ P ] app a v ◁* app c v
◁*-app (c-sub p d p′)     = c-sub p (◁-app d) p′
◁*-app (c-trs d₁ p d₂)    = c-trs (◁*-app d₁) p (◁*-app d₂)
```

## Prepending equivalence steps, and unit chains

Prepending a `⟶ᵉ` step to a transitive chain needs **no** side condition for the term it steps
to: the step joins the first block.

```agda
◁*-lf1 : ∀ {Γ s P a a′ c} → Γ ∣ s ⊢ a ⟶ᵉ a′ → Γ ∣ s ⊢[ P ] a′ ◁* c → P a → Γ ∣ s ⊢[ P ] a ◁* c
◁*-lf1 e (c-sub _ d p′) p    = c-sub p (c-lf1 e d) p′
◁*-lf1 e (c-trs d₁ q d₂) p   = c-trs (◁*-lf1 e d₁ p) q d₂

◁*-rgh : ∀ {Γ s P a c c′} → Γ ∣ s ⊢[ P ] a ◁* c′ → Γ ∣ s ⊢ c ⟶ᵉ c′ → P c → Γ ∣ s ⊢[ P ] a ◁* c
◁*-rgh (c-sub p d _) e q     = c-sub p (c-rgh d e) q
◁*-rgh (c-trs d₁ r d₂) e q   = c-trs d₁ r (◁*-rgh d₂ e q)

step-◁* : ∀ {Γ s P a a′} → P a → Γ ∣ s ⊢ a ⟶ˢ a′ → P a′ → Γ ∣ s ⊢[ P ] a ◁* a′
step-◁* p st p′ = c-sub p (c-lf2 p st p′ (c-refl (⟶ˢ-prevalid st))) p′

estep-◁* : ∀ {Γ s P a a′} → P a → Γ ∣ s ⊢ a ⟶ᵉ a′ → P a′ → Γ ∣ s ⊢[ P ] a ◁* a′
estep-◁* p e p′ = c-sub p (c-lf1 e (c-refl (⟶ᵉ-prevalid e))) p′

◁-prevalid : ∀ {Γ s P a c} → Γ ∣ s ⊢[ P ] a ◁ c → Γ ∣ s prevalid
◁-prevalid (c-refl pv)       = pv
◁-prevalid (c-lf1 e _)       = ⟶ᵉ-prevalid e
◁-prevalid (c-lf2 _ st _ _)  = ⟶ˢ-prevalid st
◁-prevalid (c-rgh d _)       = ◁-prevalid d

◁*-prevalid : ∀ {Γ s P a c} → Γ ∣ s ⊢[ P ] a ◁* c → Γ ∣ s prevalid
◁*-prevalid (c-sub _ d _) = ◁-prevalid d
◁*-prevalid (c-trs d _ _) = ◁*-prevalid d
```

## Normal form of a single-layer chain

A single-layer chain is a run of left steps followed by a run of right steps. Splitting it that
way is what the push lemma consumes: right steps are pushed by `pushᵉ` and need no side
condition, left steps are pushed one at a time.

```agda
data Left (Γ : Ctx) (s : Stack) (P : Tm → Set) : Tm → Tm → Set where
  l-nil : ∀ {a} → Γ ∣ s prevalid → Left Γ s P a a
  l-eqv : ∀ {a a′ z} → Γ ∣ s ⊢ a ⟶ᵉ a′ → Left Γ s P a′ z → Left Γ s P a z
  l-sub : ∀ {a a′ z} → P a → Γ ∣ s ⊢ a ⟶ˢ a′ → P a′ → Left Γ s P a′ z → Left Γ s P a z

data Right (Γ : Ctx) (s : Stack) : Tm → Tm → Set where
  r-nil  : ∀ {z} → Γ ∣ s prevalid → Right Γ s z z
  r-step : ∀ {c c′ z} → Γ ∣ s ⊢ c ⟶ᵉ c′ → Right Γ s c′ z → Right Γ s c z

split : ∀ {Γ s P a c} → Γ ∣ s ⊢[ P ] a ◁ c → ∃[ z ] (Left Γ s P a z × Right Γ s c z)
split (c-refl pv)        = _ , l-nil pv , r-nil pv
split (c-lf1 e d)        with split d
... | z , L , R          = z , l-eqv e L , R
split (c-lf2 p st p′ d)  with split d
... | z , L , R          = z , l-sub p st p′ L , R
split (c-rgh d e)        with split d
... | z , L , R          = z , L , r-step e R

rights : ∀ {Γ s P c z} → Right Γ s c z → Γ ∣ s ⊢[ P ] z ◁ c
rights (r-nil pv)    = c-refl pv
rights (r-step e R)  = c-rgh (rights R) e

join : ∀ {Γ s P a c z} → Left Γ s P a z → Right Γ s c z → Γ ∣ s ⊢[ P ] a ◁ c
join (l-nil _) R           = rights R
join (l-eqv e L) R         = c-lf1 e (join L R)
join (l-sub p st p′ L) R   = c-lf2 p st p′ (join L R)
```

The right run is stack-monotone outright, by `pushᵉ`.

```agda
Right-push : ∀ {Γ s s′ c z} → Right Γ s c z → Γ ∣ (s ++ s′) prevalid → Right Γ (s ++ s′) c z
Right-push (r-nil _) pv     = r-nil pv
Right-push (r-step e R) pv  = r-step (pushᵉ e pv) (Right-push R pv)
```

## What this establishes

Chains with a parametric side condition: they are Figure 4's judgements at the top (`≤*wf⇒◁*`,
`◁*⇒≤*wf`), monotone in the condition, closed under application wrapping with the condition
transported along (`◁*-app`), and every single-layer chain splits into a left run and a right
run (`split`/`join`), the right run being stack-monotone (`Right-push`).

What is *not* here yet: wrapping under a binder (`Ms-Fun`/`Ms-FOp`), which needs the renaming
lemmas of `MPSS/Rename`, and the push of a left run, which is the substance of the plan.
