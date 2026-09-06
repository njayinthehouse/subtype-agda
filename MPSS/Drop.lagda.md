# MPSS: dropping a set of names from a context

The diamond's corrected invariant (`MPSS/Strengthen`, `MPSS/Closed`) is best stated not as
"the join avoids `B`" but as "the join is derivable at the context with `B` removed" — a
derivation rather than a predicate on one, so that renaming and substituting the join afterwards
need no preservation lemmas. This module defines that removal and proves what the diamond
needs of it: lookups of names outside `B` survive, the domain shrinks, and the result is prevalid
when `B` is closed under the context's annotations and the stack does not mention `B`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Drop where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Closed
```

## The operation

```agda
infixl 6 _∖_
_∖_ : Ctx → List Name → Ctx
[]                ∖ B = []
((z , c , t) ∷ Γ) ∖ B with z ∈? B
... | yes _ = Γ ∖ B
... | no  _ = (z , c , t) ∷ (Γ ∖ B)

∖-∈ : ∀ {Γ B z c t} → z ∈ B → ((z , c , t) ∷ Γ) ∖ B ≡ Γ ∖ B
∖-∈ {B = B} {z} z∈ with z ∈? B
... | yes _ = refl
... | no  q = ⊥-elim (q z∈)

∖-∉ : ∀ {Γ B z c t} → z ∉ B → ((z , c , t) ∷ Γ) ∖ B ≡ (z , c , t) ∷ (Γ ∖ B)
∖-∉ {B = B} {z} z∉ with z ∈? B
... | yes p = ⊥-elim (z∉ p)
... | no  _ = refl

∖-[] : ∀ Γ → Γ ∖ [] ≡ Γ
∖-[] []                = refl
∖-[] ((z , c , t) ∷ Γ) = cong ((z , c , t) ∷_) (∖-[] Γ)
```

A name absent from the domain makes no difference to the set.

```agda
∖-∉dom : ∀ Γ {B x} → x ∉ dom Γ → Γ ∖ (x ∷ B) ≡ Γ ∖ B
∖-∉dom [] x∉ = refl
∖-∉dom ((z , c , t) ∷ Γ) {B} {x} x∉ = go (z ∈? B)
  where
    ih : Γ ∖ (x ∷ B) ≡ Γ ∖ B
    ih = ∖-∉dom Γ (λ h → x∉ (there h))
    go : Dec (z ∈ B) → ((z , c , t) ∷ Γ) ∖ (x ∷ B) ≡ ((z , c , t) ∷ Γ) ∖ B
    go (yes p) = trans (∖-∈ {Γ} {x ∷ B} (there p)) (trans ih (sym (∖-∈ p)))
    go (no  q) = trans (∖-∉ {Γ} {x ∷ B} z∉′) (trans (cong ((z , c , t) ∷_) ih) (sym (∖-∉ q)))
      where
        z∉′ : z ∉ (x ∷ B)
        z∉′ (here refl) = x∉ (here refl)
        z∉′ (there h)   = q h
```

## Lookups and domains

```agda
∈-∖ : ∀ {Γ B x c t} → x ∉ B → (x , c , t) ∈ Γ → (x , c , t) ∈ (Γ ∖ B)
∈-∖ {(z , c , t) ∷ Γ} {B} x∉ (here refl) rewrite ∖-∉ {Γ} {B} {z} {c} {t} x∉ = here refl
∈-∖ {(z , c′ , t′) ∷ Γ} {B} x∉ (there m) with z ∈? B
... | yes _ = ∈-∖ x∉ m
... | no  _ = there (∈-∖ x∉ m)

dom-∖ : ∀ Γ {B} → dom (Γ ∖ B) ⊑ dom Γ
dom-∖ [] ()
dom-∖ ((z , c , t) ∷ Γ) {B} h with z ∈? B
... | yes _ = there (dom-∖ Γ h)
dom-∖ ((z , c , t) ∷ Γ) {B} (here p)  | no _ = here p
dom-∖ ((z , c , t) ∷ Γ) {B} (there h) | no _ = there (dom-∖ Γ h)

∉-dom-∖ : ∀ Γ {B x} → x ∉ dom Γ → x ∉ dom (Γ ∖ B)
∉-dom-∖ Γ x∉ h = x∉ (dom-∖ Γ h)
```

A name outside `B` that is in the domain is in the restricted domain.

```agda
∈-dom-∖ : ∀ Γ {B x} → x ∉ B → x ∈ dom Γ → x ∈ dom (Γ ∖ B)
∈-dom-∖ [] x∉ ()
∈-dom-∖ ((z , c , t) ∷ Γ) {B} x∉ h with z ∈? B
∈-dom-∖ ((z , c , t) ∷ Γ) {B} x∉ (here refl) | yes p = ⊥-elim (x∉ p)
∈-dom-∖ ((z , c , t) ∷ Γ) {B} x∉ (there h)   | yes _ = ∈-dom-∖ Γ x∉ h
∈-dom-∖ ((z , c , t) ∷ Γ) {B} x∉ (here p)    | no  _ = here p
∈-dom-∖ ((z , c , t) ∷ Γ) {B} x∉ (there h)   | no  _ = there (∈-dom-∖ Γ x∉ h)
```

## Prevalidity

Every kept entry's annotation is scoped in the original domain; by closure it mentions no name
of `B`, so it is scoped in the restricted domain.

```agda
prevalid-∖ : ∀ {Γ B} → Closed Γ B → Γ prevalid → (Γ ∖ B) prevalid
prevalid-∖ cl Pv-Emp = Pv-Emp
prevalid-∖ {(z , sub , t) ∷ Γ} {B} cl (Pv-Ctx pv z∉ lt ft) with z ∈? B
... | yes _ = prevalid-∖ (closed-tail cl) pv
... | no z∉B = Pv-Ctx (prevalid-∖ (closed-tail cl) pv) (∉-dom-∖ Γ z∉) lt
                      (λ {y} h → ∈-dom-∖ Γ (λ y∈B → z∉B (cl (here refl) y∈B h)) (ft h))
prevalid-∖ {(z , eqv , t) ∷ Γ} {B} cl (Pv-EqA pv z∉ lt ft) with z ∈? B
... | yes _ = prevalid-∖ (closed-tail cl) pv
... | no z∉B = Pv-EqA (prevalid-∖ (closed-tail cl) pv) (∉-dom-∖ Γ z∉) lt
                      (λ {y} h → ∈-dom-∖ Γ (λ y∈B → z∉B (cl (here refl) y∈B h)) (ft h))

prevalid-∖-ext : ∀ {Γ B s} → Closed Γ B → B ∉* fvStack s
               → Γ ∣ s prevalid → (Γ ∖ B) ∣ s prevalid
prevalid-∖-ext cl s∉ (Pv-Nil pv) = Pv-Nil (prevalid-∖ cl pv)
prevalid-∖-ext {Γ} {B} cl s∉ (Pv-Sta {α = α} pv lα fα) =
  Pv-Sta (prevalid-∖-ext cl (∉*-++ʳ (fv α) s∉) pv) lα
         (λ {y} h → ∈-dom-∖ Γ (λ y∈B → ∉*-++ˡ s∉ y∈B h) (fα h))
```

## What this establishes

`Γ ∖ B` with the four facts the diamond's invariant uses: `∖-[]` (the invariant at the empty
set is the diamond itself), `∖-∉` and `∖-∈` (how a binding at the head is treated, which is what
the binder cases see), `∖-∉dom` (a fresh name added to the set changes nothing below its own
binding), and `prevalid-∖-ext` (the restricted configuration is prevalid).
