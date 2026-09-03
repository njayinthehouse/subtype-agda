# MPSS: the measure for the diamond's recursion

`../PLAN.md` records why no measure built from context position and term size can justify the
recursion in v2's Lemma 2: promotion decreases the promoted variable's position while the binder
rules increase it, and derivation size moves the other way. The measure that works is on the
**subject term**, not on the derivations, which is what makes it indifferent to the stack and the
context a recursive call lands at.

`Φ Γ t w ns` is the weight of `t` with every free variable charged for its annotation's weight,
recursively. Two representation choices make it definable:

- **bound indices carry an assignment `w`**, so going under a binder shifts the weights rather
  than substituting into the term — that is what makes the opening lemma provable;
- **the stack is carried as a list of weights `ns`, not of terms**, so the abstraction case can
  charge the operand it will meet without recursing on a term that is not a subterm. Recursion is
  then lexicographic on the context and the term, and Agda sees it.

Three features earn their keep:

- **the variable case charges the annotation**, so promotion strictly decreases the measure: it
  cashes in a charge already levied rather than paying a penalty;
- **the abstraction case charges the body at the weight its parameter will have once opened**, so
  entering a binder decreases too, with no counting of occurrences;
- **the abstraction case reads the stack head** when there is one, since `Me-FOp` binds the
  parameter to the popped operand rather than to the annotation.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Measure where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import MPSS.WellFormed
open import PSS.Syntax using (∉-++)
```

## Weight assignments

```agda
Wt : Set
Wt = ℕ → ℕ

infixr 5 _◂_
_◂_ : ℕ → Wt → Wt
(n ◂ w) zero    = n
(n ◂ w) (suc i) = w i

one : Wt
one _ = 1
```

## The measure

```agda
Φ : Ctx → Tm → Wt → List ℕ → ℕ

Φ Γ (bvar i)  w ns = w i
Φ Γ Top       w ns = 1
Φ Γ (app u v) w ns = suc (Φ Γ u w (Φ Γ v w [] ∷ ns) + Φ Γ v w [])

Φ Γ (lam a b) w []       = suc (Φ Γ a w [] + Φ Γ b (suc (Φ Γ a w []) ◂ w) [])
Φ Γ (lam a b) w (n ∷ ns) = suc (Φ Γ a w [] + Φ Γ b (suc n ◂ w) ns + n)

Φ []                (fvar x) w ns = 1
Φ ((y , c , β) ∷ Γ) (fvar x) w ns with x ≟ y
... | yes _ = suc (Φ Γ β one ns)
... | no  _ = Φ Γ (fvar x) w ns
```

The stack of a configuration, weighed, and the configuration's own weight.

```agda
wtStack : Ctx → Stack → List ℕ
wtStack Γ []      = []
wtStack Γ (α ∷ s) = Φ Γ α one (wtStack Γ s) ∷ wtStack Γ s

Ψ : Ctx → Stack → Tm → ℕ
Ψ Γ s t = Φ Γ t one (wtStack Γ s)
```

## Extending the context leaves the weight alone

Provided the new name does not occur in the term. The stack is already a list of numbers, so it
is untouched by construction — which is the second dividend of that representation.

```agda
Φ-ext : ∀ {Γ z c β} t w ns → z ∉ fv t
      → Φ ((z , c , β) ∷ Γ) t w ns ≡ Φ Γ t w ns

Φ-ext (bvar i) w ns z∉ = refl
Φ-ext Top      w ns z∉ = refl

Φ-ext {Γ} {z} {c} {β} (fvar x) w ns z∉ = helper
  where
    helper : Φ ((z , c , β) ∷ Γ) (fvar x) w ns ≡ Φ Γ (fvar x) w ns
    helper with x ≟ z
    ... | yes p = ⊥-elim (z∉ (here (sym p)))
    ... | no  _ = refl

Φ-ext {Γ} {z} {c} {β} (app u v) w ns z∉
  rewrite Φ-ext {Γ} {z} {c} {β} v w [] (∉-++ʳ (fv u) z∉) =
  cong (λ k → suc (k + Φ Γ v w []))
       (Φ-ext u w (Φ Γ v w [] ∷ ns) (∉-++ˡ z∉))

Φ-ext {Γ} {z} {c} {β} (lam a b) w []
  z∉ rewrite Φ-ext {Γ} {z} {c} {β} a w [] (∉-++ˡ z∉) =
  cong (λ k → suc (Φ Γ a w [] + k))
       (Φ-ext b (suc (Φ Γ a w []) ◂ w) [] (∉-++ʳ (fv a) z∉))

Φ-ext {Γ} {z} {c} {β} (lam a b) w (n ∷ ns)
  z∉ rewrite Φ-ext {Γ} {z} {c} {β} a w [] (∉-++ˡ z∉) =
  cong (λ k → suc (Φ Γ a w [] + k + n))
       (Φ-ext b (suc n ◂ w) ns (∉-++ʳ (fv a) z∉))
```

## What this establishes

The measure `Φ`, defined by lexicographic recursion on the context and the term, with bound
indices weighed by an assignment that binders shift and the stack weighed in advance; and the
fact that a fresh context entry does not change it.
