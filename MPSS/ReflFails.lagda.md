# v2's Proposition 18 is false as printed

> **Proposition 18 (Reflexivity).** Let `Γ; s` be an extended context, and `u` be a term. We have
> `Γ; s ⊢ u ⟶ˢ u` and `Γ; s ⊢ u ⟶ᵉ u`.

Stated for **every** term and every extended context, with no scoping condition. It is false, and
the counterexample is immediate: `Me-App` pushes the operand onto the stack, and `Pv-Sta` scopes
every stack entry in the domain, so an application whose operand mentions a name the context does
not bind has no reduction at all — not even to itself.

With the empty context, `y y` is such a term.

This matters beyond its own statement: Proposition 18 is what v2's proof of Proposition 17
appeals to for the β case, and `MPSS/BetaScope` refutes that in turn. The repair is the same in
both places — the scoping premise, which `MPSS/StackPush`'s `⟶ᵉ-refl` carries.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.ReflFails where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
```

## The witness

```agda
selfapp : Tm
selfapp = app (fvar 0) (fvar 0)

lc-selfapp : LC selfapp
lc-selfapp = lc-app lc-fvar lc-fvar
```

At the empty context, no stack entry can be scoped, so pushing the operand is impossible.

```agda
no-push : ∀ {s} → [] ∣ (fvar 0 ∷ s) prevalid → ⊥
no-push (Pv-Sta _ _ f) with f (here refl)
... | ()
```

The only rules that could apply to an application are `Me-App`, `Me-TAp` and `Me-Bet`. The
operator is a variable, so `Me-TAp` and `Me-Bet` are out on shape, and `Me-App` needs its premise
at the pushed stack, whose prevalidity the sub-derivation carries.

```agda
no-refl : ¬ ([] ∣ [] ⊢ selfapp ⟶ᵉ selfapp)
no-refl (Me-App d _) = no-push (⟶ᵉ-prevalid d)
```

## The refutation

Stated as the paper does — for every extended context and every term — and also in the form
restricted to locally closed terms, which is the most one could charitably read into it.

```agda
Prop-18ᵉ : Set
Prop-18ᵉ = ∀ {Γ s u} → Γ ∣ s ⊢ u ⟶ᵉ u

prop-18ᵉ-false : ¬ Prop-18ᵉ
prop-18ᵉ-false refl-all = no-refl refl-all

Prop-18ᵉ-lc : Set
Prop-18ᵉ-lc = ∀ {Γ s u} → Γ ∣ s prevalid → LC u → Γ ∣ s ⊢ u ⟶ᵉ u

prop-18ᵉ-lc-false : ¬ Prop-18ᵉ-lc
prop-18ᵉ-lc-false refl-lc = no-refl (refl-lc (Pv-Nil Pv-Emp) lc-selfapp)
```

The promotion half fails for the same reason, since `Ms-Equ` is the only rule that could give a
non-`Top` reduct of an application whose operator is a variable.

```agda
no-reflˢ : ¬ ([] ∣ [] ⊢ selfapp ⟶ˢ selfapp)
no-reflˢ (Ms-Equ _ e) = no-refl e
no-reflˢ (Ms-App d)   = no-push (⟶ˢ-prevalid d)

Prop-18ˢ-lc : Set
Prop-18ˢ-lc = ∀ {Γ s u} → Γ ∣ s prevalid → LC u → Γ ∣ s ⊢ u ⟶ˢ u

prop-18ˢ-lc-false : ¬ Prop-18ˢ-lc
prop-18ˢ-lc-false refl-lc = no-reflˢ (refl-lc (Pv-Nil Pv-Emp) lc-selfapp)
```

## What this establishes

**Proposition 18 is false as printed**, for both reductions, and stays false when restricted to
locally closed terms in a prevalid context. What holds is the statement with the scoping premise
`fv u ⊑ dom Γ`, which is `⟶ᵉ-refl` and `⟶ˢ-refl` in `MPSS/StackPush`.

The defect is in the rules as the paper gives them, not in the encoding: in a named presentation
the same term `y y` at the empty context is blocked by `Pv-Sta` for the same reason, since
`Me-App`'s premise sits at the pushed stack and every leaf of that sub-derivation demands the
extended context be prevalid.
