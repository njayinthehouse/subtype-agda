# Subtyping an applied abstraction

`Embed/TypePreserving` leaves one module parameter: the `t-ƛ` case at a non-empty stack. There,
`Srs-FunOp` binds the parameter to the stacked operand `α` while the induction hypothesis has
typed the body under the annotation `a`. `PSS/BoundedNarrowing` shows the gap cannot be closed by
F<:-style narrowing; `PSS/NarrowPoly` shows it *can* be closed once `α ≤ a` is available at every
stack.

This module puts the two together, as a lemma about λ⊲ alone.

```agda
{-# OPTIONS --safe #-}

module PSS.FunOpSubtyping where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.Close using (open-close; close-open; fv-close)
open import PSS.Commutation using (⟶≤-prevalid; ⟶≤-lc)
open import PSS.WellFormed using (fvStack)
open import PSS.Narrowing using (_∣_⊢_⟶≤*_; εₚ; _◅ₚ_; _⟶≡*_; εₑ; _◅ₑ_; ⊲⇒diag; diag⇒⊲)
open import PSS.Congruence using (⟶≤*-funop-open)
open import PSS.NarrowPoly using (Below; ⊲-narrow; ⟶≡*-fun-open)
```

## The lemma

The compatibility hypothesis is exactly what `Wf-App`-style well-formedness provides at the point
an application is formed: the operand is below the abstraction's annotation. Here it is demanded
at every stack, because `PSS/BoundedNarrowing` shows the empty-stack version is too weak.

```agda
funop-≤ : ∀ {Γ s α a b B} (L : List Name)
        → Γ ∣ (α ∷ s) prevalid
        → LC α → LC a → LC B → fv α ⊑ dom Γ
        → (∀ {y} → y ∉ L → Below Γ y α a)
        → (∀ {y} → y ∉ L → LC (b ^ fvar y))
        → (∀ {y} → y ∉ L → ((y , a) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ≤ (B ^ fvar y))
        → Γ ∣ (α ∷ s) ⊢ lam a b ≤ lam a B
funop-≤ {Γ} {s} {α} {a} {b} {B} L pv lα la lB fvα bel lcb ih =
  diag⇒⊲ pv left right
  where
    A  = L ++ fv α ++ fv a ++ fv b ++ fv B ++ dom Γ ++ fvStack s
    y  = fresh A
    a∉ = fresh-∉ A
    r₁ = ∉-++ʳ L a∉
    r₂ = ∉-++ʳ (fv α) r₁
    r₃ = ∉-++ʳ (fv a) r₂
    r₄ = ∉-++ʳ (fv b) r₃
    r₅ = ∉-++ʳ (fv B) r₄

    y∉L  = ∉-++ˡ a∉
    y∉α  : y ∉ fv α
    y∉α  = ∉-++ˡ r₁
    y∉b  : y ∉ fv b
    y∉b  = ∉-++ˡ r₃
    y∉B  : y ∉ fv B
    y∉B  = ∉-++ˡ r₄
    y∉Γ  : y ∉ dom Γ
    y∉Γ  = ∉-++ˡ r₅
    y∉s  : y ∉ fvStack s
    y∉s  = ∉-++ʳ (dom Γ) r₅

    narrowed : ((y , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ≤ (B ^ fvar y)
    narrowed = ⊲-narrow [] (bel y∉L) lα la fvα (lcb y∉L) (ih y∉L)

    inner = ⊲⇒diag narrowed
    w     = proj₁ inner
    chain = proj₁ (proj₂ inner)
    ce    = proj₂ (proj₂ inner)

    left : Γ ∣ (α ∷ s) ⊢ lam a b ⟶≤* lam a (closeRec 0 y w)
    left = ⟶≤*-funop-open y y∉α y∉b y∉Γ y∉s (lcb y∉L) chain

    right : lam a B ⟶≡* lam a (closeRec 0 y w)
    right = ⟶≡*-fun-open y y∉B la (subst-lc-open lB) ce
      where
        subst-lc-open : LC B → LC (B ^ fvar y)
        subst-lc-open l rewrite sym (open-lc-id l 0 (fvar y)) = l
```

## What this establishes

The `t-ƛ`-at-a-non-empty-stack case is **provable**, given that the stacked operand is below the
abstraction's annotation at every stack.

That hypothesis is not decoration. `PSS/BoundedNarrowing` refutes the version where it holds only
at the empty stack, so nothing weaker will do. And it is exactly the invariant the application
rule can supply: when `Srs-App` pushes an operand, well-formedness of the application has already
established that the operand is below the annotation it will meet.

**Why this does not yet close `Embed/TypePreserving`.** Threading the invariant through the
translation runs into the same obstruction one level up. To supply `Below` for the operand, the
`t-app` case would have to know `⟦u⟧ ≤ ⟦A⟧` *at every stack*. Its induction hypothesis gives that
at the empty stack, and promoting it to every stack is precisely the transport `push-is-false`
refutes.

So the invariant is not derivable inside the translation. It has to come from a judgement that
already carries it — λ⊲'s well-formedness, where `W-App` demands the operand be a well-subtype of
the annotation. That points at retargeting the translation from `≤` to `≤*wf`, which is a
different theorem, not a repair of this one.

`MPSS/StackObligation` finds the same requirement in v2's system, and shows that recording the
obligation is necessary but that the single-step shape of the binder rules is a further obstacle
there.
