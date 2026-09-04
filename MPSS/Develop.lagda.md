# MPSS: the complete development

Takahashi's route to the diamond: define `t*`, the term obtained by contracting *every* redex of
`t` at once, and prove the triangle — every step out of `t` lands on something that reduces to
`t*`. The diamond is then immediate and needs no measure, because both reducts go to the same
place.

It gives the diamond in the paper's own general form, which is worth noting. With
`Γ;s ↣ Γ₁;s₁` and `Γ;s ↣ Γ₂;s₂`, a triangle stated as

> `Γ;s ⊢ t ⟶≡ u  →  Γ;s ↣ Γ';s'  →  Γ';s' ⊢ u ⟶≡ t*`

instantiates twice to give exactly Lemma 2, with `t₃ := t*`. The reduced configuration is not a
complication: it is what the `Me-App` case needs, since joining there requires the operator's
target at the *reduced* operand's stack, which is what `Ct-Stk` supplies.

What Takahashi trades away is a proof obligation for a definition obligation: `t*` has to exist.
This module is that attempt.

```agda
{-# OPTIONS --safe #-}

module MPSS.Develop where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)

open import MPSS.WellFormed
open import PSS.Syntax using (closeRec; fresh; fresh-∉)
```

## Looking a variable up

```agda
lookupEqv : Ctx → Name → Maybe Tm
lookupEqv []                   x = nothing
lookupEqv ((y , sub , w) ∷ Γ) x = lookupEqv Γ x
lookupEqv ((y , eqv , α) ∷ Γ) x with x ≟ y
... | yes _ = just α
... | no  _ = lookupEqv Γ x
```

## The development

One clause per rule of `⟶≡`, contracting everything at once. Written without fuel it is rejected,
and Agda names the two calls exactly:

> `Termination checking failed for the following functions: star`
> — *Problematic calls:*
> `star ((fresh (dom Γ) , sub , w) ∷ Γ) [] (b ^ fvar (fresh (dom Γ)))`
> and `star Γ (b ∷ s) a`

The first is the locally nameless tax and nothing more: `b ^ z` has the same size as `b`, which is
a subterm of `lam w b`, so any size-based recursion sees through it even though Agda's structural
checker cannot.

**The second is the obstruction, in the definition rather than in a proof.** `star Γ (b ∷ s) a` is
`Me-App` pushing the operand, and it is forced — every step out of `app a b` is `Me-App` with its
operator premise at `b :: s`, so the development must be computed there. `MPSS/Height` proves no
height of this shape can pay for that push: `ht-fop` needs a stack entry charged one more than its
own height, and `ht-app-false` shows an operand cannot be.

So the fuel below is documentation, not a route. A fuelled development is not the *complete* one,
and the triangle fails for it: when the fuel runs out the clause returns its argument, which is
not maximal.

```agda
star : ℕ → Ctx → Stack → Tm → Tm
star zero    Γ s t = t
star (suc n) Γ s (bvar i) = bvar i
star (suc n) Γ s Top      = Top
star (suc n) Γ s (fvar x) with lookupEqv Γ x
... | just α  = star n Γ s α
... | nothing = fvar x
star (suc n) Γ [] (lam w b) =
  lam (star n Γ [] w) (closeRec 0 (fresh (dom Γ)) (star n ((fresh (dom Γ) , sub , w) ∷ Γ) []
                                                         (b ^ fvar (fresh (dom Γ)))))
star (suc n) Γ (α ∷ s) (lam w b) =
  lam (star n Γ [] w) (closeRec 0 (fresh (dom Γ)) (star n ((fresh (dom Γ) , eqv , α) ∷ Γ) s
                                                         (b ^ fvar (fresh (dom Γ)))))
star (suc n) Γ s (app Top b)       = Top
star (suc n) Γ s (app (lam w b) v) = (star n Γ s b) ^ (star n Γ [] v)
star (suc n) Γ s (app a b)         = app (star n Γ (b ∷ s) a) (star n Γ [] b)
```

## What this establishes

The shape of the complete development, and Agda's verdict on defining it: the `Me-App` push is
rejected, and `MPSS/Height` already proves no measure of that family can justify it.

Takahashi's method therefore does not dodge the obstruction — it relocates it, from the diamond's
induction to the existence of `t*`. The two demands are the same pair as before. `Me-FOp` binds a
stack entry to a variable worth one more than the entry; `Me-App` puts an operand on the stack
unchanged. Whichever way you charge, one of them is unpaid.
