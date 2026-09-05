# MPSS: the multiplier repair of Φ, refuted at every K

`MPSS/Measure` defines `Φ`, a weight on the subject term that charges every free variable for its
annotation and carries the stack as a list of weights. `../PLAN.md` records what happened next:
the opening lemma could not be stated, because the variable clause charges the annotation *at the
current stack*, and the fix proposed there was to take the stack out of `Φ` and put it in `Ψ`
with a multiplier `K`, chosen to bound the number of occurrences of any bound variable:

> `Φ Γ (app u v) w = 1 + Φ Γ u w + K · Φ Γ v w`
> `Φ Γ (lam a b) w = 1 + K · (1 + Φ Γ a w) + Φ Γ b ((1 + Φ Γ a w) ◂ w)`
> `Φ Γ (fvar x) w = 1 + Φ Γₓ αₓ one`, `Φ Γ (bvar i) w = wt w i`, `Φ Top = 1`
> `Ψ Γ s t = Φ Γ t one + K · Σ_{α ∈ s} Φ Γ α one`

The plan then argued, in prose, that the `Me-FOp` case needs `bump b ≤ K` for a coefficient
`bump b` that grows multiplicatively with nesting depth, so that no constant `K` works. This module
is that argument as a counterexample: for **every** `K`, `Ψ` goes up at `Me-FOp` on a body one
binder deep.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Multiplier where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_; m+1+n≰m)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Measure using (Wt; wt; _◂_; one)
```

## The measure, parametric in K

```agda
module _ (K : ℕ) where

  Φ : Ctx → Tm → Wt → ℕ
  Φ Γ (bvar i)  w = wt w i
  Φ Γ Top       w = 1
  Φ Γ (app u v) w = suc (Φ Γ u w + K * Φ Γ v w)
  Φ Γ (lam a b) w = suc (K * suc (Φ Γ a w) + Φ Γ b (suc (Φ Γ a w) ◂ w))
  Φ []                (fvar x) w = 1
  Φ ((y , c , β) ∷ Γ) (fvar x) w with x ≟ y
  ... | yes _ = suc (Φ Γ β one)
  ... | no  _ = Φ Γ (fvar x) w

  Σstk : Ctx → Stack → ℕ
  Σstk Γ []      = 0
  Σstk Γ (α ∷ s) = Φ Γ α one + Σstk Γ s

  Ψ : Ctx → Stack → Tm → ℕ
  Ψ Γ s t = Φ Γ t one + K * Σstk Γ s
```

## What Me-FOp asks of it

The same shape as `mono-fop` in `MPSS/Height`'s `Measure` record.

```agda
  Me-FOp-nonincreasing : Set
  Me-FOp-nonincreasing = ∀ Γ {z w α} s b → z ∉ dom Γ → z ∉ fv b → z ∉ fvStack s
                       → Ψ ((z , eqv , α) ∷ Γ) s (b ^ fvar z) ≤ Ψ Γ (α ∷ s) (lam w b)
```

## The counterexample

The body is `λx. x` — an abstraction whose annotation is the *outer* parameter, so that the
parameter's weight feeds the inner binder's weight assignment and is paid again there. The stack
entry is a closed term of weight `6K + 4`.

```agda
  body : Tm
  body = lam (bvar 0) (bvar 0)

  entry : Tm
  entry = lam Top (lam Top (lam Top Top))
```

Both sides are polynomials in `K`, and Agda computes them.

```agda
  lhs : ℕ
  lhs = Ψ ((0 , eqv , entry) ∷ []) [] (body ^ fvar 0)

  rhs : ℕ
  rhs = Ψ [] (entry ∷ []) (lam Top body)
```

Agda's normal forms for the two, read off with `Cmd_compute_toplevel`, and checked here by
`refl`. `X` is the weight of `λ⊤. λ⊤. ⊤` less one; the stack entry weighs `1 + X`, the bound
variable `2 + X`.

```agda
  X : ℕ
  X = K * 2 + (1 + (K * 2 + (1 + (K * 2 + 1))))

  lhs-nf : lhs ≡ 1 + (K * (3 + X) + (3 + X) + K * 0)
  lhs-nf = refl

  rhs-nf : rhs ≡ 1 + (K * 2 + (1 + (K * 3 + 3)) + K * (1 + (X + 0)))
  rhs-nf = refl
```

In closed form that is `6K² + 12K + 7` against `6K² + 9K + 5`: the opened body is heavier by
`3K + 2`, for every `K`. The ring solver certifies the gap.

```agda
gap : ∀ K → 1 + (K * (3 + (K * 2 + (1 + (K * 2 + (1 + (K * 2 + 1))))))
                 + (3 + (K * 2 + (1 + (K * 2 + (1 + (K * 2 + 1)))))) + K * 0)
          ≡ 1 + (K * 2 + (1 + (K * 3 + 3))
                 + K * (1 + ((K * 2 + (1 + (K * 2 + (1 + (K * 2 + 1))))) + 0)))
            + (2 + 3 * K)
gap = solve-∀
```

```agda
fop-false : ∀ K → ¬ Me-FOp-nonincreasing K
fop-false K h =
  m+1+n≰m (rhs K) {suc (3 * K)}
    (subst (_≤ rhs K) (trans (lhs-nf K) (trans (gap K) (cong (_+ (2 + 3 * K)) (sym (rhs-nf K)))))
           (h [] {z = 0} {w = Top} {α = entry K} [] (body K) (λ ()) (λ ()) (λ ())))
```

## Where the weight comes from

The stack entry `α` is paid for once on the right, as `K · Φ α`, and the abstraction pays `K` times
its own annotation `⊤` for the parameter. On the left the parameter is worth `1 + Φ α`, and it is the
*annotation* of the inner binder, so the inner binder pays `K · (1 + Φ α)` for its own parameter and
then pays that parameter's weight again in its body. The outer `K · Φ α` covers the first of those;
nothing covers the second. One more level of nesting would multiply it again.

That is the `bump` coefficient of `../PLAN.md` — `bump (lam a b) = K · bump a + bump b · (1 + bump a)`,
which for this body is `K + 2` — exceeding `K` by exactly the two unpaid units per unit of `Φ α`
that the polynomial gap shows. The plan reasoned this from the shape of the required lemma; here
it is a configuration.

## What this establishes

`fop-false`: for every `K`, `Ψ` with multiplier `K` goes **up** at `Me-FOp` on the body `λx. x`
with a stack entry of weight `6K + 4`. So the corrected measure of `../PLAN.md` — the stack out of
`Φ`, a multiplier on the stack in `Ψ` — fails `mono-fop`, and no choice of the multiplier saves it.
The reason is the one the plan gave: the annotation's weight feeds the body's weight assignment,
and a nested binder pays it again.

With `MPSS/Height` this closes the family: charge the stack uniformly (`M`) and `Me-App` breaks;
charge the operand (`M₂`) and `Me-FOp` breaks; charge the stack with a multiplier (`Ψ`) and
`Me-FOp` still breaks, one nesting level deeper.
