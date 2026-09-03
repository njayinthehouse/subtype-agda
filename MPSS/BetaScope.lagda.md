# A scoping defect in v2's `Me-Bet`, and the refutation of Proposition 17

v2's β-rule, as printed in Figure 2 and transcribed verbatim in `MPSS/Reduction`, is

> `Γ;s ⊢ u ⟶≡ u′    Γ;nil ⊢ v ⟶≡ v′  /  Γ;s ⊢ (λx≤t.u) v ⟶≡ u′[x\v′]`

The body `u` is reduced in `Γ;s`, a context that does **not** bind `x`. Every leaf of an
equivalence derivation demands `Γ;s prevalid`, and `Me-App` pushes its operand onto the stack,
where `Pv-Sta` demands the operand be scoped in `dom Γ`. So a body in which the parameter occurs
as an *operand* — `λx≤t. y x` is the smallest — cannot be reduced at all under `Me-Bet`, and the
redex `(λx≤t. y x) v` has no equivalence step to `y v`.

That refutes v2's Proposition 17 ("if `u ↦ v` then `u ⟶≡ v`") as printed. The appendix proof
says the β case "holds by rule `Me-Bet` and reflexivity (Proposition 18)", and Proposition 18
claims reflexivity for *every* term at *every* extended context — which is itself false for a
term with a free variable outside `dom Γ`, exactly the situation `Me-Bet`'s body premise creates
(`MPSS/Scope` records that reflexivity needs `fv u ⊑ dom Γ`).

This is independent of Conjecture 8. Proposition 17 is used in Lemma 6 (every congruence case)
and in Theorem 5 (the `Ws-Rgh` step from `t ↦ t′`), so as printed the conditional proof of
preservation has a second gap. The evident repair is to reduce the body under `Γ, x ≡ v` (as
`Me-FOp` does) or under `Γ, x ≤ t` (as `Me-Fun` does); either restores the scoping. Nothing
existing is modified here; the literal rule stays in `MPSS/Reduction` so that this refutation is
about the paper's system.

```agda
{-# OPTIONS --safe #-}

module MPSS.BetaScope where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import MPSS.Reduction
open import PSS.Reduction using (_↦_; E-App)
open import PSS.Syntax using (bvar)
```

## The witness

`y ≤ Top` in scope; the redex `(λx≤Top. y x) Top`, whose body applies the parameter.

```agda
Γ₀ : Ctx
Γ₀ = (0 , sub , Top) ∷ []

pv₀ : Γ₀ ∣ [] prevalid
pv₀ = Pv-Nil (Pv-Ctx Pv-Emp (λ ()) lc-Top (λ ()))

body : Tm
body = app (fvar 0) (bvar 0)

redex : Tm
redex = app (lam Top body) Top

lc-redex : LC redex
lc-redex = lc-app (lc-lam [] lc-Top (λ _ → lc-app lc-fvar lc-fvar)) lc-Top

fv-redex : fv redex ⊑ dom Γ₀
fv-redex (here refl) = here refl
```

The operational semantics contracts it.

```agda
steps : redex ↦ app (fvar 0) Top
steps = E-App (lc-lam [] lc-Top (λ _ → lc-app lc-fvar lc-fvar)) lc-Top
```

## No equivalence step reaches the contractum

The opened body `y x` cannot reduce at all in `Γ₀ ∣ []` when `x` is fresh: the only applicable
rule is `Me-App`, which pushes `x` onto the stack, and prevalidity of that stack would put `x`
in `dom Γ₀`.

```agda
no-body : ∀ {x w} → x ≢ 0 → Γ₀ ∣ [] ⊢ app (fvar 0) (fvar x) ⟶ᵉ w → ⊥
no-body x≢0 (Me-App d _) with ⟶ᵉ-prevalid d
... | Pv-Sta _ _ f with f (here refl)
...   | here p    = x≢0 p
...   | there ()
```

At the redex, `Me-App` keeps the operator an abstraction, `Me-TAp` needs a `Top` operator, and
`Me-Bet` needs the body to reduce. So nothing reaches `y Top`.

The target is kept general and pinned by an equation afterwards, because `Me-Bet`'s conclusion
`u′ ^ v′` is not a constructor form and Agda cannot unify it against `y Top` directly.

```agda
no-β′ : ∀ {w} → Γ₀ ∣ [] ⊢ app (lam Top body) Top ⟶ᵉ w → w ≡ app (fvar 0) Top → ⊥
no-β′ (Me-App (Me-FOp _ _ _) _) ()
no-β′ (Me-Bet L F _) _ = no-body x≢0 (F x∉L)
  where
    x   = fresh (0 ∷ L)
    x∉L : x ∉ L
    x∉L h = fresh-∉ (0 ∷ L) (there h)
    x≢0 : x ≢ 0
    x≢0 p = fresh-∉ (0 ∷ L) (here p)

no-β : ¬ (Γ₀ ∣ [] ⊢ redex ⟶ᵉ app (fvar 0) Top)
no-β d = no-β′ d refl
```

## Proposition 17, refuted

Stated with every hygiene hypothesis one could want — prevalid context, locally closed and
scoped subject — so the refutation is not a scoping artefact of the encoding.

```agda
Prop-17 : Set
Prop-17 = ∀ {Γ u v}
        → Γ ∣ [] prevalid → LC u → fv u ⊑ dom Γ
        → u ↦ v
        → Γ ∣ [] ⊢ u ⟶ᵉ v

prop-17-false : ¬ Prop-17
prop-17-false p = no-β (p pv₀ lc-redex fv-redex steps)
```

## What this establishes

**v2's Proposition 17 is false for the system as printed**, because `Me-Bet` reduces the body of
a redex in a context that does not bind the parameter. The witness is the smallest possible:
`(λx≤Top. y x) Top` with `y ≤ Top`.

Consequences:

- Lemma 6 and Theorem 5 of v2, which cite Proposition 17, have a gap as printed that is
  independent of Conjecture 8. It is a repairable one — bind the parameter in `Me-Bet`'s body
  premise — but the repair changes the reduction relation, and the commutation theorem would have
  to be re-checked against it.
- Any proof of Conjecture 8 that contracts a redex (the "β route" through which `AppCongr` would
  have to go, see `MPSS/Conjecture8`) is unavailable in the literal system whenever the body
  applies its parameter. A proof for the literal system must go through the stack rules alone.
