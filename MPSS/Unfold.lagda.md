# MPSS: eliminating the context by unfolding

Every approach so far has had to weigh a stack entry against a variable, and each failed at the
same pair of rules. This one never does. Instead of measuring the configuration, it **erases** it:
translate `Γ;s ⊢ t` to a plain term by substituting away every equivalence annotation, and appeal
to the diamond of a reduction that has no context and no stack — v1's `⟶≡`, which
`PSS/Diamond` proves.

The translation is worth stating for its own sake, because it is the one thing in this whole
investigation that needs no measure at all.

```agda
{-# OPTIONS --safe #-}

module MPSS.Unfold where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Relation.Unary.Any using (here; there)

open import MPSS.WellFormed
open import PSS.Syntax using (_[_:=_]; fresh; fresh-∉; lc-Top)
open import PSS.Reduction using (_⟶≡_; Cr-Var; Cr-Top; Cr-App; Cr-Fun; Cr-Beta; Cr-TopApp)
```

## The unfolding

`U Γ t` replaces every equivalence-annotated variable by its annotation, repeatedly. It is
**structurally recursive on the context** — each step discharges one entry and substitutes it
away, and an entry's annotation is scoped in the rest, which is exactly the tail being recursed on.

No measure, no fuel, no well-founded machinery: the acyclicity that made every height argument
delicate is already carried by the shape of the context.

```agda
U : Ctx → Tm → Tm
U []                  t = t
U ((y , sub , w) ∷ Γ) t = U Γ t
U ((y , eqv , α) ∷ Γ) t = U Γ (t [ y := α ])
```

It is a homomorphism for every term former, since substitution is.

```agda
U-Top : ∀ Γ → U Γ Top ≡ Top
U-Top []                  = refl
U-Top ((y , sub , w) ∷ Γ) = U-Top Γ
U-Top ((y , eqv , α) ∷ Γ) = U-Top Γ

U-app : ∀ Γ a b → U Γ (app a b) ≡ app (U Γ a) (U Γ b)
U-app []                  a b = refl
U-app ((y , sub , w) ∷ Γ) a b = U-app Γ a b
U-app ((y , eqv , α) ∷ Γ) a b = U-app Γ (a [ y := α ]) (b [ y := α ])

U-lam : ∀ Γ w b → U Γ (lam w b) ≡ lam (U Γ w) (U Γ b)
U-lam []                  w b = refl
U-lam ((y , sub , v) ∷ Γ) w b = U-lam Γ w b
U-lam ((y , eqv , α) ∷ Γ) w b = U-lam Γ (w [ y := α ]) (b [ y := α ])

U-bvar : ∀ Γ i → U Γ (bvar i) ≡ bvar i
U-bvar []                  i = refl
U-bvar ((y , sub , w) ∷ Γ) i = U-bvar Γ i
U-bvar ((y , eqv , α) ∷ Γ) i = U-bvar Γ i
```

## The simulation that would finish it

If every equivalence step translated to a step of the context-free reduction, the diamond would
follow from `PSS/Diamond` with no measure anywhere.

```agda
Sim : Set
Sim = ∀ {Γ s t u} → Γ ∣ s ⊢ t ⟶ᵉ u → U Γ t ⟶≡ U Γ u
```

## Why it fails, and where

`Me-FOp` breaks it, and only `Me-FOp`. The rule pops the operand and records the parameter as
being *equivalent* to it, then reduces the body under that binding — but it **keeps the
abstraction**. The unfolding substitutes the binding away, so a body that unfolds its own
parameter translates to a step between two abstractions whose bodies are unrelated.

The smallest instance: the identity's body unfolds the parameter, which is `⊤`.

```agda
pv₀ : [] ∣ (Top ∷ []) prevalid
pv₀ = Pv-Sta (Pv-Nil Pv-Emp) lc-Top (λ ())

step : ∀ {x} → ((x , eqv , Top) ∷ []) ∣ [] ⊢ fvar x ⟶ᵉ Top
step = Me-Pro (Pv-Nil (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ())))
              (here refl)
              (Me-Top (Pv-Nil (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ()))))

fop : [] ∣ (Top ∷ []) ⊢ lam Top (bvar 0) ⟶ᵉ lam Top Top
fop = Me-FOp [] (Me-Top (Pv-Nil Pv-Emp)) (λ _ → step)
```

Under the unfolding at the empty context both sides stay put, so the simulation would have to
supply `λ⊤. x ⟶≡ λ⊤. ⊤` — and the context-free reduction has no step from a variable to `⊤`,
because it has no rule that looks anything up.

```agda
no-var-Top : ∀ {x} → ¬ (fvar x ⟶≡ Top)
no-var-Top ()

sim-false : ¬ Sim
sim-false h with h fop
... | Cr-Fun L _ F = no-var-Top (F {fresh L} (fresh-∉ L))
```

## What this establishes

`U` is definable outright, by plain structural recursion on the context — the one construction in
this investigation that needs no measure. It is a homomorphism for every term former, and it does
simulate the rules that look a variable up: `Me-Pro` becomes an ordinary reduction of the
annotation, and `Me-Var` becomes reflexivity, which is exactly the part v1 gets for free.

`sim-false` says the translation cannot be pushed through `Me-FOp`, and the counterexample is as
small as one can be: `λ⊤. x` with `⊤` on the stack steps to `λ⊤. ⊤`, and no context-free reduction
relates the two, because none relates `x` to `⊤`.

So the obstruction survives its third change of clothes. It is not the stack arithmetic, and not
the existence of a complete development: **the equivalence binding `Me-FOp` introduces is not
eliminable by substitution**, because the rule keeps the abstraction whose parameter it has just
defined. That is precisely what v1 does not have — v1's `Srs-FunOp` records `x ≤ α`, which
`Me-Pro` cannot cash in — and it is why v1's diamond proof does not transfer.
