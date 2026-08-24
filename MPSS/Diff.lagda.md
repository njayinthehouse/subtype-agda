# What actually changed between v1 (λ⊲) and v2 (MPSS)

The rules were renamed wholesale — `Cr-*`/`Srs-*` became `Me-*`/`Ms-*` — but that is cosmetic.
This module proves the changes that are **not** cosmetic, so the answer rests on machine-checked
statements rather than on reading two figures side by side.

```agda
{-# OPTIONS --safe #-}

module MPSS.Diff where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import MPSS.Subtyping

import PSS.Reduction as V1
```

## Difference 1 — equivalence reduction can now move a variable

This is the sharpest one. In v1, `⟶≡` on a free variable is **stuck**: `Cr-Var` is the only rule
with a variable on the left, so the target must be that same variable. `../Embed/TypePreserving`
uses exactly this fact.

```agda
v1-fvar-stuck : ∀ {x w} → fvar x V1.⟶≡ w → w ≡ fvar x
v1-fvar-stuck V1.Cr-Var = refl
```

In MPSS it is false. `Me-Pro` lets a variable carrying an equivalence annotation reduce to that
annotation, so a variable can equivalence-reduce to something else entirely.

```agda
Γ₁ : Ctx
Γ₁ = (1 , eqv , Top) ∷ []

pv₁ : Γ₁ ∣ [] prevalid
pv₁ = Pv-Nil (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ()))

mpss-fvar-moves : Γ₁ ∣ [] ⊢ fvar 1 ⟶ᵉ Top
mpss-fvar-moves = Me-Pro pv₁ (here refl) (Me-Top pv₁)

v1-fvar-stuck-fails-in-MPSS :
  ¬ (∀ {Γ s x w} → Γ ∣ s ⊢ fvar x ⟶ᵉ w → w ≡ fvar x)
v1-fvar-stuck-fails-in-MPSS stuck with stuck mpss-fvar-moves
... | ()
```

So MPSS's equivalence reduction is **not** v1's with a decorative index: the index is load
bearing, and the relation is strictly larger.

## Difference 2 — the two lookups are disjoint

A variable bound by an equivalence annotation is invisible to `Ms-Pro`, which needs a *subtype*
annotation. It reaches subtyping only through `Ms-Equ`. v1 had no such distinction, since every
annotation was a subtype annotation.

```agda
eqv-not-sub : ∀ {Γ x α t} → ((x , eqv , α) ∷ Γ) prevalid → ¬ (x ≤ t ∈ ((x , eqv , α) ∷ Γ))
eqv-not-sub (Pv-EqA _ x∉ _ _) (there m) = x∉ (∈-dom m)
```

## Difference 3 — the stack now binds by equivalence, not subtyping

v1's `Srs-FunOp` extended the context with `x ≤ α`; MPSS's `Ms-FOp` extends it with `x ≡ α`.
The popped operand is recorded exactly rather than as an upper bound. This is visible in the
rule types, and its consequence is that a parameter can be *unfolded* to the operand:

```agda
param-unfolds : ∀ {Γ s α x}
              → Γ ∣ s prevalid
              → x ≐ α ∈ Γ
              → Γ ∣ s ⊢ α ⟶ᵉ α
              → Γ ∣ s ⊢ fvar x ≤ α
param-unfolds pv m d = As-Left-1 (Ms-Equ pv (Me-Pro pv m d)) (As-Refl pv)
```

In v1 the corresponding parameter could only be *promoted* to its bound, never identified with
it, so no equivalence step of this shape existed.

## What did **not** change: promotion is still not stack-monotone

The natural hope is that binding by equivalence removes the obstruction we hit in
`../Embed/TypePreserving` — that a step derivable at the empty stack fails at a larger one. It
does not. With `y ≤ Top` in scope, `λx≤y. x` still promotes to `λx≤y. y` at `nil`, using `Ms-Fun`
to bind the parameter by the annotation `y`:

```agda
Γ₀ : Ctx
Γ₀ = (0 , sub , Top) ∷ []

pv₀ : Γ₀ ∣ [] prevalid
pv₀ = Pv-Nil (Pv-Ctx Pv-Emp (λ ()) lc-Top (λ ()))

fv-y : fv (fvar 0) ⊑ dom Γ₀
fv-y (here refl) = here refl

witness : Γ₀ ∣ [] ⊢ lam (fvar 0) (bvar 0) ⟶ˢ lam (fvar 0) (fvar 0)
witness = Ms-Fun (0 ∷ []) body
  where
    body : ∀ {x} → x ∉ (0 ∷ [])
         → ((x , sub , fvar 0) ∷ Γ₀) ∣ [] ⊢ (bvar 0 ^ fvar x) ⟶ˢ (fvar 0 ^ fvar x)
    body {x} x∉ = Ms-Pro (Pv-Nil (Pv-Ctx (Pv-Ctx Pv-Emp (λ ()) lc-Top (λ ()))
                                         x∉ lc-fvar fv-y)) (here refl)
```

At the stack `[Top]` it fails, exactly as in v1 — `Ms-Fun` no longer applies, and `Ms-FOp` binds
`x ≡ Top`, from which the parameter can only reach `Top`.

```agda
Top-⟶ᵉ : ∀ {Γ s w} → Γ ∣ s ⊢ Top ⟶ᵉ w → w ≡ Top
Top-⟶ᵉ (Me-Top _) = refl

inner-e : ∀ {x} → x ≢ 0
        → ((x , eqv , Top) ∷ Γ₀) ∣ [] ⊢ fvar x ⟶ᵉ fvar 0 → ⊥
inner-e x≢0 (Me-Var _)             = x≢0 refl
inner-e x≢0 (Me-Pro _ (here refl) d) with Top-⟶ᵉ d
... | ()
inner-e x≢0 (Me-Pro _ (there (here ())) _)

inner-s : ∀ {x} → x ≢ 0
        → ((x , eqv , Top) ∷ Γ₀) ∣ [] ⊢ fvar x ⟶ˢ fvar 0 → ⊥
inner-s x≢0 (Ms-Pro _ (here ()))
inner-s x≢0 (Ms-Pro _ (there (here ())))
inner-s x≢0 (Ms-Equ _ e) = inner-e x≢0 e

no-push : ¬ (Γ₀ ∣ (Top ∷ []) ⊢ lam (fvar 0) (bvar 0) ⟶ˢ lam (fvar 0) (fvar 0))
no-push (Ms-Equ _ (Me-FOp L _ F)) = inner-e (x≢0 L) (F (x∉L L))
  where
    x∉L : ∀ L → fresh (0 ∷ L) ∉ L
    x∉L L h = fresh-∉ (0 ∷ L) (there h)
    x≢0 : ∀ L → fresh (0 ∷ L) ≢ 0
    x≢0 L p = fresh-∉ (0 ∷ L) (here p)
no-push (Ms-FOp L F) = inner-s (x≢0 L) (F (x∉L L))
  where
    x∉L : ∀ L → fresh (0 ∷ L) ∉ L
    x∉L L h = fresh-∉ (0 ∷ L) (there h)
    x≢0 : ∀ L → fresh (0 ∷ L) ≢ 0
    x≢0 L p = fresh-∉ (0 ∷ L) (here p)

push-is-false : ¬ (∀ {Γ s u v} → Γ ∣ [] ⊢ u ⟶ˢ v → Γ ∣ s prevalid → Γ ∣ s ⊢ u ⟶ˢ v)
push-is-false push =
  no-push (push witness (Pv-Sta pv₀ lc-Top (λ ())))
```

## Verdict

**MPSS differs from λ⊲ substantially, not superficially.** Three changes are real:

1. **Equivalence reduction gained a rule and became genuinely context-sensitive.** In v1,
   `fvar x ⟶≡ w` forces `w ≡ fvar x`; in MPSS it does not. v1's `Γ ∣ s` index on `⟶≡` was
   provably decorative (`../PSS/Faithfulness`); MPSS's is load bearing. `Me-App` also pushes onto
   the stack, and `Me-Fun`/`Me-FOp` extend the context — none of which v1's `Cr-*` rules did.
2. **Contexts carry two kinds of annotation with disjoint lookups.**
3. **Popping an operand binds it by equivalence, not by subtyping** — the parameter *is* the
   operand rather than being bounded by it.

And one thing did **not** change: `push-is-false` still holds. The redesign records the operand
more precisely, but promotion is still not stack-monotone, so the obstruction blocking
`../Embed/TypePreserving`'s `t-ƛ` case survives into MPSS unaltered.
