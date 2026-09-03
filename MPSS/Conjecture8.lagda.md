# Attacking Conjecture 8

v2 proves Progress (Theorem 4) and Preservation (Theorem 5) **conditionally**, on one unproved
assumption, and says so plainly:

> "All in all, type safety, which is the combination of progress (Theorem 4) and preservation
> (Theorem 5), holds under the assumption that Conjecture 8 holds. … Establishing this conjecture
> is the final step towards a complete proof of type safety."

> **Conjecture 8 (Well-subtyping is context independent).** Let `Γ` be a logical context and `u`,
> `t` terms such that `Γ ⊢ u ≤wf t`. Let `Co` be a covariant context such that both `Co[u]` and
> `Co[t]` are well-formed in `Γ`. We conjecture that `Γ ⊢ Co[u] ≤wf Co[t]`.

And they say why they need it, which is the part that matters here:

> "**Our subtyping relation in MPSS is context-dependent, unlike in PSS where it isn't**, which
> implies that Lemma 7 relies on the conjecture…"

So the redesign that fixed commutativity is what opened this gap.

**Correction (2026-09-02).** The blockquote above and the statement `Conjecture8` below are
over the single-layer relation `≤wf`. v2 prints the conjecture over the **transitive** relation
`≤*wf` — "Γ ⊢ u ≤*wf t … we conjecture that Γ ⊢ Co[u] ≤*wf Co[t]" — and Lemma 9 consumes it in
that form. The two are not interchangeable. `MPSS/Conjecture8Star` restates it as printed and
redoes the decomposition; this module is kept as the record of the earlier statement, and its
`CoCtx` machinery is reused there.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conjecture8 where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import PSS.Syntax using (open-lc-id)
```

## Covariant contexts

> `Co ::= □ | λx≤t. Co | Co t`

The hole in `λx≤t. Co` sits under a binder. Only locally closed terms are ever plugged, so they
mention nothing that binder binds and plugging stays structural.

```agda
data CoCtx : Set where
  ∙      : CoCtx
  co-fun : Tm → CoCtx → CoCtx
  co-app : CoCtx → Tm → CoCtx

plug : CoCtx → Tm → Tm
plug ∙            u = u
plug (co-fun t C) u = lam t (plug C u)
plug (co-app C v) u = app (plug C u) v

data CoLC : CoCtx → Set where
  colc-∙   : CoLC ∙
  colc-fun : ∀ {t C} → LC t → CoLC C → CoLC (co-fun t C)
  colc-app : ∀ {C v} → CoLC C → LC v → CoLC (co-app C v)

plug-lc : ∀ C {u} → CoLC C → LC u → LC (plug C u)
plug-lc ∙ _ lu = lu
plug-lc (co-fun t C) (colc-fun lt cc) lu = lc-lam [] lt body
  where
    lb : LC (plug C _)
    lb = plug-lc C cc lu

    body : ∀ {x} → x ∉ [] → LC ((plug C _) ^ fvar x)
    body {x} _ = subst LC (open-lc-id lb 0 (fvar x)) lb
plug-lc (co-app C v) (colc-app cc lv) lu = lc-app (plug-lc C cc lu) lv
```

## The statement

The local-closure premises are the usual locally nameless hygiene, of exactly the kind
`../PSS/Faithfulness` proves inert for v1's judgements: in the paper's named presentation every
term is a term by construction.

```agda
Conjecture8 : Set
Conjecture8 = ∀ {Γ u t} (C : CoCtx)
            → CoLC C → LC u → LC t
            → Γ ⊢ u ≤wf t
            → Γ ⊢ plug C u wf
            → Γ ⊢ plug C t wf
            → Γ ⊢ plug C u ≤wf plug C t
```

## The decomposition

One piece per context former. `Weakening` carries the burden of building the extended context,
so the induction itself needs no scoping theory.

```agda
Weakening : Set
Weakening = ∀ {Γ x a u t}
          → x ∉ dom Γ → Γ ⊢ a wf
          → Γ ⊢ u ≤wf t
          → ((x , sub , a) ∷ Γ) ⊢ u ≤wf t

FunCongr : Set
FunCongr = ∀ {Γ a b b'} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , sub , a) ∷ Γ) ⊢ b ≤wf b')
         → Γ ⊢ lam a b ≤wf lam a b'

AppCongr : Set
AppCongr = ∀ {Γ f f' v}
         → Γ ⊢ f ≤wf f'
         → Γ ⊢ app f v wf → Γ ⊢ app f' v wf
         → Γ ⊢ app f v ≤wf app f' v
```

Given the three, the conjecture follows by induction on the context. The hole case *is* the
hypothesis; the binder case is weakening then the abstraction congruence; the application case is
the application congruence.

```agda
op-wf : ∀ {Γ f v} → Γ ⊢ app f v wf → Γ ⊢ f wf
op-wf (Wf-App d₁ _) = ⊑*wf⇒wfˡ d₁

conj8-from : Weakening → FunCongr → AppCongr → Conjecture8

conj8-from wk fc ac ∙ _ _ _ d wfu wft = d

conj8-from wk fc ac {Γ} {u} {t} (co-fun a C) (colc-fun la cc) lu lt d wfu wft =
  go wfu wft
  where
    go : Γ ⊢ lam a (plug C u) wf → Γ ⊢ lam a (plug C t) wf
       → Γ ⊢ lam a (plug C u) ≤wf lam a (plug C t)
    go (Wf-Fun L₁ F₁ da) (Wf-Fun L₂ F₂ _) = fc (L₁ ++ L₂ ++ dom Γ) fam
      where
        fam : ∀ {x} → x ∉ (L₁ ++ L₂ ++ dom Γ)
            → ((x , sub , a) ∷ Γ) ⊢ plug C u ≤wf plug C t
        fam {x} x∉ =
          conj8-from wk fc ac C cc lu lt
            (wk (∉-++ʳ L₂ (∉-++ʳ L₁ x∉)) da d)
            (subst (λ z → ((x , sub , a) ∷ Γ) ⊢ z wf)
                   (sym (open-lc-id (plug-lc C cc lu) 0 (fvar x)))
                   (F₁ (∉-++ˡ x∉)))
            (subst (λ z → ((x , sub , a) ∷ Γ) ⊢ z wf)
                   (sym (open-lc-id (plug-lc C cc lt) 0 (fvar x)))
                   (F₂ (∉-++ˡ (∉-++ʳ L₁ x∉))))

conj8-from wk fc ac (co-app C v) (colc-app cc lv) lu lt d wfu wft =
  ac (conj8-from wk fc ac C cc lu lt d (op-wf wfu) (op-wf wft)) wfu wft
```

## What this establishes

Conjecture 8 stated in full, and **reduced to three named pieces**. Two of them are routine:
`Weakening` is v2's Lemma 20, and `FunCongr` follows from `Ms-Fun` and `Me-Fun`, which are
congruences at the reduction level.

**`AppCongr` is the crux**, and it is where the difficulty lives. To derive
`Γ ⊢ f v ≤wf f' v` from `Γ ⊢ f ≤wf f'`, the only structural route is `Ms-App`, whose premise sits
at the **pushed** stack `v :: s`, while the hypothesis sits at `nil`. That transport is exactly
what `../MPSS/Diff`'s `push-is-false` refutes.

It does not follow that the conjecture is false, and a first attempt at refuting it fails
instructively. Take `Γ₀ = y ≤ Top`, `f = λx≤y. x`, `f' = λx≤y. y` — the `push-is-false` witness.
For `f v` to be well-formed, `Wf-App` demands `Γ₀ ⊢ v ≤*wf y`, so `v = Top` is excluded and
`v = y` is the natural choice. But then β applies on both sides: `(λx≤y. x) y ⟶ᵉ y` and
`(λx≤y. y) y ⟶ᵉ y`, and the two meet. That is the stack design working as intended — the operand
is known exactly, so promoting the body and contracting the redex agree.

So `AppCongr` must be proved through β rather than through `Ms-App`, which is precisely where it
becomes entangled with v2's Lemma 7 (substitution preserves well-formedness) — the lemma that
depends on Conjecture 8 in the first place. That circularity is the real obstacle, and it is
visible here rather than asserted.
