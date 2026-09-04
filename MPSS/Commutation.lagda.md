# MPSS: Lemma 1 from Lemma 2

> **Lemma 1 (`⟶≤` and `⟶≡` strongly commute).** If `Γ;s ⊢ t₀ ⟶≡ t₁` and `Γ;s ⊢ t₀ ⟶≤ t₂`, then
> for any `Γ′;s′` with `Γ;s ↣ Γ′;s′` there is `t₃` with `Γ;s ⊢ t₂ ⟶≡ t₃` and `Γ′;s′ ⊢ t₁ ⟶≤ t₃`.

The paper's proof of Lemma 1 cites Lemma 2, so the two are sequential rather than mutual, and
Lemma 1 can be proved from the diamond as a black box. That is what this module does — **by
induction on the promotion alone**, with no measure anywhere. The diamond absorbs the one case
that would need one.

Each case pays for itself:

| the promotion | how it closes |
| --- | --- |
| `Ms-Equ` | one application of Lemma 2 — this is the only place it is used |
| `Ms-Top` | `⊤` on both sides |
| `Ms-Pro` | the annotation's reduct, read off the context reduction by `↣-sub` |
| `Ms-App` | the induction hypothesis at the pushed stack, which is what `Ct-Stk` is for |
| `Ms-Fun`, `Ms-FOp` | the induction hypothesis under the binder |

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Commutation where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-ctx; ↣-nil; ↣-sub)
open import MPSS.Assumed using (Lem-2)
open import MPSS.TopLemma using (Top-⟶ˢ)
open import MPSS.StackPush using (pushᵉ)
```

## The two things taken as hypotheses

Prevalidity along a reduction is a fact about `↣` alone; `MPSS/CtxReduce` records why it resists
the obvious inductions and is not proved there.

```agda
↣-Prevalid : Set
↣-Prevalid = ∀ {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → Γ ∣ s prevalid → Γ' ∣ s' prevalid
```

The second is one case of the theorem itself, and it is the case the printed β-rule makes
unreachable. `Ms-App` over a redex meets `Me-Bet`, whose body premise sits at `Γ;s` with the
parameter unbound, while the promotion's own body premise sits at `Γ, x ≡ v; s`. The two are in
different contexts, so no induction hypothesis applies to them as they stand; under the repair
that binds the parameter, both sit in the same extended context and the case closes like the
others. `MPSS/AUDIT` records the same obstruction in the diamond's own `Me-App`/`Me-Bet` case.

```agda
Bet-App : Set
Bet-App = ∀ {Γ s Γ' s' w b v t₁ a'}
        → Γ ∣ s ⊢ app (lam w b) v ⟶ᵉ t₁
        → Γ ∣ (v ∷ s) ⊢ lam w b ⟶ˢ a'
        → Γ ∣ s ↣ Γ' ∣ s'
        → ∃[ t₃ ] ((Γ ∣ s ⊢ app a' v ⟶ᵉ t₃) × (Γ' ∣ s' ⊢ t₁ ⟶ˢ t₃))
```

The third is the pair of abstraction cases. Both rules take their body premise cofinitely at the
same extended context, so the induction hypothesis applies inside the family; what the cases cost
is the locally nameless bookkeeping around it — pick a fresh name, close the joined body over it,
and rebuild both cofinite families by renaming. `MPSS/Wrap` has that machinery for a single
relation; these need a variant that also carries the annotation's own step, since `Me-Fun` moves
the annotation where `Ms-Fun` leaves it fixed.

```agda
Fun-Fun : Set
Fun-Fun = ∀ {Γ Γ' w w₁} b b₁ b₂ (L₁ L₂ : List Name)
        → Γ ∣ [] ⊢ w ⟶ᵉ w₁
        → (∀ {x} → x ∉ L₁ → ((x , sub , w) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ (b₁ ^ fvar x))
        → (∀ {x} → x ∉ L₂ → ((x , sub , w) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ˢ (b₂ ^ fvar x))
        → Γ ∣ [] ↣ Γ' ∣ []
        → ∃[ t₃ ] ((Γ ∣ [] ⊢ lam w b₂ ⟶ᵉ t₃) × (Γ' ∣ [] ⊢ lam w₁ b₁ ⟶ˢ t₃))

FOp-FOp : Set
FOp-FOp = ∀ {Γ Γ' s s' α w w₁} b b₁ b₂ (L₁ L₂ : List Name)
        → Γ ∣ [] ⊢ w ⟶ᵉ w₁
        → (∀ {x} → x ∉ L₁ → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ (b₁ ^ fvar x))
        → (∀ {x} → x ∉ L₂ → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ (b₂ ^ fvar x))
        → Γ ∣ (α ∷ s) ↣ Γ' ∣ s'
        → ∃[ t₃ ] ((Γ ∣ (α ∷ s) ⊢ lam w b₂ ⟶ᵉ t₃) × (Γ' ∣ s' ⊢ lam w₁ b₁ ⟶ˢ t₃))
```

## Lemma 1

```agda
module _ (lem-2 : Lem-2) (↣-pv : ↣-Prevalid) (bet-app : Bet-App)
         (fun-fun : Fun-Fun) (fop-fop : FOp-FOp) where

  Lem-1 : ∀ {Γ s Γ' s' t₀ t₁ t₂}
        → Γ ∣ s ⊢ t₀ ⟶ᵉ t₁
        → Γ ∣ s ⊢ t₀ ⟶ˢ t₂
        → Γ ∣ s ↣ Γ' ∣ s'
        → ∃[ t₃ ] ((Γ ∣ s ⊢ t₂ ⟶ᵉ t₃) × (Γ' ∣ s' ⊢ t₁ ⟶ˢ t₃))
```

**`Ms-Top`.** The promotion has already reached `⊤`, which equivalence-reduces only to itself, and
anything promotes to it.

```agda
  Lem-1 e (Ms-Top pv) d = Top , Me-Top pv , Ms-Top (↣-pv d pv)
```

**`Ms-Equ`.** Two equivalence steps out of the same term: exactly the diamond, with `Ct-Refl` on
the side that stays put and the given reduction on the side that moves.

```agda
  Lem-1 e₁ (Ms-Equ pv e₂) d with lem-2 e₂ e₁ Ct-Refl d
  ... | t₃ , eˡ , eʳ = t₃ , eˡ , Ms-Equ (⟶ᵉ-prevalid eʳ) eʳ
```

**`Ms-Pro`.** The promotion reads `x`'s subtype annotation, and `↣-sub` returns its reduct at the empty stack, where `pushᵉ` carries it to the stack in play. The equivalence step out of a variable
is `Me-Var`, which leaves it alone, or `Me-Pro`, which reads an *equivalence* annotation — and a
prevalid context gives each name one annotation of one kind, so the second is impossible. The
paper lists it as a case; it cannot arise.

```agda
  Lem-1 (Me-Var pv) (Ms-Pro pv' m) d with ↣-sub (prevalid-ctx pv') d m
  ... | t' , m' , e' = t' , pushᵉ {s = []} e' pv' , Ms-Pro (↣-pv d pv') m'
  Lem-1 (Me-Pro pv me _) (Ms-Pro pv' ms) d = ⊥-elim (clash (prevalid-ctx pv) me ms)
    where
      clash : ∀ {Γ x α t} → Γ prevalid → x ≐ α ∈ Γ → x ≤ t ∈ Γ → _
      clash (Pv-Ctx pv x∉ _ _) (there me) (here refl) = x∉ (∈-dom me)
      clash (Pv-EqA pv x∉ _ _) (here refl) (there ms) = x∉ (∈-dom ms)
      clash (Pv-Ctx pv _ _ _)  (there me) (there ms)  = clash pv me ms
      clash (Pv-EqA pv _ _ _)  (there me) (there ms)  = clash pv me ms
```

**`Ms-App`.** The operator's premises sit at the pushed stack, and the operand's reduct is what the
target stack must be pushed with — `Ct-Stk` on the given reduction supplies exactly that.

```agda
  Lem-1 (Me-App du dv) (Ms-App st) d with Lem-1 du st (Ct-Stk d dv)
  ... | a₃ , eˡ , stʳ = app a₃ _ , Me-App eˡ dv , Ms-App stʳ
  Lem-1 (Me-TAp pv) (Ms-App st) d with Top-⟶ˢ st
  ... | refl = Top , Me-TAp pv , Ms-Top (↣-pv d pv)
  Lem-1 e@(Me-Bet _ _ _) (Ms-App st) d = bet-app e st d
```

**Under a binder.** Both rules take their body premise cofinitely at the same extended context, so
the induction hypothesis applies inside the family; the annotation and the stack are untouched.

```agda
  Lem-1 (Me-Fun {u = b} {u' = b₁} L₁ dt F₁) (Ms-Fun {u' = b₂} L₂ F₂) d with ↣-nil d
  ... | refl = fun-fun b b₁ b₂ L₁ L₂ dt F₁ F₂ d
  Lem-1 (Me-FOp {u = b} {u' = b₁} L₁ dt F₁) (Ms-FOp {u' = b₂} L₂ F₂) d =
    fop-fop b b₁ b₂ L₁ L₂ dt F₁ F₂ d
```

## What this establishes

**Lemma 1 reduced to Lemma 2 plus four named statements**, by induction on the promotion, with no
measure anywhere. Five of the eight cases are discharged outright, and the paper's own
`Me-Pro`/`Ms-Pro` case is proved vacuous: a prevalid context gives each name one annotation of one
kind, so a variable cannot both promote and unfold.

Of what is left, `↣-Prevalid` is a fact about `↣` alone, `Fun-Fun` and `FOp-FOp` are locally
nameless bookkeeping over an induction hypothesis that does apply, and `Bet-App` is the one with
mathematical content — the case where the printed β-rule puts the two body premises in different
contexts.
