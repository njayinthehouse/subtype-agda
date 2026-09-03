# MPSS: Theorem 4 — progress

> **Theorem 4 (Progress).** Let `t` be a term. For every logical context `Γ`, if `Γ ⊢ t wf` then
> either `t` is in normal form, or there exists `t′` with `t ↦ t′`.

The operational semantics and normal forms are shared with v1 — `↦` and `NF` are context-free, so
`PSS/Reduction` defines them once and both systems use them — and so is the renaming machinery
that transports a step found at one fresh name to a cofinite family (`PSS/Progress`). What is new
is the well-formedness derivation being read alongside, and the one place it is consulted.

That place is the application case. With operator and operand both normal, the operator is `Top`,
an abstraction, or neutral. An abstraction gives a β-step and a neutral operator gives a normal
form; `Top` would give a stuck term, and is excluded by Theorem 11 — `Wf-App` demands
`Γ ⊢ u ≤*wf λx≤t.Top`, which `Top` cannot satisfy. Theorem 11 is where the two commutation
assumptions enter, through Theorem 3; the rest of progress needs nothing assumed.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Progress where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

open import MPSS.WellFormed
open import MPSS.Static using (⊑wf⇒⊲)
open import MPSS.Inversion using (⊑*wf⇒⊲*)
open import MPSS.TopLemma using (Top≰lam)
open import MPSS.Assumed using (Lem-1; Lem-2)
open import MPSS.Transitivity using (Thm-3)

open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; closeRec)
open import PSS.Reduction
  using (_↦_; E-App; E-Lam-l; E-Lam-r; E-App-l; E-App-r;
         NF; Neutral; nf-Top; nf-lam; nf-ne; ne-var; ne-app)
open import PSS.Progress using (NF-open-rename; ↦-lc; ↦-close-rename)
```

## Theorem 11, in the form progress needs

`Top` is not below an abstraction in the static system either: push the derivation into the
machine system with Proposition 13, collapse it with Theorem 3, and apply `Top≰lam`.

```agda
Thm-11wf : Lem-1 → Lem-2
         → ∀ {Γ t u} → ¬ (Γ ⊢ Top ⊑*wf[ sub-m ] lam t u)
Thm-11wf lem-1 lem-2 d = Top≰lam (Thm-3 lem-1 lem-2 (⊑*wf⇒⊲* d))
```

## Theorem 4

By induction on local closure, reading the well-formedness derivation alongside it.

```agda
module _ (lem-1 : Lem-1) (lem-2 : Lem-2) where

  Thm-4 : ∀ {Γ t} → LC t → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')

  Thm-4 lc-fvar (Wf-PrS _ _) = inj₁ (nf-ne ne-var)
  Thm-4 lc-fvar (Wf-PrE _ _) = inj₁ (nf-ne ne-var)
  Thm-4 lc-Top  (Wf-Top _)   = inj₁ nf-Top
```

**Abstractions.** Try the annotation first, then the body at one fresh name; a step there is
closed over that name and reopened at an arbitrary one, and likewise for normality.

```agda
  Thm-4 (lc-lam {a} {b} L₀ la F₀) (Wf-Fun L F wa) = result
    where
      A  = L₀ ++ L ++ fv b
      x  = fresh A
      a∉ = fresh-∉ A

      x∉L₀ = ∉-++ˡ a∉
      x∉L  = ∉-++ˡ (∉-++ʳ L₀ a∉)
      x∉b : x ∉ fv b
      x∉b  = ∉-++ʳ L (∉-++ʳ L₀ a∉)

      result : NF (lam a b) ⊎ ∃[ t' ] (lam a b ↦ t')
      result with Thm-4 la wa
      ... | inj₂ (a' , st) = inj₂ (lam a' b , E-Lam-l st)
      ... | inj₁ na with Thm-4 (F₀ x∉L₀) (F x∉L)
      ...   | inj₁ nb = inj₁ (nf-lam [] na (λ {y} _ → NF-open-rename {b} x y x∉b nb))
      ...   | inj₂ (w , stw) =
               inj₂ ( lam a (closeRec 0 x w)
                    , E-Lam-r [] (λ {y} _ →
                        ↦-close-rename {b} {w} x y (↦-lc (F₀ x∉L₀) stw) x∉b stw) )
```

**Applications.** The only case that consults the derivation.

```agda
  Thm-4 (lc-app {u} {v} lu lv) (Wf-App d₁ d₂)
    with Thm-4 lu (⊑*wf⇒wfˡ d₁)
  ... | inj₂ (u' , st)              = inj₂ (app u' v , E-App-l st)
  ... | inj₁ nf-Top                 = ⊥-elim (Thm-11wf lem-1 lem-2 d₁)
  ... | inj₁ (nf-lam {a} {b} _ _ _) = inj₂ ((b ^ v) , E-App lu lv)
  ... | inj₁ (nf-ne ne) with Thm-4 lv (⊑*wf⇒wfˡ d₂)
  ...   | inj₂ (v' , st) = inj₂ (app u v' , E-App-r st)
  ...   | inj₁ nv        = inj₁ (nf-ne (ne-app ne nv))
```

Local closure is recoverable from well-formedness, so the theorem is also available exactly as
the paper states it.

```agda
  Thm-4′ : ∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')
  Thm-4′ w = Thm-4 (wf⇒lc w) w
```

## What this establishes

Theorem 4, from Lemmas 1 and 2 alone — Conjecture 8 and Proposition 17 are not involved. Progress
is therefore the half of type safety that MPSS gets unconditionally once commutation is in hand;
preservation is the half that needs the conjecture and the repaired β-rule.
