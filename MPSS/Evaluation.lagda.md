# MPSS: Lemma 6 — evaluation preserves well-formedness

> **Lemma 6 (Evaluation preserves well-formedness).** Let `Γ` be a logical context and `t`, `t′`
> terms with `t ↦ t′` and `Γ ⊢ t wf`. Then `Γ ⊢ t′ wf`.

The paper's proof, case by case, with the two results it defers to taken as hypotheses: Lemma 7
(substitution) for the β case and Lemma 23 (narrowing) for the annotation case. Everything else
is discharged here.

The β case is the one that carries the argument. `Wf-App` records the operator below
`λy≤z.Top` and the operand below `z`, while `Wf-Fun` binds the body under the operator's *own*
annotation `u`. Those two annotations are not the same term, so the operand cannot be substituted
until `z` and `u` are related — which is what inversion (Lemma 10) provides, as an equivalence,
and what Lemmas 15 and 16 turn into a subtyping in the direction `Ws-Trs` can use.

Lemma 23 carries the narrowed annotation's own well-formedness as an extra hypothesis. The paper
does not state it, and the case that uses the lemma has it to hand — `Wf-Fun` records exactly
that — so nothing is lost; what it buys is the local closure the locally nameless proof needs.

Lemma 7 is stated here in the form the β case actually needs: the context suffix is empty, and
substitution for the bound variable is opening. That is the same statement, since
`Γ, x≤u ⊢ v wf` with `x` fresh is `(v ^ x)` well-formed and `v[x\w]` is `v ^ w`. The body is an
explicit argument because it occurs only under `openRec`, which is not injective, so leaving it
implicit would make it unsolvable wherever the lemma is passed as a hypothesis.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Evaluation where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Static using (Lem-15; Lem-16; ⊑*wf⇒wfʳ)
open import MPSS.Inversion using (Lem-10)
open import MPSS.Preservation using (Prop-27)
open import MPSS.Assumed using (Lem-1; Lem-2; Prop-17ʳ)

open import PSS.Reduction using (_↦_; E-App; E-Lam-l; E-Lam-r; E-App-l; E-App-r)
```

## The two deferred results, as statements

```agda
Lem-7₀ : Set
Lem-7₀ = ∀ {Γ u w} v (L : List Name)
       → (∀ {x} → x ∉ L → ((x , sub , u) ∷ Γ) ⊢ (v ^ fvar x) wf)
       → Γ ⊢ w ⊑*wf[ sub-m ] u
       → Γ ⊢ (v ^ w) wf

Lem-23 : Set
Lem-23 = ∀ (Δ : Ctx) {Γ x t t' u}
       → (Δ ++ (x , sub , t) ∷ Γ) ⊢ u wf
       → Γ ⊢ t wf
       → Γ ∣ [] ⊢ t ⟶ᵉ t'
       → Γ ⊢ t' wf
       → (Δ ++ (x , sub , t') ∷ Γ) ⊢ u wf
```

## Lemma 6

```agda
module _ (lem-1 : Lem-1) (lem-2 : Lem-2)
         (prop-17 : Prop-17ʳ) (lem-7 : Lem-7₀) (lem-23 : Lem-23) where

  Lem-6 : ∀ {Γ t t'} → Γ ⊢ t wf → t ↦ t' → Γ ⊢ t' wf
```

**β.** Inversion relates the operator's annotation `u` to the domain `z` recorded by `Wf-App`;
symmetry and the equivalence-to-subtyping cast put the operand below `u`, and Lemma 7 substitutes.

```agda
  Lem-6 (Wf-App {u = lam a b} {v = c} d₁ d₂) (E-App _ _)
    with ⊑*wf⇒wfˡ d₁ | ⊑*wf⇒wfʳ d₁
  ... | Wf-Fun L F wa | Wf-Fun _ _ wz =
        lem-7 b L F
          (Ws-Trs d₂ wz (Ws-Sub wz (Lem-16 (Lem-15 (Lem-10 lem-1 lem-2 d₁))) wa))
```

**The annotation of an abstraction.** The step in the annotation is re-read as an equivalence step
by Proposition 17, and Lemma 23 carries the body's derivation across the changed annotation.

```agda
  Lem-6 {Γ} (Wf-Fun L F wu) (E-Lam-l st) =
    Wf-Fun L (λ {x} x∉ → lem-23 [] (F x∉) wu e wu') wu'
    where
      wu' = Lem-6 wu st
      e   = prop-17 (Pv-Nil (wf⇒prevalid wu)) (wf⇒lc wu) (wf-fv wu) st
```

**The body of an abstraction.** The induction hypothesis applies under the binder directly.

```agda
  Lem-6 (Wf-Fun L F wu) (E-Lam-r L' F') =
    Wf-Fun (L ++ L') (λ {x} x∉ → Lem-6 (F (∉-++ˡ x∉)) (F' (∉-++ʳ L x∉))) wu
```

**Applications.** Proposition 27 carries each side's subtyping derivation across its own step.

```agda
  Lem-6 (Wf-App d₁ d₂) (E-App-l st) =
    Wf-App (Prop-27 prop-17 d₁ st (Lem-6 (⊑*wf⇒wfˡ d₁) st)) d₂
  Lem-6 (Wf-App d₁ d₂) (E-App-r st) =
    Wf-App d₁ (Prop-27 prop-17 d₂ st (Lem-6 (⊑*wf⇒wfˡ d₂) st))
```

## What this establishes

Lemma 6, from Lemmas 1, 2, 7 and 23 and the repaired Proposition 17. Composed with
`MPSS/Preservation`, it gives Theorem 5 on the same assumptions — so preservation now rests on
exactly two unproved things beyond commutation: Lemma 7, which is where Conjecture 8 enters, and
Lemma 23.
