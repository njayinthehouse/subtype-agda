# MPSS: the inversion lemma

> **Lemma 10 (Inversion lemma).** Let `Γ` be a logical context and `λx≤t.u`, `λx≤t′.u′` terms.
> If `Γ ⊢ (λx≤t.u) ≤*wf (λx≤t′.u′)` then `Γ ⊢ t ≡wf t′`.

The paper's route: Proposition 13 turns the static derivation into a machine one, Theorem 3
collapses it to a single step, and the single step is then read off. The last part the paper does
by exhibiting the common reduct `z` and inducting twice on the lengths of the two reduction
sequences that reach it. Here it is one induction on the collapsed derivation, because
`As-Left-1` and `As-Right` *are* those two sequences, interleaved.

The case analysis is exhaustive by construction, and worth naming, since it is the whole content:
out of an abstraction, promotion is `Ms-Top`, `Ms-Equ`, `Ms-Fun` or `Ms-FOp`, and equivalence
reduction is `Me-Fun` or `Me-FOp`. `Ms-Top` is discharged by `Top≰lam`; `Ms-Fun` and `Ms-FOp`
leave the annotation untouched and so contribute nothing; the remaining three each move the
annotation by exactly one equivalence step, which is what `Ws-Lf1` and `Ws-Rgh` consume.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Inversion where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)

open import MPSS.WellFormed
open import MPSS.Static using (⊑wf⇒⊲)
open import MPSS.TopLemma using (Top≰lam)
open import MPSS.Assumed using (Lem-1; Lem-2)
open import MPSS.Transitivity using (Thm-3)
```

## Proposition 13, lifted to the transitive closure

The paper's "by induction on the number of transitivity steps, applying Proposition 13 to each".

```agda
⊑*wf⇒⊲* : ∀ {Γ u m t} → Γ ⊢ u ⊑*wf[ m ] t → Γ ∣ [] ⊢ u ⊲*[ m ] t
⊑*wf⇒⊲* (Ws-Sub _ d _)   = Ast-Sub (⊑wf⇒⊲ d)
⊑*wf⇒⊲* (Ws-Trs d₁ _ d₂) = Ast-Trans (⊑*wf⇒⊲* d₁) (⊑*wf⇒⊲* d₂)
```

## Reading the annotation off a collapsed derivation

```agda
lam-inv : ∀ {Γ s a b c d}
        → Γ ∣ s ⊢ lam a b ⊲[ sub-m ] lam c d
        → Γ ⊢ a ⊑wf[ eqv-m ] c
lam-inv (As-Refl pv)                          = Ws-Rfl (prevalid-ctx pv)
lam-inv (As-Left-1 (Ms-Top _) d)              = ⊥-elim (Top≰lam d)
lam-inv (As-Left-1 (Ms-Equ _ (Me-Fun _ e _)) d) = Ws-Lf1 e (lam-inv d)
lam-inv (As-Left-1 (Ms-Equ _ (Me-FOp _ e _)) d) = Ws-Lf1 e (lam-inv d)
lam-inv (As-Left-1 (Ms-Fun _ _) d)            = lam-inv d
lam-inv (As-Left-1 (Ms-FOp _ _) d)            = lam-inv d
lam-inv (As-Right d (Me-Fun _ e _))           = Ws-Rgh (lam-inv d) e
lam-inv (As-Right d (Me-FOp _ e _))           = Ws-Rgh (lam-inv d) e
```

`Ms-Fun` and `Ms-FOp` promote under the binder and return `λx≤t.u′` with the annotation `t`
literally unchanged, so those two cases are the identity on the annotation — the paper's remark
that the right-hand sequence "consists only of use of the rule `Ms-Fun` or `Ms-Equ` with
`Me-Fun`".

## Lemma 10

```agda
Lem-10 : Lem-1 → Lem-2
       → ∀ {Γ t u t' u'}
       → Γ ⊢ lam t u ⊑*wf[ sub-m ] lam t' u'
       → Γ ⊢ t ⊑wf[ eqv-m ] t'
Lem-10 lem-1 lem-2 d = lam-inv (Thm-3 lem-1 lem-2 (⊑*wf⇒⊲* d))
```

## What this establishes

`lam-inv`, which is Lemma 10 for the collapsed machine relation and needs no assumption at all,
and `Lem-10` itself, which is the paper's statement and inherits only Lemmas 1 and 2 through
Theorem 3. Also `⊑*wf⇒⊲*`, Proposition 13 on the transitive closure.
