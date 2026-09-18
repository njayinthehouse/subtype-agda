# MPSS: preservation and type safety from the repaired Proposition 17

`MPSS/Preservation` and `MPSS/Evaluation` prove Proposition 27, Lemma 6 and Theorem 5 from the
assumed `Prop-17ʳ`, which `MPSS/Prop17Refuted` shows is uninhabited. This module re-derives the
three from `Prop-17ʷ` (`MPSS/Prop17Chain`), the chain form through well-formed terms, which is
proved. The proofs are those modules' proofs with the single equivalence step replaced by the
chain: Proposition 27 pushes the well-subtyping derivation forward along it, and Lemma 6 narrows
the body's well-formedness along it. Type safety then rests on Conjecture 8 and nothing else.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Preservation17 where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.Sum.Base using (_⊎_)
open import Data.List.Membership.Propositional using (_∉_)

open import MPSS.WellFormed
open import MPSS.Static using (Lem-15; Lem-16; ⊑*wf⇒wfʳ)
open import MPSS.Unconditional using (Lem-10; Thm-4′)
open import MPSS.Evaluation using (Lem-7₀)
open import MPSS.Lemma7 using (Lem-7₀-holds)
open import MPSS.Assumed using (Conj-8)
open import MPSS.Prop17Chain using (Prop-17ʷ; push-chain; narrow-chain)

open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ)
```

## Proposition 27

```agda
Prop-27ʷ : ∀ {Γ u u' v}
         → Γ ⊢ u ⊑*wf[ sub-m ] v
         → u ↦ u'
         → Γ ⊢ u' wf
         → Γ ⊢ u' ⊑*wf[ sub-m ] v
Prop-27ʷ d st w' = push-chain d (Prop-17ʷ (⊑*wf⇒wfˡ d) st w')
```

## Lemma 6 and Theorem 5

Lemma 6's β case is Lemma 7's, which is where Conjecture 8 enters; the annotation case
narrows along the chain; the application cases are Proposition 27.

```agda
module _ (lem-7 : Lem-7₀) where

  Lem-6ʷ : ∀ {Γ t t'} → Γ ⊢ t wf → t ↦ t' → Γ ⊢ t' wf
  Lem-6ʷ (Wf-App {u = lam a b} {v = c} d₁ d₂) (E-App _ _)
    with ⊑*wf⇒wfˡ d₁ | ⊑*wf⇒wfʳ d₁
  ... | Wf-Fun L F wa | Wf-Fun _ _ wz =
        lem-7 b L F (Ws-Trs d₂ wz (Ws-Sub wz (Lem-16 (Lem-15 (Lem-10 d₁))) wa))
  Lem-6ʷ (Wf-Fun L F wu) (E-Lam-l st) =
    Wf-Fun L (λ {x} x∉ → narrow-chain (F x∉) wu ch) wu'
    where
      wu' = Lem-6ʷ wu st
      ch  = Prop-17ʷ wu st wu'
  Lem-6ʷ (Wf-Fun L F wu) (E-Lam-r L' F') =
    Wf-Fun (L ++ L') (λ {x} x∉ → Lem-6ʷ (F (∉-++ˡ x∉)) (F' (∉-++ʳ L x∉))) wu
  Lem-6ʷ (Wf-App d₁ d₂) (E-App-l st) =
    Wf-App (Prop-27ʷ d₁ st (Lem-6ʷ (⊑*wf⇒wfˡ d₁) st)) d₂
  Lem-6ʷ (Wf-App d₁ d₂) (E-App-r st) =
    Wf-App d₁ (Prop-27ʷ d₂ st (Lem-6ʷ (⊑*wf⇒wfˡ d₂) st))

  Thm-5ʷ : ∀ {Γ t t' u}
         → Γ ⊢ t ⊑*wf[ sub-m ] u
         → t ↦ t'
         → Γ ⊢ t' ⊑*wf[ sub-m ] u
  Thm-5ʷ d st = Prop-27ʷ d st (Lem-6ʷ (⊑*wf⇒wfˡ d) st)
```

## Type safety, from Conjecture 8 alone

```agda
module _ (conj-8 : Conj-8) where

  preservation : ∀ {Γ t t' u}
               → Γ ⊢ t ⊑*wf[ sub-m ] u → t ↦ t' → Γ ⊢ t' ⊑*wf[ sub-m ] u
  preservation = Thm-5ʷ (Lem-7₀-holds conj-8)

  type-safety : (∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t'))
              × (∀ {Γ t t' u} → Γ ⊢ t ⊑*wf[ sub-m ] u → t ↦ t' → Γ ⊢ t' ⊑*wf[ sub-m ] u)
  type-safety = Thm-4′ , preservation
```

## What this establishes

Proposition 27 and, given Lemma 7, Lemma 6 and Theorem 5, with the refuted assumption gone.
Type safety of MPSS — progress and preservation — from exactly Conjecture 8, the paper's own
open problem, and nothing else. `MPSS/Unconditional`'s version, which takes `Prop-17ʳ` as well,
is superseded and left in place.
