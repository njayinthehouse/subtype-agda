# MPSS: a term below the target is well-formed wherever the target is

The side condition of `MPSS/PushWf` at the points of a lifted chain is well-formedness of the
point closed up through its wrappers (`MPSS/Wrapper`). This module proves the fact that supplies
it, for a plain covariant context:

> if Conjecture 8 holds **at the target `t`** — for every `m ≤*wf t` and every covariant context —
> then `plug C t` well-formed and `m ≤*wf t` give `plug C m` well-formed.

By induction on the context. At an application node it is `app-wf-mid`: the conjecture at the
smaller context puts `plug C m` below `plug C t`, which is below the abstraction the application's
well-formedness needs. At a binder it is `Wf-Fun` over the opened context, with the chain
weakened. So in an induction on the rank of the target, the well-formedness of every point of a
chain lifted to a bound `w` comes from the induction hypothesis at `w`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.BelowWf where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Weakening using (⊑*wf-weaken)
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug)
open import MPSS.CoNarrow using (openCo; plug-open; coSize; coSize-open)
open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ)
```

## Conjecture 8 at a target

```agda
C8To : Tm → Set
C8To t = ∀ {Γ m} (C : CoCtx) → LC m
       → Γ ⊢ m ≤*wf t → Γ ⊢ plug C m wf → Γ ⊢ plug C t wf
       → Γ ⊢ plug C m ≤*wf plug C t
```

## Below the target, well-formed

```agda
module _ {t : Tm} (c8 : C8To t) (lt : LC t) where

  below-wf-n : ∀ n (C : CoCtx) → coSize C ≤ n → ∀ {Γ m}
             → LC m → Γ ⊢ m ≤*wf t → Γ ⊢ plug C t wf → Γ ⊢ plug C m wf
  below-wf-n n ∙ _ lm d wt = ⊑*wf⇒wfˡ d
  below-wf-n (suc n) (co-app C v) (s≤s le) lm d (Wf-App d₁ d₂) =
    Wf-App (Ws-Trs (c8 C lm d wm wt′) wt′ d₁) d₂
    where
      wt′ = ⊑*wf⇒wfˡ d₁
      wm  = below-wf-n n C le lm d wt′
  below-wf-n (suc n) (co-fun a C) (s≤s le) {Γ} {m} lm d (Wf-Fun L F wa) =
    Wf-Fun (L ++ dom Γ) body wa
    where
      body : ∀ {x} → x ∉ (L ++ dom Γ) → ((x , sub , a) ∷ Γ) ⊢ (plug C m ^ fvar x) wf
      body {x} x∉ =
        subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (sym (plug-open C 0 x lm))
          (below-wf-n n (openCo 0 (fvar x) C)
                      (subst (_≤ n) (sym (coSize-open 0 (fvar x) C)) le)
                      lm
                      (⊑*wf-weaken [] ((x , sub , a) ∷ []) pv′ d)
                      (subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (plug-open C 0 x lt) (F (∉-++ˡ x∉))))
        where
          pv′ : ((x , sub , a) ∷ Γ) prevalid
          pv′ = Pv-Ctx (wf⇒prevalid wa) (∉-++ʳ L x∉) (wf⇒lc wa) (wf-fv wa)

  below-wf : ∀ (C : CoCtx) {Γ m}
           → LC m → Γ ⊢ m ≤*wf t → Γ ⊢ plug C t wf → Γ ⊢ plug C m wf
  below-wf C = below-wf-n (coSize C) C ≤-refl
```

## What this establishes

`below-wf`: from Conjecture 8 at the target `t`, every `m ≤*wf t` is well-formed in every covariant
context in which `t` is. With `MPSS/Wrapper` this is the side condition at the points of a chain
lifted to `t`, once a generated wrapper is read as a covariant context.
