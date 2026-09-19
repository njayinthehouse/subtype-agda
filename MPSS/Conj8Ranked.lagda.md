# MPSS: Conjecture 8 over contexts with well-formed annotations, if every well-formed term is ranked

From the fundamental lemma (`MPSS/Fundamental`), by induction on the covariant context:

- the hole: `u ≤*wf t` is good, by the fundamental lemma at the identity substitution — which is
  good because the context's annotations are well-formed;
- an operand: goodness is closed under application to a good operand, and the operand is good at
  the domain by the fundamental lemma on the derivation `Wf-App` holds;
- an abstraction: the chain under the binder, by `FunCongr`, and the fundamental lemma again.

**The hypothesis `rk` — every well-formed term is ranked — is false in full MPSS**
(`MPSS/CONJ8.md` §14), so as it stands this is a statement about the argument, not about MPSS:
the reducibility proof closes, and what is left is to relativize it to a class of terms that is
ranked and closed under what the proof uses. With `MPSS/WfCtxSafety` the same hypothesis gives
Lemmas 7 and 6 and Theorem 5 over such contexts.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

open import MPSS.WellFormed
open import MPSS.DomainOrder using (Ranked)

module MPSS.Conj8Ranked (rk : ∀ {Γ T} → Γ ⊢ T wf → Ranked Γ T) where

open import Data.Nat.Base using (ℕ; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst; subst₂)

open import MPSS.GoodAt rk
open import MPSS.GoodSubst rk
open import MPSS.Fundamental rk
open import MPSS.WfCtx using (WfCtx; wc-sub; WfCtx⇒prevalid; Conj-8ʷᶜ; Lem-6ʷᶜ; Preservationʷᶜ)
open import MPSS.WfCtxSafety using (lem-6ʷᶜ; preservationʷᶜ)
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug; op-wf)
open import MPSS.CoNarrow using (openCo; plug-open; coSize; coSize-open)
open import MPSS.CoFun using (FunCongr)
open import MPSS.Weakening using (⊑*wf-weaken)
open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ)
```

```agda
good : ∀ {Γ a b} → WfCtx Γ → Γ ⊢ a ≤*wf b → G Γ a b
good c d = proj₂ (FL-sub d) (mor-id c)

conj8-n : ∀ n (C : CoCtx) → coSize C ≤ n → ∀ {Γ u t}
        → WfCtx Γ → LC u → LC t → Γ ⊢ u ≤*wf t
        → Γ ⊢ plug C u wf → Γ ⊢ plug C t wf
        → G Γ (plug C u) (plug C t)
conj8-n n ∙ _ c lu lt d wu wt = good c d
conj8-n (suc n) (co-fun a C) (s≤s le) {Γ} {u} {t} c lu lt d wu@(Wf-Fun L₁ F₁ wa) wt@(Wf-Fun L₂ F₂ _) =
  good c (FunCongr (L₁ ++ L₂ ++ dom Γ) fam wu wt)
  where
    fam : ∀ {x} → x ∉ (L₁ ++ L₂ ++ dom Γ)
        → ((x , sub , a) ∷ Γ) ⊢ (plug C u ^ fvar x) ≤*wf (plug C t ^ fvar x)
    fam {x} x∉ =
      subst₂ (λ p q → ((x , sub , a) ∷ Γ) ⊢ p ≤*wf q)
             (sym (plug-open C 0 x lu)) (sym (plug-open C 0 x lt))
             (G-≤ (conj8-n n (openCo 0 (fvar x) C)
                           (subst (_≤ n) (sym (coSize-open 0 (fvar x) C)) le)
                           c′ lu lt
                           (⊑*wf-weaken [] ((x , sub , a) ∷ []) (WfCtx⇒prevalid c′) d)
                           (subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (plug-open C 0 x lu) (F₁ (∉-++ˡ x∉)))
                           (subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (plug-open C 0 x lt) (F₂ (∉-++ˡ (∉-++ʳ L₁ x∉))))))
      where
        c′ : WfCtx ((x , sub , a) ∷ Γ)
        c′ = wc-sub c (∉-++ʳ L₂ (∉-++ʳ L₁ x∉)) wa
conj8-n (suc n) (co-app C v) (s≤s le) c lu lt d wu wt@(Wf-App e dv) =
  G-app (conj8-n n C le c lu lt d (op-wf wu) (op-wf wt)) wt e (good c dv)

conj-8ʷᶜ : Conj-8ʷᶜ
conj-8ʷᶜ C c lu lt d wu wt = G-≤ (conj8-n (coSize C) C ≤-refl c lu lt d wu wt)

lemma-6ʷᶜ : Lem-6ʷᶜ
lemma-6ʷᶜ = lem-6ʷᶜ conj-8ʷᶜ

theorem-5ʷᶜ : Preservationʷᶜ
theorem-5ʷᶜ = preservationʷᶜ conj-8ʷᶜ
```

## What this establishes

`rk → Conj-8ʷᶜ`, and with `MPSS/WfCtxSafety`, `rk → Lem-6ʷᶜ` and `rk → Preservationʷᶜ`. The
reducibility argument closes. Its hypothesis is false in full MPSS, so the theorem about a
calculus is still owed: the argument has to be relativized to a class of terms in which
well-formed terms are ranked, closed under substitution by members, the two reductions, subterms
and application — the simply-kinded terms are the candidate.
