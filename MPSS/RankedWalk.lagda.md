# MPSS: the layer walk, with the lifting asked only below an admissible target

`MPSS/Conj8Reduction` reduces Conjecture 8 to `StepLift`, the lifting of one promotion under one
operand, and takes it for *every* promotion. An induction on the rank of the target can only
offer the lifting for promotions **below a target it has already reached**, so this module redoes
the walk with that much and no more:

> `StepLiftᵀ`: a promotion `a ⟶ˢ a′` between well-formed terms, with `a′ ≤*wf T`, `T v`
> well-formed and the target `T` admissible (`𝒯 Γ T`), lifts under `v`.

The walk already has the suffix `a′ ≤*wf T` in hand — it uses it for the well-formedness of the
applied point — so nothing new is proved, only passed on. The transitive layer is handled by
carrying the rest of the chain to the target along, instead of changing the target to the middle
term as `appcongr-from` does.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.RankedWalk where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.Weakening using (⊑*wf-weaken)
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug; op-wf)
open import MPSS.Conjecture8Star using (app-wf-mid)
open import MPSS.CoNarrow using (openCo; plug-open; coSize; coSize-open)
open import MPSS.CoFun using (FunCongr)
open import MPSS.Conj8Reduction
  using (_⊢_⇝_; lp-end; lp-e; lp-s; _∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; split; rebuild; app-e; app-e*; arg-wf)
open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ)

module _ (𝒯 : Ctx → Tm → Set) where

  StepLiftᵀ : Set
  StepLiftᵀ = ∀ {Γ a a' T v}
            → 𝒯 Γ T → Γ ⊢ a' ≤*wf T → Γ ⊢ app T v wf
            → Γ ⊢ a wf → Γ ∣ [] ⊢ a ⟶ˢ a' → Γ ⊢ a' wf
            → Γ ⊢ app a v wf → Γ ⊢ app a' v wf
            → Γ ⊢ app a v ⊑*wf[ sub-m ] app a' v

  module _ (lift : StepLiftᵀ) where

    -- one layer `a ≤wf t`, where `t` continues to the admissible target `T` by `k`
    walk : ∀ {Γ a c t T v}
         → 𝒯 Γ T → (∀ {p} → Γ ⊢ p ≤*wf t → Γ ⊢ p ≤*wf T) → Γ ⊢ app T v wf
         → Γ ⊢ a wf → Γ ⊢ app a v wf
         → Γ ⊢ a ⇝ c → Γ ∣ [] ⊢ t ⟶ᵉ* c
         → Γ ⊢ t wf → Γ ⊢ app t v wf
         → Γ ⊢ app a v ⊑*wf[ sub-m ] app t v
    walk {Γ} {a} {c} {t} {T} {v} ad k wTv wa wav L R wt wtv = go wa wav L
      where
        pvΓ = wf⇒prevalid wa
        wv  = arg-wf wav
        rgh : ∀ {p q} → Γ ∣ [] ⊢ q ⟶ᵉ* p → Γ ⊢ p ⊑wf[ sub-m ] q
        rgh εᵉ       = Ws-Rfl pvΓ
        rgh (e ◅ᵉ S) = Ws-Rgh (rgh S) e
        go : ∀ {b} → Γ ⊢ b wf → Γ ⊢ app b v wf → Γ ⊢ b ⇝ c
           → Γ ⊢ app b v ⊑*wf[ sub-m ] app t v
        go {b} wb wbv L′ = gather wbv L′ (λ ℓ → ℓ)
          where
            gather : ∀ {p} → Γ ⊢ app b v wf → Γ ⊢ p ⇝ c
                   → (∀ {q} → Γ ⊢ app p v ⊑wf[ sub-m ] q → Γ ⊢ app b v ⊑wf[ sub-m ] q)
                   → Γ ⊢ app b v ⊑*wf[ sub-m ] app t v
            gather wbv′ lp-end k′            = Ws-Sub wbv′ (k′ (rgh (app-e* wv R))) wtv
            gather wbv′ (lp-e e L″) k′       = gather wbv′ L″ (λ ℓ → k′ (Ws-Lf1 (app-e wv e) ℓ))
            gather {p} wbv′ (lp-s wp e wp′ L″) k′ =
              Ws-Trs (Ws-Sub wbv′ (k′ (Ws-Rfl pvΓ)) wpv)
                     wpv
                     (Ws-Trs (lift ad (k p′≤t) wTv wp e wp′ wpv wp′v) wp′v (go wp′ wp′v L″))
              where
                p′≤t = Ws-Sub wp′ (rebuild pvΓ L″ R) wt
                wpv  = app-wf-mid (Ws-Sub wp (rebuild pvΓ (lp-s wp e wp′ L″) R) wt) wp wtv
                wp′v = app-wf-mid p′≤t wp′ wtv

    -- the transitive closure, the rest of the chain carried along
    appcongrᵀ : ∀ {Γ f m T v}
              → 𝒯 Γ T → (∀ {p} → Γ ⊢ p ≤*wf m → Γ ⊢ p ≤*wf T) → Γ ⊢ app T v wf
              → Γ ⊢ f ≤*wf m
              → Γ ⊢ app f v wf → Γ ⊢ app m v wf
              → Γ ⊢ app f v ≤*wf app m v
    appcongrᵀ ad k wTv (Ws-Sub wf d wm) w w′ with split d
    ... | c , L , R = walk ad k wTv wf w L R wm w′
    appcongrᵀ ad k wTv (Ws-Trs d₁ wm′ d₂) w w′ =
      Ws-Trs (appcongrᵀ ad (λ q → k (Ws-Trs q wm′ d₂)) wTv d₁ w wm′v) wm′v
             (appcongrᵀ ad k wTv d₂ wm′v w′)
      where
        wm′v = app-wf-mid d₂ wm′ w′

    -- Conjecture 8 at a pair all of whose prefix targets are admissible
    conj8ᵀ-n : ∀ n (C : CoCtx) → coSize C ≤ n → ∀ {Γ u t}
             → (∀ {Γ′} (C′ : CoCtx) → Γ′ ⊢ plug C′ t wf → 𝒯 Γ′ (plug C′ t))
             → LC u → LC t
             → Γ ⊢ u ⊑*wf[ sub-m ] t
             → Γ ⊢ plug C u wf → Γ ⊢ plug C t wf
             → Γ ⊢ plug C u ⊑*wf[ sub-m ] plug C t
    conj8ᵀ-n n ∙ _ ad lu lt d wu wt = d
    conj8ᵀ-n (suc n) (co-fun a C) (s≤s le) {Γ} {u} {t} ad lu lt d wu@(Wf-Fun L₁ F₁ wa) wt@(Wf-Fun L₂ F₂ _) =
      FunCongr (L₁ ++ L₂ ++ dom Γ) fam wu wt
      where
        fam : ∀ {x} → x ∉ (L₁ ++ L₂ ++ dom Γ)
            → ((x , sub , a) ∷ Γ) ⊢ (plug C u ^ fvar x) ⊑*wf[ sub-m ] (plug C t ^ fvar x)
        fam {x} x∉ =
          subst₂ (λ p q → ((x , sub , a) ∷ Γ) ⊢ p ⊑*wf[ sub-m ] q)
                 (sym (plug-open C 0 x lu)) (sym (plug-open C 0 x lt))
                 (conj8ᵀ-n n (openCo 0 (fvar x) C) (subst (_≤ n) (sym (coSize-open 0 (fvar x) C)) le)
                           ad lu lt
                           (⊑*wf-weaken [] ((x , sub , a) ∷ []) pv′ d)
                           (subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (plug-open C 0 x lu) (F₁ (∉-++ˡ x∉)))
                           (subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (plug-open C 0 x lt) (F₂ (∉-++ˡ (∉-++ʳ L₁ x∉)))))
          where
            pv′ : ((x , sub , a) ∷ Γ) prevalid
            pv′ = Pv-Ctx (wf⇒prevalid wa) (∉-++ʳ L₂ (∉-++ʳ L₁ x∉)) (wf⇒lc wa) (wf-fv wa)
    conj8ᵀ-n (suc n) (co-app C v) (s≤s le) ad lu lt d wu wt =
      appcongrᵀ (ad C (op-wf wt)) (λ q → q) wt
                (conj8ᵀ-n n C le ad lu lt d (op-wf wu) (op-wf wt)) wu wt

    conj8ᵀ : ∀ (C : CoCtx) {Γ u t}
           → (∀ {Γ′} (C′ : CoCtx) → Γ′ ⊢ plug C′ t wf → 𝒯 Γ′ (plug C′ t))
           → LC u → LC t
           → Γ ⊢ u ⊑*wf[ sub-m ] t
           → Γ ⊢ plug C u wf → Γ ⊢ plug C t wf
           → Γ ⊢ plug C u ⊑*wf[ sub-m ] plug C t
    conj8ᵀ C = conj8ᵀ-n (coSize C) C ≤-refl
```

## What this establishes

`conj8ᵀ : StepLiftᵀ → …`: Conjecture 8 at every pair whose prefix targets are admissible, from the
lifting of promotions below admissible targets only. With `𝒯` "rank at most `n`" this is the
outer half of the induction on the rank.
