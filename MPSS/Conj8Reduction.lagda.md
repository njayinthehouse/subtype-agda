# MPSS: Conjecture 8 reduced to lifting one promotion under an application

`MPSS/Conjecture8Star` reduces the conjecture, over a covariant context, to three pieces:
weakening, the abstraction congruence, and the application congruence for a single
well-subtyping layer. Weakening is Lemma 19 (`MPSS/Weakening`); the abstraction congruence is
`MPSS/CoFun`. This module takes the last piece one step further, mechanizing the layer walk
that `Conjecture8Star` left in prose: a `≤wf` layer between well-formed terms is a chain of
equivalence steps and promotion steps on the left meeting a chain of equivalence steps on the
right, and every one of them lifts to the applied terms — an equivalence step by `pushᵉ` and
`Me-App`, a promotion by whatever lifts it. So the application congruence, and with it the
conjecture in the form `MPSS/Assumed` declares (no local-closure premise on the context), rests
on **one obligation**:

> `StepLift`: a single promotion `Γ;nil ⊢ a ⟶≤ a′` between well-formed terms, with `a v` and
> `a′ v` well-formed, gives `Γ ⊢ a v ≤*wf a′ v`.

Its `Ms-Pro`, `Ms-Top` and `Ms-Equ` instances are immediate. `Ms-App` pushes its premise one
stack deeper, and `Ms-Fun` promotes under the binder that the operand is about to be bound to —
that pair is the conjecture's content, and `MPSS/Push` and `MPSS/CONJ8.md` say what it costs.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conj8Reduction where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.StackPush using (⟶ᵉ-refl; pushᵉ)
open import MPSS.Weakening using (⊑*wf-weaken)
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug; op-wf)
open import MPSS.Conjecture8Star using (AppCongr*; AppCongr₁; appcongr-from; app-wf-mid)
open import MPSS.CoNarrow using (openCo; plug-open; coSize; coSize-open)
open import MPSS.CoFun using (FunCongr)
open import MPSS.Assumed using (Conj-8)
open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ)
```

## The obligation

```agda
StepLift : Set
StepLift = ∀ {Γ a a' v}
         → Γ ⊢ a wf → Γ ∣ [] ⊢ a ⟶ˢ a' → Γ ⊢ a' wf
         → Γ ⊢ app a v wf → Γ ⊢ app a' v wf
         → Γ ⊢ app a v ⊑*wf[ sub-m ] app a' v
```

## A layer as two chains

The left chain keeps the well-formedness that `Ws-Lf2` records at its promotion points; the
right chain is equivalence steps from the target down to the meeting point.

```agda
infix 3 _⊢_⇝_
data _⊢_⇝_ (Γ : Ctx) : Tm → Tm → Set where
  lp-end : ∀ {c} → Γ ⊢ c ⇝ c
  lp-e   : ∀ {a a₁ c} → Γ ∣ [] ⊢ a ⟶ᵉ a₁ → Γ ⊢ a₁ ⇝ c → Γ ⊢ a ⇝ c
  lp-s   : ∀ {a a₁ c} → Γ ⊢ a wf → Γ ∣ [] ⊢ a ⟶ˢ a₁ → Γ ⊢ a₁ wf → Γ ⊢ a₁ ⇝ c → Γ ⊢ a ⇝ c

infix 3 _∣_⊢_⟶ᵉ*_
data _∣_⊢_⟶ᵉ*_ : Ctx → Stack → Tm → Tm → Set where
  εᵉ   : ∀ {Γ s a} → Γ ∣ s ⊢ a ⟶ᵉ* a
  _◅ᵉ_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ b → Γ ∣ s ⊢ b ⟶ᵉ* c → Γ ∣ s ⊢ a ⟶ᵉ* c

split : ∀ {Γ a t} → Γ ⊢ a ⊑wf[ sub-m ] t
      → ∃[ c ] ((Γ ⊢ a ⇝ c) × (Γ ∣ [] ⊢ t ⟶ᵉ* c))
split (Ws-Rfl _)        = _ , lp-end , εᵉ
split (Ws-Lf1 e d)      with split d
... | c , L , R         = c , lp-e e L , R
split (Ws-Lf2 w e w' d) with split d
... | c , L , R         = c , lp-s w e w' L , R
split (Ws-Rgh d e)      with split d
... | c , L , R         = c , L , e ◅ᵉ R
```

Rebuilding a layer from a point of the left chain onward, which is how a middle point is shown
below the target.

```agda
rebuild : ∀ {Γ a c t} → Γ prevalid → Γ ⊢ a ⇝ c → Γ ∣ [] ⊢ t ⟶ᵉ* c → Γ ⊢ a ⊑wf[ sub-m ] t
rebuild {Γ} pv lp-end      R = rgh R
  where
    rgh : ∀ {c t} → Γ ∣ [] ⊢ t ⟶ᵉ* c → Γ ⊢ c ⊑wf[ sub-m ] t
    rgh εᵉ        = Ws-Rfl pv
    rgh (e ◅ᵉ R)  = Ws-Rgh (rgh R) e
rebuild pv (lp-e e L)      R = Ws-Lf1 e (rebuild pv L R)
rebuild pv (lp-s w e w' L) R = Ws-Lf2 w e w' (rebuild pv L R)
```

## Lifting the two kinds of equivalence step to the applied terms

```agda
app-e : ∀ {Γ a a₁ v} → Γ ⊢ v wf → Γ ∣ [] ⊢ a ⟶ᵉ a₁ → Γ ∣ [] ⊢ app a v ⟶ᵉ app a₁ v
app-e wv e = Me-App (pushᵉ e (Pv-Sta (Pv-Nil pvΓ) lv fvv)) (⟶ᵉ-refl (Pv-Nil pvΓ) lv fvv)
  where
    pvΓ = wf⇒prevalid wv
    lv  = wf⇒lc wv
    fvv = wf-fv wv

app-e* : ∀ {Γ t c v} → Γ ⊢ v wf → Γ ∣ [] ⊢ t ⟶ᵉ* c → Γ ∣ [] ⊢ app t v ⟶ᵉ* app c v
app-e* wv εᵉ       = εᵉ
app-e* wv (e ◅ᵉ R) = app-e wv e ◅ᵉ app-e* wv R

arg-wf : ∀ {Γ f v} → Γ ⊢ app f v wf → Γ ⊢ v wf
arg-wf (Wf-App _ d₂) = ⊑*wf⇒wfˡ d₂
```

## The walk

From a well-formed point `a` of the left chain, whose application is well-formed, to the
target. Equivalence steps are gathered into one layer until the next promotion point, whose
application is well-formed because the point is below the target; the promotion is lifted by
the obligation; and the last stretch, together with the whole right chain, is one layer.

```agda
module _ (lift : StepLift) where

  walk : ∀ {Γ a c t v}
       → Γ ⊢ a wf → Γ ⊢ app a v wf
       → Γ ⊢ a ⇝ c → Γ ∣ [] ⊢ t ⟶ᵉ* c
       → Γ ⊢ t wf → Γ ⊢ app t v wf
       → Γ ⊢ app a v ⊑*wf[ sub-m ] app t v
  walk {Γ} {a} {c} {t} {v} wa wav L R wt wtv = go wa wav L
    where
      pvΓ = wf⇒prevalid wa
      wv  = arg-wf wav
      -- the right chain, lifted, closes the layer that reaches the meeting point
      rgh : ∀ {p q} → Γ ∣ [] ⊢ q ⟶ᵉ* p → Γ ⊢ p ⊑wf[ sub-m ] q
      rgh εᵉ       = Ws-Rfl pvΓ
      rgh (e ◅ᵉ S) = Ws-Rgh (rgh S) e
      -- gather equivalence steps up to the next promotion point, or to the end
      go : ∀ {b} → Γ ⊢ b wf → Γ ⊢ app b v wf → Γ ⊢ b ⇝ c
         → Γ ⊢ app b v ⊑*wf[ sub-m ] app t v
      go {b} wb wbv L′ = gather wbv L′ (λ ℓ → ℓ)
        where
          -- `k` rebuilds the layer from `b` to the current point out of the gathered steps
          gather : ∀ {p} → Γ ⊢ app b v wf → Γ ⊢ p ⇝ c
                 → (∀ {q} → Γ ⊢ app p v ⊑wf[ sub-m ] q → Γ ⊢ app b v ⊑wf[ sub-m ] q)
                 → Γ ⊢ app b v ⊑*wf[ sub-m ] app t v
          gather wbv′ lp-end k            = Ws-Sub wbv′ (k (rgh (app-e* wv R))) wtv
          gather wbv′ (lp-e e L″) k       = gather wbv′ L″ (λ ℓ → k (Ws-Lf1 (app-e wv e) ℓ))
          gather {p} wbv′ (lp-s wp e wp′ L″) k =
            Ws-Trs (Ws-Sub wbv′ (k (Ws-Rfl pvΓ)) wpv)
                   wpv
                   (Ws-Trs (lift wp e wp′ wpv wp′v) wp′v (go wp′ wp′v L″))
            where
              wpv  = app-wf-mid (Ws-Sub wp (rebuild pvΓ (lp-s wp e wp′ L″) R) wt) wp wtv
              wp′v = app-wf-mid (Ws-Sub wp′ (rebuild pvΓ L″ R) wt) wp′ wtv
```

## The application congruence, and the conjecture

```agda
  appcongr₁ : AppCongr₁
  appcongr₁ {Γ} wf d wf′ w w′ with split d
  ... | c , L , R = walk wf w L R wf′ w′

  appcongr : AppCongr*
  appcongr = appcongr-from appcongr₁
```

The context induction, on the context's depth, which opening the context at a fresh name
preserves — so no local-closure premise on the context is needed, and the statement is
`MPSS/Assumed`'s `Conj-8` exactly.

```agda
  conj8-n : ∀ n (C : CoCtx) → coSize C ≤ n → ∀ {Γ u t}
          → LC u → LC t
          → Γ ⊢ u ⊑*wf[ sub-m ] t
          → Γ ⊢ plug C u wf → Γ ⊢ plug C t wf
          → Γ ⊢ plug C u ⊑*wf[ sub-m ] plug C t
  conj8-n n ∙ _ lu lt d wu wt = d
  conj8-n (suc n) (co-fun a C) (s≤s le) {Γ} {u} {t} lu lt d wu@(Wf-Fun L₁ F₁ wa) wt@(Wf-Fun L₂ F₂ _) =
    FunCongr (L₁ ++ L₂ ++ dom Γ) fam wu wt
    where
      fam : ∀ {x} → x ∉ (L₁ ++ L₂ ++ dom Γ)
          → ((x , sub , a) ∷ Γ) ⊢ (plug C u ^ fvar x) ⊑*wf[ sub-m ] (plug C t ^ fvar x)
      fam {x} x∉ =
        subst₂ (λ p q → ((x , sub , a) ∷ Γ) ⊢ p ⊑*wf[ sub-m ] q)
               (sym (plug-open C 0 x lu)) (sym (plug-open C 0 x lt))
               (conj8-n n (openCo 0 (fvar x) C) (subst (_≤ n) (sym (coSize-open 0 (fvar x) C)) le)
                        lu lt
                        (⊑*wf-weaken [] ((x , sub , a) ∷ []) pv′ d)
                        (subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (plug-open C 0 x lu) (F₁ (∉-++ˡ x∉)))
                        (subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (plug-open C 0 x lt) (F₂ (∉-++ˡ (∉-++ʳ L₁ x∉)))))
        where
          pv′ : ((x , sub , a) ∷ Γ) prevalid
          pv′ = Pv-Ctx (wf⇒prevalid wa) (∉-++ʳ L₂ (∉-++ʳ L₁ x∉)) (wf⇒lc wa) (wf-fv wa)
  conj8-n (suc n) (co-app C v) (s≤s le) lu lt d wu wt =
    appcongr (conj8-n n C le lu lt d (op-wf wu) (op-wf wt)) wu wt

  conj8 : Conj-8
  conj8 C = conj8-n (coSize C) C ≤-refl
```

## What this establishes

`conj8 : StepLift → Conj-8`, with nothing else assumed: Conjecture 8 as `MPSS/Assumed` declares
it — and with it Lemma 7, Lemma 9, Lemma 6, Theorem 5 and type safety
(`MPSS/Preservation17`) — reduces to lifting one promotion between well-formed terms under one
well-formed application. Everything in the reduction is unconditional. The obligation is where
the conjecture's content sits: `MPSS/Push` shows a promotion pushed one operand deeper replays as
a chain provided the operand reaches the annotation at every stack under a narrowed binder, and
`MPSS/ReachFails` shows that reach needs the well-formedness the obligation carries.
