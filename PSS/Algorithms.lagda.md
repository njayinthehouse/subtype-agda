# System λ⊲: §5 — the practical algorithms

Figure 6's three judgements: **minimal promotion** `⟶mp`, the **subtyping algorithm** `st`, and
the **well-formedness algorithm** `wfa`. Each is given as an inductive relation, so "the
algorithm terminates and returns yes" is "a derivation exists" — which is why the correctness
theorems split into a soundness half that holds outright and a completeness half that needs the
termination hypothesis the paper states.

Every rule but `mp-nf` requires its source to already be a normal form — Figure 6 writes the
sources with the subscript `n` — which is what makes the six cases mutually exclusive and
minimal promotion deterministic (Lemma 5.1).

Minimal promotion takes a term to the next station on its *minimal superpath*: reduce to normal
form if it is not one, otherwise promote the head — a variable to its bound, an applied
abstraction into its body, and `λx≤tₙ.Top` to `Top`, the top of every path.

Two deviations from the printed rules, both forced by the encoding and neither changing the
relation:

- The neutral-spine rule `x u₁ₙ⋯uₘₙ ⟶mp t u₁ₙ⋯uₘₙ` is split into a base case at the variable
  and a congruence case gated on the operator being neutral. In locally nameless a spine is a
  left-nested `app`, so the recursive form is the natural one and generates the same relation.
- The `Srs-FunOp`-shaped rule is stated with the *remaining* stack `s` in its premise. Figure 6
  prints `nil` there, which cannot be right — the conclusion has stack `α::s`, and the rule
  mirrors `Srs-FunOp`, whose premise keeps `s`.

```agda
{-# OPTIONS --safe #-}

module PSS.Algorithms where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed
open import PSS.Close
open import PSS.Equivalence
open import PSS.Promotion using (prevalid-nil; prevalid-entry-lc)
open import PSS.Scope
open import PSS.Commutation using (⟶≤-prevalid; ⟶≤-lc; fv-stack-head)
open import PSS.Narrowing
open import PSS.Congruence
```

## Figure 6

```agda
infix 3 _∣_⊢_⟶mp_
data _∣_⊢_⟶mp_ : Ctx → Stack → Tm → Tm → Set where

  mp-nf    : ∀ {Γ s u uₙ} → ¬ (NF u) → Γ ∣ s prevalid → u ⟶≡* uₙ → NF uₙ
           → Γ ∣ s ⊢ u ⟶mp uₙ

  mp-var   : ∀ {Γ s x t} → Γ ∣ s prevalid → x ≤ t ∈ Γ
           → Γ ∣ s ⊢ fvar x ⟶mp t

  mp-app   : ∀ {Γ s u u' v} → Neutral u → NF v
           → Γ ∣ (v ∷ s) ⊢ u ⟶mp u'
           → Γ ∣ s ⊢ app u v ⟶mp app u' v

  mp-fun   : ∀ {Γ t u u'} (L : List Name) → NF (lam t u)
           → (∀ {x} → x ∉ L → ((x , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶mp (u' ^ fvar x))
           → Γ ∣ [] ⊢ lam t u ⟶mp lam t u'

  mp-funop : ∀ {Γ s α t u u'} (L : List Name) → NF (lam t u)
           → (∀ {x} → x ∉ L → ((x , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶mp (u' ^ fvar x))
           → Γ ∣ (α ∷ s) ⊢ lam t u ⟶mp lam t u'

  mp-top   : ∀ {Γ s t} → Γ ∣ s prevalid → NF (lam t Top)
           → Γ ∣ s ⊢ lam t Top ⟶mp Top

infix 3 _∣_⊢_⟶mp*_
data _∣_⊢_⟶mp*_ : Ctx → Stack → Tm → Tm → Set where
  εₘ   : ∀ {Γ s t} → Γ ∣ s ⊢ t ⟶mp* t
  _◅ₘ_ : ∀ {Γ s t u v} → Γ ∣ s ⊢ t ⟶mp u → Γ ∣ s ⊢ u ⟶mp* v → Γ ∣ s ⊢ t ⟶mp* v

infix 3 _∣_⊢_st_
data _∣_⊢_st_ : Ctx → Stack → Tm → Tm → Set where
  st-eq   : ∀ {Γ s u t tₙ} → Γ ∣ s ⊢ u st tₙ → t ⟶≡* tₙ → NF tₙ → Γ ∣ s ⊢ u st t
  st-refl : ∀ {Γ s tₙ}     → Γ ∣ s prevalid → NF tₙ → Γ ∣ s ⊢ tₙ st tₙ
  st-step : ∀ {Γ s u u' tₙ} → Γ ∣ s ⊢ u ⟶mp u' → Γ ∣ s ⊢ u' st tₙ → Γ ∣ s ⊢ u st tₙ

infix 3 _∣_⊢_wfa
data _∣_⊢_wfa : Ctx → Stack → Tm → Set where

  A-Top   : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ s ⊢ Top wfa

  A-Var   : ∀ {Γ s x t} → Γ ∣ s prevalid → x ≤ t ∈ Γ → Γ ∣ s ⊢ t wfa
          → Γ ∣ s ⊢ fvar x wfa

  A-Fun   : ∀ {Γ t u} (L : List Name)
          → (∀ {x} → x ∉ L → ((x , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) wfa)
          → Γ ∣ [] ⊢ t wfa
          → Γ ∣ [] ⊢ lam t u wfa

  A-FunOp : ∀ {Γ s α t u} (L : List Name)
          → (∀ {x} → x ∉ L → ((x , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) wfa)
          → Γ ∣ [] ⊢ t wfa
          → Γ ∣ (α ∷ s) ⊢ lam t u wfa

  A-App   : ∀ {Γ s u v tₙ}
          → Γ ∣ (v ∷ s) ⊢ u ⟶mp* lam tₙ Top
          → Γ ∣ [] ⊢ v st tₙ
          → Γ ∣ (v ∷ s) ⊢ u wfa
          → Γ ∣ [] ⊢ v wfa
          → Γ ∣ [] ⊢ tₙ wfa
          → Γ ∣ (v ∷ s) ⊢ lam tₙ Top wfa
          → Γ ∣ s ⊢ app u v wfa
```

## Chains preserve local closure

```agda
⟶≤*-lc : ∀ {Γ s u w} → LC u → Γ ∣ s ⊢ u ⟶≤* w → LC w
⟶≤*-lc lu εₚ        = lu
⟶≤*-lc lu (st ◅ₚ c) = ⟶≤*-lc (⟶≤-lc lu st) c
```

## Minimal promotion is promotion

Lemma 5.3 in the direction that matters for correctness: a minimal-promotion step is a
promotion, so the minimal superpath is a path in `⟶≤`.

```agda
mp⇒⟶≤* : ∀ {Γ s u v} → LC u → Γ ∣ s ⊢ u ⟶mp v → Γ ∣ s ⊢ u ⟶≤* v

mp⇒⟶≤* lu (mp-nf _ pv c _)   = ⟶≡*⇒⟶≤* pv c
mp⇒⟶≤* lu (mp-var pv mem)    = Srs-Prom pv mem ◅ₚ εₚ
mp⇒⟶≤* lu (mp-top pv _)      = Srs-Top pv ◅ₚ εₚ
mp⇒⟶≤* (lc-app lu lv) (mp-app _ _ d) = ⟶≤*-app (mp⇒⟶≤* lu d)

mp⇒⟶≤* {Γ} (lc-lam {t} {u} L₀ lt F₀) (mp-fun {u' = u'} L _ F) = result
  where
    A  = L₀ ++ L ++ fv t ++ fv u ++ fv u' ++ dom Γ
    x  = fresh A
    a∉ = fresh-∉ A

    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ (fv t) r₂
    r₄ = ∉-++ʳ (fv u) r₃

    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉t : x ∉ fv t
    x∉t  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u' : x ∉ fv u'
    x∉u' = ∉-++ˡ r₄
    x∉Γ : x ∉ dom Γ
    x∉Γ  = ∉-++ʳ (fv u') r₄

    inner : ((x , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶≤* (u' ^ fvar x)
    inner = mp⇒⟶≤* (F₀ x∉L₀) (F x∉L)

    result : Γ ∣ [] ⊢ lam t u ⟶≤* lam t u'
    result = subst (λ z → Γ ∣ [] ⊢ lam t u ⟶≤* lam t z)
                   (close-open 0 x u' x∉u')
                   (⟶≤*-fun-open x x∉t x∉u x∉Γ (F₀ x∉L₀) inner)

mp⇒⟶≤* {Γ} {α ∷ s} (lc-lam {t} {u} L₀ lt F₀) (mp-funop {u' = u'} L _ F) = result
  where
    A  = L₀ ++ L ++ fv α ++ fv u ++ fv u' ++ dom Γ ++ fvStack s
    x  = fresh A
    a∉ = fresh-∉ A

    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ (fv α) r₂
    r₄ = ∉-++ʳ (fv u) r₃
    r₅ = ∉-++ʳ (fv u') r₄

    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉α : x ∉ fv α
    x∉α  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u' : x ∉ fv u'
    x∉u' = ∉-++ˡ r₄
    x∉Γ : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ r₅
    x∉s : x ∉ fvStack s
    x∉s  = ∉-++ʳ (dom Γ) r₅

    inner : ((x , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶≤* (u' ^ fvar x)
    inner = mp⇒⟶≤* (F₀ x∉L₀) (F x∉L)

    result : Γ ∣ (α ∷ s) ⊢ lam t u ⟶≤* lam t u'
    result = subst (λ z → Γ ∣ (α ∷ s) ⊢ lam t u ⟶≤* lam t z)
                   (close-open 0 x u' x∉u')
                   (⟶≤*-funop-open {t = t} x x∉α x∉u x∉Γ x∉s (F₀ x∉L₀) inner)

mp-lc : ∀ {Γ s u v} → LC u → Γ ∣ s ⊢ u ⟶mp v → LC v
mp-lc lu d = ⟶≤*-lc lu (mp⇒⟶≤* lu d)

mp*⇒⟶≤* : ∀ {Γ s u v} → LC u → Γ ∣ s ⊢ u ⟶mp* v → Γ ∣ s ⊢ u ⟶≤* v
mp*⇒⟶≤* lu εₘ        = εₚ
mp*⇒⟶≤* lu (d ◅ₘ c)  = mp⇒⟶≤* lu d ++ₚ mp*⇒⟶≤* (mp-lc lu d) c
  where
    _++ₚ_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶≤* b → Γ ∣ s ⊢ b ⟶≤* c → Γ ∣ s ⊢ a ⟶≤* c
    εₚ        ++ₚ q = q
    (st ◅ₚ p) ++ₚ q = st ◅ₚ (p ++ₚ q)
```

## Theorem 5.5 — the subtyping algorithm is sound

```agda
Thm-5·5 : ∀ {Γ s u t} → LC u → Γ ∣ s ⊢ u st t → Γ ∣ s ⊢ u ≤ t
Thm-5·5 lu (st-refl pv _)  = As-Refl pv
Thm-5·5 lu (st-eq d c _)   = ≤-right* (Thm-5·5 lu d) c
Thm-5·5 lu (st-step mp d)  =
  ≤-left* (mp⇒⟶≤* lu mp) (Thm-5·5 (mp-lc lu mp) d)
```

## Theorem 5.6 — the well-formedness algorithm is sound

```agda
Thm-5·6 : ∀ {Γ s u} → LC u → Γ ∣ s ⊢ u wfa → Γ ∣ s ⊢ u wf

Thm-5·6 lu (A-Top pv)         = W-Top pv
Thm-5·6 lu (A-Var pv mem d)   = W-Var pv mem (Thm-5·6 (bound-lc pv mem) d)
  where
    bound-lc : ∀ {Γ s y t} → Γ ∣ s prevalid → (y , t) ∈ Γ → LC t
    bound-lc pv m = prevalid-entry-lc (prevalid-nil pv) m
Thm-5·6 (lc-lam L₀ lt F₀) (A-Fun L F d) =
  W-Fun (L₀ ++ L) (λ {x} x∉ → Thm-5·6 (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
        (Thm-5·6 lt d)
Thm-5·6 (lc-lam L₀ lt F₀) (A-FunOp L F d) =
  W-FunOp (L₀ ++ L) (λ {x} x∉ → Thm-5·6 (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
          (Thm-5·6 lt d)
Thm-5·6 (lc-app lu lv) (A-App path vst wu wv wt wlam) =
  W-App (Wf-Sub (Wf-Rule wu' (Thm-5·6 llam wlam)
                 (⟶≤*⇒≤ (wf⇒prevalid wu') (mp*⇒⟶≤* lu path))))
        (Wf-Sub (Wf-Rule (Thm-5·6 lv wv) (Thm-5·6 ltn wt)
                 (Thm-5·5 lv vst)))
  where
    wu' = Thm-5·6 lu wu

    llam : LC (lam _ Top)
    llam = ⟶≤*-lc lu (mp*⇒⟶≤* lu path)

    ltn = lc-lam₁ llam
```

## What this establishes

Figure 6's three algorithms, and the soundness halves of Theorems 5.5 and 5.6: whatever the
subtyping algorithm accepts really is a subtyping, and whatever the well-formedness algorithm
accepts really is well-formed.

**Owed.** The completeness halves — "if the judgement holds *and the algorithm terminates*, the
algorithm says yes" — need the termination hypothesis as an explicit premise, since λ⊲ is not
normalising and the algorithm reduces its argument to normal form. Also owed: Lemma 5.1
(minimal promotion is unique), Lemma 5.3 in its full minimality form, and Lemma 5.7 with
Theorem 5.8 (the inversion lemma and incremental typechecking).
