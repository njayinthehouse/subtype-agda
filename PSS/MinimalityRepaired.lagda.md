# Definition 5.2, repaired — and Lemma 5.3

`PSS/Minimal` records that v1's Definition 5.2 is **refutable as printed**: minimality of a
promotion `Γ;s ⊢ uₙ ⟶≤ v` is stated by quantifying over *every* `w` with `Γ;s ⊢ uₙ ⟶≤ w`, and
`Srs-Eq` at a reflexive equivalence step makes `w := uₙ` always available, so minimality would
demand `Γ;s ⊢ v ⟶≤* uₙ` — false whenever `v` is strictly above `uₙ`.

The obvious repair — quantify only over promotions not justified by `Srs-Eq` — is **also
insufficient**, and that is a second defect. `Srs-Fun` can be reflexive on its own: `λt.Top`
promotes to `λt.Top`, because the body `Top` promotes to `Top` by `Srs-Top`, which is a perfectly
proper step. Minimality would then demand `Top ⟶≤* λt.Top`, and `Top` promotes only to `Top`.

What actually works is to exclude promotions that **land back on the subject**. On a normal form
that also excludes every `Srs-Eq` step, since `⟶≡` goes nowhere from a normal form — so this
subsumes the first repair rather than competing with it.

This module records both defects, states the repaired definition, and proves Lemma 5.3 against
it. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module PSS.MinimalityRepaired where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Close using (open-close; close-open; fv-close)
open import PSS.Narrowing using (_∣_⊢_⟶≤*_; εₚ; _◅ₚ_; _⟶≡*_; εₑ; _◅ₑ_)
open import PSS.Congruence using (⟶≤*-app; ⟶≤*-fun-open; ⟶≤*-funop-open)
open import PSS.Commutation using (⟶≤-prevalid; ⟶≤-lc)
open import PSS.WellFormed using (fvStack)
open import PSS.Algorithms using (_∣_⊢_⟶mp_; mp-nf; mp-var; mp-app; mp-fun; mp-funop; mp-top;
                                  mp⇒⟶≤*; ⟶≤*-lc)
open import PSS.MinimalUnique using (bound-unique)
open import PSS.Minimal using (Top-only)
open import PSS.Confluence using (nf-⟶≡*-id)
```

## Proper promotion

Promotion with `Srs-Eq` removed. Everything else is verbatim.

```agda
infix 3 _∣_⊢_⟶≤ᵖ_
data _∣_⊢_⟶≤ᵖ_ : Ctx → Stack → Tm → Tm → Set where

  Pp-Prom  : ∀ {Γ s x t}
           → Γ ∣ s prevalid → x ≤ t ∈ Γ
           → Γ ∣ s ⊢ fvar x ⟶≤ᵖ t

  Pp-Top   : ∀ {Γ s u}
           → Γ ∣ s prevalid
           → Γ ∣ s ⊢ u ⟶≤ᵖ Top

  Pp-App   : ∀ {Γ s u u' v}
           → Γ ∣ (v ∷ s) ⊢ u ⟶≤ᵖ u'
           → Γ ∣ s ⊢ app u v ⟶≤ᵖ app u' v

  Pp-Fun   : ∀ {Γ t u u'} (L : List Name)
           → (∀ {x} → x ∉ L → ((x , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶≤ᵖ (u' ^ fvar x))
           → Γ ∣ [] ⊢ lam t u ⟶≤ᵖ lam t u'

  Pp-FunOp : ∀ {Γ s α t u u'} (L : List Name)
           → (∀ {x} → x ∉ L → ((x , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶≤ᵖ (u' ^ fvar x))
           → Γ ∣ (α ∷ s) ⊢ lam t u ⟶≤ᵖ lam t u'
```

A proper promotion is a promotion.

```agda
⟶≤ᵖ⇒⟶≤ : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶≤ᵖ v → Γ ∣ s ⊢ u ⟶≤ v
⟶≤ᵖ⇒⟶≤ (Pp-Prom pv m)   = Srs-Prom pv m
⟶≤ᵖ⇒⟶≤ (Pp-Top pv)      = Srs-Top pv
⟶≤ᵖ⇒⟶≤ (Pp-App d)       = Srs-App (⟶≤ᵖ⇒⟶≤ d)
⟶≤ᵖ⇒⟶≤ (Pp-Fun L F)     = Srs-Fun L (λ x∉ → ⟶≤ᵖ⇒⟶≤ (F x∉))
⟶≤ᵖ⇒⟶≤ (Pp-FunOp L F)   = Srs-FunOp L (λ x∉ → ⟶≤ᵖ⇒⟶≤ (F x∉))

⟶≤ᵖ-prevalid : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶≤ᵖ v → Γ ∣ s prevalid
⟶≤ᵖ-prevalid d = ⟶≤-prevalid (⟶≤ᵖ⇒⟶≤ d)
```

## Definition 5.2, repaired

Faithful to the printed definition except for the exclusion, and restricted to normal forms —
which is what the paper's own subscript in `uₙ` already says.

```agda
Minimal : Ctx → Stack → Tm → Tm → Set
Minimal Γ s uₙ v = ∀ {w} → Γ ∣ s ⊢ uₙ ⟶≤ w → ¬ (w ≡ uₙ) → Γ ∣ s ⊢ v ⟶≤* w
```

The second defect, mechanized: a proper promotion really can land back on its subject.

```agda
pv-x : ((0 , Top) ∷ []) ∣ [] prevalid
pv-x = P-Ctx2 P-Ctx1 (λ ()) lc-Top (λ ())

reflexive-proper : [] ∣ [] ⊢ lam Top Top ⟶≤ᵖ lam Top Top
reflexive-proper = Pp-Fun (0 ∷ []) (λ {x} _ → Pp-Top (P-Ctx2 P-Ctx1 (λ ()) lc-Top (λ ())))
```

So excluding `Srs-Eq` alone leaves `λTop.Top` promoting to itself, and minimality would demand
`Top ⟶≤* λTop.Top`, which `Top-only` refutes.

## Lemma 5.3

The minimal promotion computed by `⟶mp` is minimal in the repaired sense.

```agda
Top-step : ∀ {Γ s w} → Γ ∣ s ⊢ Top ⟶≤ w → w ≡ Top
Top-step st = Top-only (st ◅ₚ εₚ)

open-inj : ∀ {u v x} → x ∉ fv u → x ∉ fv v → (u ^ fvar x) ≡ (v ^ fvar x) → u ≡ v
open-inj {u} {v} {x} x∉u x∉v e =
  trans (sym (close-open 0 x u x∉u)) (trans (cong (closeRec 0 x) e) (close-open 0 x v x∉v))

Lem-5·3 : ∀ {Γ s uₙ v} → LC uₙ → NF uₙ
        → Γ ∣ s ⊢ uₙ ⟶mp v
        → Minimal Γ s uₙ v

-- Srs-Eq goes nowhere from a normal form, so it is always excluded.
Lem-5·3 lu nf d (Srs-Eq pv e) w≢ = ⊥-elim (w≢ (sym (nf-⟶≡*-id nf (e ◅ₑ εₑ))))

-- Everything promotes to Top, and so does the minimal promotion.
Lem-5·3 lu nf d (Srs-Top pv) w≢ = Srs-Top pv ◅ₚ εₚ

Lem-5·3 lu nf (mp-nf ¬nf _ _ _) _ _ = ⊥-elim (¬nf nf)

Lem-5·3 {v = v} lu nf (mp-var pv m) (Srs-Prom pv' m') w≢ =
  subst (λ z → _ ∣ _ ⊢ v ⟶≤* z) (bound-unique pv m m') εₚ

Lem-5·3 (lc-app lf la) (nf-ne (ne-app ne nv)) (mp-app _ _ d) (Srs-App st) w≢ =
  ⟶≤*-app (Lem-5·3 lf (nf-ne ne) d st (λ e → w≢ (cong (λ z → app z _) e)))

Lem-5·3 lu nf (mp-top {t = t} pv _) (Srs-Fun {u' = e} L F) w≢ =
  ⊥-elim (w≢ (cong (lam t) (open-inj x∉e x∉Top (Top-step (F x∉L)))))
  where
    A    = L ++ fv e
    x    = fresh A
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉e  : x ∉ fv e
    x∉e  = ∉-++ʳ L (fresh-∉ A)
    x∉Top : x ∉ fv Top
    x∉Top ()

Lem-5·3 lu nf (mp-top {t = t} pv _) (Srs-FunOp {u' = e} L F) w≢ =
  ⊥-elim (w≢ (cong (lam t) (open-inj x∉e x∉Top (Top-step (F x∉L)))))
  where
    A    = L ++ fv e
    x    = fresh A
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉e  : x ∉ fv e
    x∉e  = ∉-++ʳ L (fresh-∉ A)
    x∉Top : x ∉ fv Top
    x∉Top ()

Lem-5·3 (lc-lam L₀ lt F₀) (nf-lam L₃ nt N₃)
        (mp-fun {t = t} {u = b} {u' = c} L₁ _ F₁) (Srs-Fun {u' = e} L₂ F₂) w≢ =
  subst (λ z → _ ∣ [] ⊢ lam t c ⟶≤* lam t z) (close-open 0 x e x∉e)
        (⟶≤*-fun-open x x∉t x∉c x∉Γ lcc
                      (Lem-5·3 (F₀ x∉L₀) (N₃ x∉L₃) (F₁ x∉L₁) (F₂ x∉L₂) body≢))
  where
    A   = L₀ ++ L₁ ++ L₂ ++ L₃ ++ fv t ++ fv b ++ fv c ++ fv e ++ dom _
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L₁ r₁
    r₃  = ∉-++ʳ L₂ r₂
    r₄  = ∉-++ʳ L₃ r₃
    r₅  = ∉-++ʳ (fv t) r₄
    r₆  = ∉-++ʳ (fv b) r₅
    r₇  = ∉-++ʳ (fv c) r₆
    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ r₁
    x∉L₂ = ∉-++ˡ r₂
    x∉L₃ = ∉-++ˡ r₃
    x∉t  = ∉-++ˡ r₄
    x∉b  : x ∉ fv b
    x∉b  = ∉-++ˡ r₅
    x∉c  : x ∉ fv c
    x∉c  = ∉-++ˡ r₆
    x∉e  : x ∉ fv e
    x∉e  = ∉-++ˡ r₇
    x∉Γ  = ∉-++ʳ (fv e) r₇

    lcc : LC (c ^ fvar x)
    lcc = ⟶≤*-lc (F₀ x∉L₀) (mp⇒⟶≤* (F₀ x∉L₀) (F₁ x∉L₁))

    body≢ : ¬ ((e ^ fvar x) ≡ (b ^ fvar x))
    body≢ p = w≢ (cong (lam t) (open-inj x∉e x∉b p))

Lem-5·3 (lc-lam L₀ lt F₀) (nf-lam L₃ nt N₃)
        (mp-funop {s = s} {α = α} {t = t} {u = b} {u' = c} L₁ _ F₁)
        (Srs-FunOp {u' = e} L₂ F₂) w≢ =
  subst (λ z → _ ∣ (α ∷ s) ⊢ lam t c ⟶≤* lam t z) (close-open 0 x e x∉e)
        (⟶≤*-funop-open x x∉α x∉c x∉Γ x∉s lcc
                        (Lem-5·3 (F₀ x∉L₀) (N₃ x∉L₃) (F₁ x∉L₁) (F₂ x∉L₂) body≢))
  where
    A   = L₀ ++ L₁ ++ L₂ ++ L₃ ++ fv α ++ fv b ++ fv c ++ fv e ++ dom _ ++ fvStack s
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L₁ r₁
    r₃  = ∉-++ʳ L₂ r₂
    r₄  = ∉-++ʳ L₃ r₃
    r₅  = ∉-++ʳ (fv α) r₄
    r₆  = ∉-++ʳ (fv b) r₅
    r₇  = ∉-++ʳ (fv c) r₆
    r₈  = ∉-++ʳ (fv e) r₇
    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ r₁
    x∉L₂ = ∉-++ˡ r₂
    x∉L₃ = ∉-++ˡ r₃
    x∉α  = ∉-++ˡ r₄
    x∉b  : x ∉ fv b
    x∉b  = ∉-++ˡ r₅
    x∉c  : x ∉ fv c
    x∉c  = ∉-++ˡ r₆
    x∉e  : x ∉ fv e
    x∉e  = ∉-++ˡ r₇
    x∉Γ  = ∉-++ˡ r₈
    x∉s  = ∉-++ʳ (dom _) r₈

    lcc : LC (c ^ fvar x)
    lcc = ⟶≤*-lc (F₀ x∉L₀) (mp⇒⟶≤* (F₀ x∉L₀) (F₁ x∉L₁))

    body≢ : ¬ ((e ^ fvar x) ≡ (b ^ fvar x))
    body≢ p = w≢ (cong (lam t) (open-inj x∉e x∉b p))
```

## What this establishes

**Two defects in v1's Definition 5.2, and a repair that works.**

1. As printed, `Srs-Eq` at a reflexive equivalence step makes the subject its own promotion, so
   minimality is unsatisfiable whenever the minimal promotion is strictly above the subject
   (recorded in `PSS/Minimal`).
2. Excluding `Srs-Eq` is **not enough**: `reflexive-proper` exhibits `λTop.Top` promoting to
   itself by `Srs-Fun`, whose body step `Top ⟶≤ Top` is a perfectly proper `Srs-Top`. Minimality
   would then demand `Top ⟶≤* λTop.Top`, which `Top-only` refutes.

The repair that works is to exclude promotions that land back on the subject. On a normal form —
which is what the paper's own `uₙ` denotes — that subsumes defect 1, since `⟶≡` goes nowhere from
a normal form.

**Lemma 5.3 holds against the repaired definition**: the minimal promotion computed by `⟶mp` is
minimal. The cases are: `Srs-Eq` excluded by normality; `Srs-Top` because everything promotes to
`Top`; `Srs-Prom` by uniqueness of bounds; `Srs-App` and the two binder rules by recursion and
the corresponding `⟶≤*` congruence; and `mp-top` against a binder competitor by showing the
competitor is the subject itself.

`_⟶≤ᵖ_` (promotion without `Srs-Eq`) is retained because it is what makes defect 2 statable.
