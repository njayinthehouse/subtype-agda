# Narrowing a bound, when the new bound is below the old at every stack

`PSS/BoundedNarrowing` refutes the F<:-shaped narrowing lemma: `P ≤ Q` at the *empty* stack is
not enough, because promotion is not stack-monotone. The refutation leaves one route open, and
this module takes it — require the hypothesis `P ≤ Q` **at every stack and every context
extension**, which is exactly what a stack-indexed theorem can supply.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module PSS.NarrowPoly where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.Transitivity using (⊲-trans)
open import PSS.Commutation using (⟶≤-prevalid; ⟶≤-lc)
open import PSS.Equivalence using (⟶≡-lc)
open import PSS.Close using (open-close; close-open; fv-close)
open import PSS.Diamond using (close-rename)
open import PSS.Narrowing using (_∣_⊢_⟶≤*_; εₚ; _◅ₚ_; _⟶≡*_; εₑ; _◅ₑ_; ⊲⇒diag; diag⇒⊲)
open import PSS.Congruence using (⟶≤*-app; ⟶≤*-fun-open; ⟶≤*-funop-open)
open import PSS.WellFormed using (fvStack; prevalid-pop)
open import PSS.Algorithms using (⟶≤*-lc)
```

## Domains and lookups are unchanged by narrowing

```agda
dom-++ : ∀ (Δ Γ : Ctx) → dom (Δ ++ Γ) ≡ dom Δ ++ dom Γ
dom-++ []            Γ = refl
dom-++ ((x , t) ∷ Δ) Γ = cong (x ∷_) (dom-++ Δ Γ)

dom-narrow : ∀ (Δ : Ctx) {Γ x P Q}
           → dom (Δ ++ (x , Q) ∷ Γ) ≡ dom (Δ ++ (x , P) ∷ Γ)
dom-narrow Δ {Γ} {x} {P} {Q} =
  trans (dom-++ Δ ((x , Q) ∷ Γ)) (sym (dom-++ Δ ((x , P) ∷ Γ)))

∈-narrow : ∀ (Δ : Ctx) {Γ x P Q y t}
         → (y , t) ∈ (Δ ++ (x , Q) ∷ Γ)
         → ((y , t) ∈ (Δ ++ (x , P) ∷ Γ)) ⊎ ((y ≡ x) × (t ≡ Q))
∈-narrow Δ {Γ} {x} {P} m with ∈-++⁻ Δ m
... | inj₁ p            = inj₁ (∈-++⁺ˡ p)
... | inj₂ (here refl)  = inj₂ (refl , refl)
... | inj₂ (there p)    = inj₁ (∈-++⁺ʳ Δ (there p))

∈-narrow-head : ∀ (Δ : Ctx) {Γ x P} → (x , P) ∈ (Δ ++ (x , P) ∷ Γ)
∈-narrow-head Δ = ∈-++⁺ʳ Δ (here refl)
```

## Prevalidity transfers

```agda
prevalid-narrow : ∀ (Δ : Ctx) {Γ x P Q s}
                → LC P → fv P ⊑ dom Γ
                → (Δ ++ (x , Q) ∷ Γ) ∣ s prevalid
                → (Δ ++ (x , P) ∷ Γ) ∣ s prevalid
prevalid-narrow []            lP fvP (P-Ctx2 pv x∉ _ _)   = P-Ctx2 pv x∉ lP fvP
prevalid-narrow ((y , t) ∷ Δ) {Γ} {x} {P} {Q} lP fvP (P-Ctx2 pv y∉ lt fvt) =
  P-Ctx2 (prevalid-narrow Δ lP fvP pv)
         (subst (y ∉_) (dom-narrow Δ {Γ} {x} {P} {Q}) y∉)
         lt
         (λ h → subst (_ ∈_) (dom-narrow Δ {Γ} {x} {P} {Q}) (fvt h))
prevalid-narrow Δ {Γ} {x} {P} {Q} lP fvP (P-Ctx3 pv lα fvα) =
  P-Ctx3 (prevalid-narrow Δ lP fvP pv) lα
         (λ h → subst (_ ∈_) (dom-narrow Δ {Γ} {x} {P} {Q}) (fvα h))
```

## The hypothesis

`P` is below `Q` in every context extension and at every stack. This is stronger than the F<:
premise, and `PSS/BoundedNarrowing` shows something stronger is required.

```agda
Below : Ctx → Name → Tm → Tm → Set
Below Γ x P Q = ∀ (Δ' : Ctx) {s'}
              → (Δ' ++ (x , P) ∷ Γ) ∣ s' prevalid
              → (Δ' ++ (x , P) ∷ Γ) ∣ s' ⊢ P ≤ Q
```

## Two congruences the structural cases need

`⟶≤*` congruences already exist in `PSS/Congruence`; the `⟶≡*` side needs building, the same way
`⟶≤*-fun` was — close the join at the chosen name and rename.

```agda
⟶≡*-appˡ : ∀ {u u' v} → u ⟶≡* u' → LC v → app u v ⟶≡* app u' v
⟶≡*-appˡ εₑ       lv = εₑ
⟶≡*-appˡ (e ◅ₑ c) lv = Cr-App e (⟶≡-refl lv) ◅ₑ ⟶≡*-appˡ c lv

⟶≡*-fun : ∀ {t u₀ w} x → LC t → LC u₀
        → u₀ ⟶≡* w
        → lam t (closeRec 0 x u₀) ⟶≡* lam t (closeRec 0 x w)
⟶≡*-fun x lt lu₀ εₑ = εₑ
⟶≡*-fun {t} {u₀} x lt lu₀ (_◅ₑ_ {u = u₁} e c) =
  step ◅ₑ ⟶≡*-fun x lt (⟶≡-lc lu₀ e) c
  where
    lu₁ : LC u₁
    lu₁ = ⟶≡-lc lu₀ e

    e' : ((closeRec 0 x u₀) ^ fvar x) ⟶≡ u₁
    e' rewrite open-close lu₀ 0 x = e

    step : lam t (closeRec 0 x u₀) ⟶≡ lam t (closeRec 0 x u₁)
    step = Cr-Fun [] (⟶≡-refl lt)
             (λ {y} _ → close-rename {closeRec 0 x u₀} {u₁} x y lu₁ (fv-close 0 x u₀) e')

⟶≡*-fun-open : ∀ {t u w} x → x ∉ fv u → LC t → LC (u ^ fvar x)
             → (u ^ fvar x) ⟶≡* w
             → lam t u ⟶≡* lam t (closeRec 0 x w)
⟶≡*-fun-open {t} {u} {w} x x∉u lt lux c =
  subst (λ z → lam t z ⟶≡* lam t (closeRec 0 x w))
        (close-open 0 x u x∉u)
        (⟶≡*-fun x lt lux c)
```

## Narrowing

Every rule but `Srs-Prom` at the narrowed variable transfers verbatim. That one case is where
the hypothesis and transitivity are spent.

```agda
⊲-narrow : ∀ (Δ : Ctx) {Γ x P Q s p q}
         → Below Γ x P Q → LC P → LC Q → fv P ⊑ dom Γ
         → LC p
         → (Δ ++ (x , Q) ∷ Γ) ∣ s ⊢ p ≤ q
         → (Δ ++ (x , P) ∷ Γ) ∣ s ⊢ p ≤ q

⟶≤-narrow : ∀ (Δ : Ctx) {Γ x P Q s v v'}
          → Below Γ x P Q → LC P → LC Q → fv P ⊑ dom Γ
          → LC v
          → (Δ ++ (x , Q) ∷ Γ) ∣ s ⊢ v ⟶≤ v'
          → (Δ ++ (x , P) ∷ Γ) ∣ s ⊢ v ≤ v'

⊲-narrow Δ bel lP lQ fvP lp (As-Refl pv) =
  As-Refl (prevalid-narrow Δ lP fvP pv)
⊲-narrow Δ bel lP lQ fvP lp (As-Right d e) =
  As-Right (⊲-narrow Δ bel lP lQ fvP lp d) e
⊲-narrow Δ {Γ} {x} {P} {Q} bel lP lQ fvP lp (As-Left-1 st d) =
  ⊲-trans lp (⟶≤-lc lp st)
          (⟶≤-narrow Δ bel lP lQ fvP lp st)
          (⊲-narrow Δ bel lP lQ fvP (⟶≤-lc lp st) d)

⟶≤-narrow Δ {Γ} {x} {P} {Q} bel lP lQ fvP lv (Srs-Prom pv m)
  with ∈-narrow Δ {Γ} {x} {P} {Q} m
... | inj₁ m' = As-Left-1 (Srs-Prom pv' m') (As-Refl pv')
  where pv' = prevalid-narrow Δ lP fvP pv
... | inj₂ (refl , refl) =
      As-Left-1 (Srs-Prom pv' (∈-narrow-head Δ)) (bel Δ pv')
  where pv' = prevalid-narrow Δ lP fvP pv

⟶≤-narrow Δ bel lP lQ fvP lv (Srs-Top pv) =
  As-Left-1 (Srs-Top (prevalid-narrow Δ lP fvP pv)) (As-Refl (prevalid-narrow Δ lP fvP pv))
⟶≤-narrow Δ bel lP lQ fvP lv (Srs-Eq pv e) =
  As-Left-1 (Srs-Eq pv' e) (As-Refl pv')
  where pv' = prevalid-narrow Δ lP fvP pv
```

The three structural cases. Each narrows the sub-derivation, reads off the diagonal, and
rebuilds with the matching pair of congruences.

```agda
⟶≤-narrow Δ {Γ} {x} {P} {Q} bel lP lQ fvP (lc-app la lb) (Srs-App {u' = a'} st)
  with ⊲⇒diag (⟶≤-narrow Δ bel lP lQ fvP la st)
... | w , chain , ce =
      diag⇒⊲ (prevalid-narrow Δ lP fvP (prevalid-pop (⟶≤-prevalid st)))
             (⟶≤*-app chain) (⟶≡*-appˡ ce lb)

⟶≤-narrow Δ {Γ} {x} {P} {Q} bel lP lQ fvP
          (lc-lam L₀ lt F₀) (Srs-Fun {t = t} {u = u} {u' = u'} L F) = build
  where
    Γ' = Δ ++ (x , P) ∷ Γ
    A  = L₀ ++ L ++ fv t ++ fv u ++ fv u' ++ dom Γ'
    y  = fresh A
    a∉ = fresh-∉ A
    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ (fv t) r₂
    r₄ = ∉-++ʳ (fv u) r₃

    y∉L₀ = ∉-++ˡ a∉
    y∉L  = ∉-++ˡ r₁
    y∉t  : y ∉ fv t
    y∉t  = ∉-++ˡ r₂
    y∉u  : y ∉ fv u
    y∉u  = ∉-++ˡ r₃
    y∉u' : y ∉ fv u'
    y∉u' = ∉-++ˡ r₄
    y∉Γ' : y ∉ dom Γ'
    y∉Γ' = ∉-++ʳ (fv u') r₄

    inner = ⊲⇒diag (⟶≤-narrow ((y , t) ∷ Δ) bel lP lQ fvP (F₀ y∉L₀) (F y∉L))
    w     = proj₁ inner
    chain = proj₁ (proj₂ inner)
    ce    = proj₂ (proj₂ inner)

    build : Γ' ∣ [] ⊢ lam t u ≤ lam t u'
    build = diag⇒⊲ (prevalid-narrow Δ lP fvP (⟶≤-prevalid (Srs-Fun {t = t} {u = u} {u' = u'} L F)))
                   (⟶≤*-fun-open y y∉t y∉u y∉Γ' (F₀ y∉L₀) chain)
                   (⟶≡*-fun-open y y∉u' lt (⟶≤-lc (F₀ y∉L₀) (F y∉L)) ce)

⟶≤-narrow Δ {Γ} {x} {P} {Q} bel lP lQ fvP
          (lc-lam L₀ lt F₀) (Srs-FunOp {s = s} {α = α} {t = t} {u = u} {u' = u'} L F) = build
  where
    Γ' = Δ ++ (x , P) ∷ Γ
    A  = L₀ ++ L ++ fv α ++ fv u ++ fv u' ++ dom Γ' ++ fvStack s
    y  = fresh A
    a∉ = fresh-∉ A
    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ (fv α) r₂
    r₄ = ∉-++ʳ (fv u) r₃
    r₅ = ∉-++ʳ (fv u') r₄

    y∉L₀ = ∉-++ˡ a∉
    y∉L  = ∉-++ˡ r₁
    y∉α  : y ∉ fv α
    y∉α  = ∉-++ˡ r₂
    y∉u  : y ∉ fv u
    y∉u  = ∉-++ˡ r₃
    y∉u' : y ∉ fv u'
    y∉u' = ∉-++ˡ r₄
    y∉Γ' : y ∉ dom Γ'
    y∉Γ' = ∉-++ˡ r₅
    y∉s  : y ∉ fvStack s
    y∉s  = ∉-++ʳ (dom Γ') r₅

    inner = ⊲⇒diag (⟶≤-narrow ((y , α) ∷ Δ) bel lP lQ fvP (F₀ y∉L₀) (F y∉L))
    w     = proj₁ inner
    chain = proj₁ (proj₂ inner)
    ce    = proj₂ (proj₂ inner)

    build : Γ' ∣ (α ∷ s) ⊢ lam t u ≤ lam t u'
    build = diag⇒⊲ (prevalid-narrow Δ lP fvP (⟶≤-prevalid (Srs-FunOp {s = s} {α = α} {t = t} {u = u} {u' = u'} L F)))
                   (⟶≤*-funop-open y y∉α y∉u y∉Γ' y∉s (F₀ y∉L₀) chain)
                   (⟶≡*-fun-open y y∉u' lt (⟶≤-lc (F₀ y∉L₀) (F y∉L)) ce)
```

## What this establishes

**Narrowing holds for λ⊲ once the hypothesis is stack-polymorphic.**

```
⊲-narrow : Below Γ x P Q → … → (Δ ++ (x , Q) ∷ Γ) ∣ s ⊢ p ≤ q
                             → (Δ ++ (x , P) ∷ Γ) ∣ s ⊢ p ≤ q
```

where `Below Γ x P Q` asks for `P ≤ Q` in **every** context extension and at **every** stack.

`PSS/BoundedNarrowing` shows that strength is necessary: with the hypothesis only at the empty
stack the lemma is false. The witness there fails precisely because `P ≤ Q` was unavailable at
the stack where `Srs-App` needed it — and `Below` supplies it there by construction.

The single case that does real work is `Srs-Prom` at the narrowed variable: under `x ≤ Q` the
variable steps to `Q`, and under `x ≤ P` it steps to `P`, from which `Below` and transitivity
(`⊲-trans`, i.e. Theorem 4.4) recover the rest. Every other case narrows its sub-derivation and
rebuilds with the matching pair of congruences — which is why the `⟶≡*` side had to be built here
alongside the `⟶≤*` congruences that `PSS/Congruence` already had.
