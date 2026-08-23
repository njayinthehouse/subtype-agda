# System λ⊲: congruence of promotion chains

§5's algorithms promote under binders and inside applications, so their soundness needs
promotion *chains* to be congruent. The application case is immediate from `Srs-App`; the
abstraction cases are the familiar shape — a chain of steps at one fresh name, each closed and
renamed into the cofinite family `Srs-Fun` and `Srs-FunOp` demand.

```agda
{-# OPTIONS --safe #-}

module PSS.Congruence where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed using (fvStack)
open import PSS.Close
open import PSS.Equivalence
open import PSS.Promotion using (prevalid-nil)
open import PSS.Scope
open import PSS.Commutation using (⟶≤-prevalid; ⟶≤-lc)
open import PSS.Rename
open import PSS.Narrowing
```

## Chains and the subtyping relation

```agda
≤-left* : ∀ {Γ s u u' t} → Γ ∣ s ⊢ u ⟶≤* u' → Γ ∣ s ⊢ u' ≤ t → Γ ∣ s ⊢ u ≤ t
≤-left* εₚ         d = d
≤-left* (st ◅ₚ c)  d = As-Left-1 st (≤-left* c d)

≤-right* : ∀ {Γ s u t w} → Γ ∣ s ⊢ u ≤ w → t ⟶≡* w → Γ ∣ s ⊢ u ≤ t
≤-right* d εₑ        = d
≤-right* d (e ◅ₑ c)  = As-Right (≤-right* d c) e

⟶≤*⇒≤ : ∀ {Γ s u w} → Γ ∣ s prevalid → Γ ∣ s ⊢ u ⟶≤* w → Γ ∣ s ⊢ u ≤ w
⟶≤*⇒≤ pv c = ≤-left* c (As-Refl pv)

⟶≡*⇒⟶≤* : ∀ {Γ s u w} → Γ ∣ s prevalid → u ⟶≡* w → Γ ∣ s ⊢ u ⟶≤* w
⟶≡*⇒⟶≤* pv εₑ       = εₚ
⟶≡*⇒⟶≤* pv (e ◅ₑ c) = Srs-Eq pv e ◅ₚ ⟶≡*⇒⟶≤* pv c
```

## Congruence for applications

```agda
⟶≤*-app : ∀ {Γ s u u' v} → Γ ∣ (v ∷ s) ⊢ u ⟶≤* u' → Γ ∣ s ⊢ app u v ⟶≤* app u' v
⟶≤*-app εₚ        = εₚ
⟶≤*-app (st ◅ₚ c) = Srs-App st ◅ₚ ⟶≤*-app c
```

## Congruence under a binder

A chain under the binder becomes a chain of `Srs-Fun` (resp. `Srs-FunOp`) steps: each step is
closed at the chosen name and renamed to the cofinite family the rule demands.

Both ends of the chain are stated *closed*. Stating the source as `u ^ fvar x` instead would
force the recursive call to be transported across `open-close`, and the termination checker
cannot see through that; closing both ends keeps the recursion on the chain itself.

```agda
⟶≤*-fun : ∀ {Γ t u₀ w} x
        → x ∉ fv t → x ∉ dom Γ → LC u₀
        → ((x , t) ∷ Γ) ∣ [] ⊢ u₀ ⟶≤* w
        → Γ ∣ [] ⊢ lam t (closeRec 0 x u₀) ⟶≤* lam t (closeRec 0 x w)
⟶≤*-fun x x∉t x∉Γ lu₀ εₚ = εₚ
⟶≤*-fun {Γ} {t} {u₀} x x∉t x∉Γ lu₀ (_◅ₚ_ {u = u₁} st chain) =
  step ◅ₚ ⟶≤*-fun x x∉t x∉Γ (⟶≤-lc lu₀ st) chain
  where
    st' : ((x , t) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x u₀) ^ fvar x) ⟶≤ u₁
    st' rewrite open-close lu₀ 0 x = st

    step : Γ ∣ [] ⊢ lam t (closeRec 0 x u₀) ⟶≤ lam t (closeRec 0 x u₁)
    step = Srs-Fun (x ∷ dom Γ)
             (λ {y} y∉ → ⟶≤-rename-head {Γ} {[]} {closeRec 0 x u₀} {u₁} {t} x y
                           (∉-tail y∉) (λ p → y∉ (here p)) x∉t (fv-close 0 x u₀)
                           (⟶≤-lc lu₀ st) st' (λ ()))

⟶≤*-funop : ∀ {Γ s α t u₀ w} x
          → x ∉ fv α → x ∉ dom Γ → x ∉ fvStack s → LC u₀
          → ((x , α) ∷ Γ) ∣ s ⊢ u₀ ⟶≤* w
          → Γ ∣ (α ∷ s) ⊢ lam t (closeRec 0 x u₀) ⟶≤* lam t (closeRec 0 x w)
⟶≤*-funop x x∉α x∉Γ x∉s lu₀ εₚ = εₚ
⟶≤*-funop {Γ} {s} {α} {t} {u₀} x x∉α x∉Γ x∉s lu₀ (_◅ₚ_ {u = u₁} st chain) =
  step ◅ₚ ⟶≤*-funop x x∉α x∉Γ x∉s (⟶≤-lc lu₀ st) chain
  where
    st' : ((x , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x u₀) ^ fvar x) ⟶≤ u₁
    st' rewrite open-close lu₀ 0 x = st

    step : Γ ∣ (α ∷ s) ⊢ lam t (closeRec 0 x u₀) ⟶≤ lam t (closeRec 0 x u₁)
    step = Srs-FunOp (x ∷ dom Γ)
             (λ {y} y∉ → ⟶≤-rename-head {Γ} {s} {closeRec 0 x u₀} {u₁} {α} x y
                           (∉-tail y∉) (λ p → y∉ (here p)) x∉α (fv-close 0 x u₀)
                           (⟶≤-lc lu₀ st) st' x∉s)
```

At the call sites the source is opened, so `close-open` puts it back into the closed form.

```agda
⟶≤*-fun-open : ∀ {Γ t u w} x
             → x ∉ fv t → x ∉ fv u → x ∉ dom Γ → LC (u ^ fvar x)
             → ((x , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶≤* w
             → Γ ∣ [] ⊢ lam t u ⟶≤* lam t (closeRec 0 x w)
⟶≤*-fun-open {Γ} {t} {u} {w} x x∉t x∉u x∉Γ lux chain =
  subst (λ z → Γ ∣ [] ⊢ lam t z ⟶≤* lam t (closeRec 0 x w))
        (close-open 0 x u x∉u)
        (⟶≤*-fun x x∉t x∉Γ lux chain)

⟶≤*-funop-open : ∀ {Γ s α t u w} x
               → x ∉ fv α → x ∉ fv u → x ∉ dom Γ → x ∉ fvStack s → LC (u ^ fvar x)
               → ((x , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶≤* w
               → Γ ∣ (α ∷ s) ⊢ lam t u ⟶≤* lam t (closeRec 0 x w)
⟶≤*-funop-open {Γ} {s} {α} {t} {u} {w} x x∉α x∉u x∉Γ x∉s lux chain =
  subst (λ z → Γ ∣ (α ∷ s) ⊢ lam t z ⟶≤* lam t (closeRec 0 x w))
        (close-open 0 x u x∉u)
        (⟶≤*-funop {t = t} x x∉α x∉Γ x∉s lux chain)
```

## What this establishes

Promotion chains are congruent for application and under both abstraction rules — the
infrastructure §5's minimal promotion needs to be sound for `≤`.
