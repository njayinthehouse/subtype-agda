# MPSS: bookkeeping for substitution

Domains, scoping, lookups and prevalidity under substituting a term for a name in a context
split `Δ ++ Γ`, where the name is outside `dom (Δ ++ Γ)`. Separated from `MPSS/Subst` so that the
reduction cases there are not buried in it.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Subst.Base where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Rename using (substCtx; substStack; dom-substCtx; ∈-substCtx)
open import PSS.Syntax using (subst-fresh; subst-lc)
open import PSS.Promotion using (fv-subst)
```

## Domains

```agda
dom-++ : ∀ (Δ Γ : Ctx) → dom (Δ ++ Γ) ≡ dom Δ ++ dom Γ
dom-++ []            Γ = refl
dom-++ ((z , _) ∷ Δ) Γ = cong (z ∷_) (dom-++ Δ Γ)

dom-sub : ∀ (Δ : Ctx) {Γ x v} → dom (substCtx x v Δ ++ Γ) ≡ dom (Δ ++ Γ)
dom-sub Δ {Γ} {x} {v} =
  trans (dom-++ (substCtx x v Δ) Γ)
        (trans (cong (_++ dom Γ) (dom-substCtx x v Δ)) (sym (dom-++ Δ Γ)))

∈-dom-sub : ∀ (Δ : Ctx) {Γ x v y} → y ∈ dom (Δ ++ Γ) → y ∈ dom (substCtx x v Δ ++ Γ)
∈-dom-sub Δ h = subst (_ ∈_) (sym (dom-sub Δ)) h

∉-dom-sub : ∀ (Δ : Ctx) {Γ x v y} → y ∉ dom (Δ ++ Γ) → y ∉ dom (substCtx x v Δ ++ Γ)
∉-dom-sub Δ h k = h (subst (_ ∈_) (dom-sub Δ) k)
```

## Scoping

```agda
⊑-subst : ∀ (Δ : Ctx) {Γ v t} x
        → fv v ⊑ dom Γ → fv t ⊑ dom (Δ ++ Γ)
        → fv (t [ x := v ]) ⊑ dom (substCtx x v Δ ++ Γ)
⊑-subst Δ {Γ} {v} {t} x fvv fvt h with fv-subst x v t h
... | inj₁ (p , _) = ∈-dom-sub Δ (fvt p)
... | inj₂ p       = ∈-dom-sub Δ (subst (_ ∈_) (sym (dom-++ Δ Γ)) (∈-++⁺ʳ (dom Δ) (fvv p)))
```

## Lookups

An entry of `Δ` becomes its substituted self; an entry of `Γ` is unchanged, because `x` occurs in
nothing that `Γ` records.

```agda
suffix-prevalid : ∀ (Δ : Ctx) {Γ} → (Δ ++ Γ) prevalid → Γ prevalid
suffix-prevalid []      pv               = pv
suffix-prevalid (_ ∷ Δ) (Pv-Ctx pv _ _ _) = suffix-prevalid Δ pv
suffix-prevalid (_ ∷ Δ) (Pv-EqA pv _ _ _) = suffix-prevalid Δ pv

∉-fv-Γ : ∀ (Δ : Ctx) {Γ x z b t} → (Δ ++ Γ) prevalid → x ∉ dom (Δ ++ Γ)
       → (z , b , t) ∈ Γ → x ∉ fv t
∉-fv-Γ Δ {Γ} pv x∉ m h =
  x∉ (subst (_ ∈_) (sym (dom-++ Δ Γ))
            (∈-++⁺ʳ (dom Δ) (prevalid-bound-fv (suffix-prevalid Δ pv) m h)))

∈-sub : ∀ (Δ : Ctx) {Γ x v z b t} → (Δ ++ Γ) prevalid → x ∉ dom (Δ ++ Γ)
      → (z , b , t) ∈ (Δ ++ Γ)
      → (z , b , t [ x := v ]) ∈ (substCtx x v Δ ++ Γ)
∈-sub Δ {Γ} {x} {v} {t = t} pv x∉ m with ∈-++⁻ Δ m
... | inj₁ p = ∈-++⁺ˡ (∈-substCtx x v Δ p)
... | inj₂ p = subst (λ w → (_ , _ , w) ∈ (substCtx x v Δ ++ Γ))
                     (sym (subst-fresh {t} x v (∉-fv-Γ Δ pv x∉ p)))
                     (∈-++⁺ʳ (substCtx x v Δ) p)
```

## A name outside the domain does not occur in the stack

```agda
∉-stack : ∀ {Γ s x} → Γ ∣ s prevalid → x ∉ dom Γ → x ∉ fvStack s
∉-stack (Pv-Nil _) x∉ ()
∉-stack {s = α ∷ s} (Pv-Sta pv lα fα) x∉ h with ∈-++⁻ (fv α) h
... | inj₁ p = x∉ (fα p)
... | inj₂ p = ∉-stack pv x∉ p
```

## Prevalidity

```agda
prevalid-ctx-subst : ∀ (Δ : Ctx) {Γ x v}
                   → LC v → fv v ⊑ dom Γ → x ∉ dom (Δ ++ Γ)
                   → (Δ ++ Γ) prevalid
                   → (substCtx x v Δ ++ Γ) prevalid
prevalid-ctx-subst []      lv fvv x∉ pv = pv
prevalid-ctx-subst ((z , sub , t) ∷ Δ) {x = x} lv fvv x∉ (Pv-Ctx pv z∉ lt ft) =
  Pv-Ctx (prevalid-ctx-subst Δ lv fvv (λ h → x∉ (there h)) pv)
         (∉-dom-sub Δ z∉) (subst-lc lt lv) (⊑-subst Δ {t = t} x fvv ft)
prevalid-ctx-subst ((z , eqv , t) ∷ Δ) {x = x} lv fvv x∉ (Pv-EqA pv z∉ lt ft) =
  Pv-EqA (prevalid-ctx-subst Δ lv fvv (λ h → x∉ (there h)) pv)
         (∉-dom-sub Δ z∉) (subst-lc lt lv) (⊑-subst Δ {t = t} x fvv ft)

prevalid-subst : ∀ (Δ : Ctx) {Γ s x v}
               → LC v → fv v ⊑ dom Γ → x ∉ dom (Δ ++ Γ)
               → (Δ ++ Γ) ∣ s prevalid
               → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) prevalid
prevalid-subst Δ lv fvv x∉ (Pv-Nil pv) = Pv-Nil (prevalid-ctx-subst Δ lv fvv x∉ pv)
prevalid-subst Δ {x = x} lv fvv x∉ (Pv-Sta {α = α} pv lα fα) =
  Pv-Sta (prevalid-subst Δ lv fvv x∉ pv) (subst-lc lα lv) (⊑-subst Δ {t = α} x fvv fα)
```

## What this establishes

The bookkeeping `MPSS/Subst` needs: domains are unchanged by substituting in a context, scoped
terms stay scoped, lookups transfer with the entry substituted, a name outside the domain does
not occur in the stack, and prevalidity is preserved.
