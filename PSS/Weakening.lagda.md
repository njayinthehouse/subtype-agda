# Context weakening for λ⊲

Neither `PSS/` nor the paper's v1 development has weakening; `PSS/NarrowPoly`'s `Below`
hypothesis needs it, and so do v2's Lemmas 19–22. Inserting a context `Θ` in the middle preserves
subtyping, given that the enlarged extended context is prevalid.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module PSS.Weakening where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.Commutation using (⟶≤-prevalid; ⟶≤-lc)
open import PSS.WellFormed using (fvStack; prevalid-pop)
```

## Domains

```agda
dom-++ : ∀ (Δ Γ : Ctx) → dom (Δ ++ Γ) ≡ dom Δ ++ dom Γ
dom-++ []            Γ = refl
dom-++ ((x , t) ∷ Δ) Γ = cong (x ∷_) (dom-++ Δ Γ)

∈-weaken : ∀ (Δ Θ : Ctx) {Γ y t}
         → (y , t) ∈ (Δ ++ Γ)
         → (y , t) ∈ (Δ ++ Θ ++ Γ)
∈-weaken Δ Θ {Γ} m with ∈-++⁻ Δ m
... | inj₁ p = ∈-++⁺ˡ p
... | inj₂ p = ∈-++⁺ʳ Δ (∈-++⁺ʳ Θ p)

dom-⊑ : ∀ (Δ Θ : Ctx) {Γ} → dom (Δ ++ Γ) ⊑ dom (Δ ++ Θ ++ Γ)
dom-⊑ Δ Θ {Γ} h
  with ∈-++⁻ (dom Δ) (subst (_ ∈_) (dom-++ Δ Γ) h)
... | inj₁ p = subst (_ ∈_) (sym (dom-++ Δ (Θ ++ Γ))) (∈-++⁺ˡ p)
... | inj₂ p = subst (_ ∈_) (sym (dom-++ Δ (Θ ++ Γ)))
                     (∈-++⁺ʳ (dom Δ) (subst (_ ∈_) (sym (dom-++ Θ Γ)) (∈-++⁺ʳ (dom Θ) p)))
```

Adding a context binding under a non-empty stack: strip the stack, add the binding, re-add the
stack — the entries' scoping survives because the domain only grows.

```agda
prevalid-cons : ∀ {Γ' s y α}
              → Γ' ∣ s prevalid → y ∉ dom Γ' → LC α → fv α ⊑ dom Γ'
              → ((y , α) ∷ Γ') ∣ s prevalid
prevalid-cons P-Ctx1               y∉ lα fvα = P-Ctx2 P-Ctx1 y∉ lα fvα
prevalid-cons p@(P-Ctx2 _ _ _ _)   y∉ lα fvα = P-Ctx2 p y∉ lα fvα
prevalid-cons (P-Ctx3 p l f)       y∉ lα fvα =
  P-Ctx3 (prevalid-cons p y∉ lα fvα) l (λ h → there (f h))
```

## Weakening

The enlarged extended context is a hypothesis: prevalidity of a bigger context does not follow
from prevalidity of a smaller one. Binder rules re-pick their fresh name to avoid `dom Θ`.

```agda
⊲-weaken  : ∀ (Δ Θ : Ctx) {Γ s p q}
          → (Δ ++ Θ ++ Γ) ∣ s prevalid
          → (Δ ++ Γ) ∣ s ⊢ p ≤ q
          → (Δ ++ Θ ++ Γ) ∣ s ⊢ p ≤ q

⟶≤-weaken : ∀ (Δ Θ : Ctx) {Γ s v v'}
          → (Δ ++ Θ ++ Γ) ∣ s prevalid
          → (Δ ++ Γ) ∣ s ⊢ v ⟶≤ v'
          → (Δ ++ Θ ++ Γ) ∣ s ⊢ v ⟶≤ v'

⊲-weaken Δ Θ pv (As-Refl _)       = As-Refl pv
⊲-weaken Δ Θ pv (As-Right d e)    = As-Right (⊲-weaken Δ Θ pv d) e
⊲-weaken Δ Θ pv (As-Left-1 st d)  = As-Left-1 (⟶≤-weaken Δ Θ pv st) (⊲-weaken Δ Θ pv d)

⟶≤-weaken Δ Θ pv (Srs-Prom _ m) = Srs-Prom pv (∈-weaken Δ Θ m)
⟶≤-weaken Δ Θ pv (Srs-Top _)    = Srs-Top pv
⟶≤-weaken Δ Θ pv (Srs-Eq _ e)   = Srs-Eq pv e

⟶≤-weaken Δ Θ {Γ} {s} pv (Srs-App {v = v} st) =
  Srs-App (⟶≤-weaken Δ Θ (P-Ctx3 pv lv fvv) st)
  where
    inner = ⟶≤-prevalid st
    lv  : LC v
    lv  = head-lc inner
      where
        head-lc : ∀ {Γ₀ s₀ α} → Γ₀ ∣ (α ∷ s₀) prevalid → LC α
        head-lc (P-Ctx3 _ l _) = l
    fvv : fv v ⊑ dom (Δ ++ Θ ++ Γ)
    fvv h = dom-⊑ Δ Θ (head-fv inner h)
      where
        head-fv : ∀ {Γ₀ s₀ α} → Γ₀ ∣ (α ∷ s₀) prevalid → fv α ⊑ dom Γ₀
        head-fv (P-Ctx3 _ _ f) = f

⟶≤-weaken Δ Θ {Γ} pv (Srs-Fun {t = t} {u} {u'} L F) =
  Srs-Fun (L ++ dom (Δ ++ Θ ++ Γ)) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , t) ∷ Δ ++ Θ ++ Γ) ∣ [] ⊢ (u ^ fvar y) ⟶≤ (u' ^ fvar y)
    body {y} y∉ = ⟶≤-weaken ((y , t) ∷ Δ) Θ pv' (F (∉-++ˡ y∉))
      where
        inner = ⟶≤-prevalid (F (∉-++ˡ y∉))
        lt : LC t
        lt = head-lc inner
          where
            head-lc : ∀ {Γ₀} → ((y , t) ∷ Γ₀) ∣ [] prevalid → LC t
            head-lc (P-Ctx2 _ _ l _) = l
        fvt : fv t ⊑ dom (Δ ++ Θ ++ Γ)
        fvt h = dom-⊑ Δ Θ (head-fv inner h)
          where
            head-fv : ∀ {Γ₀} → ((y , t) ∷ Γ₀) ∣ [] prevalid → fv t ⊑ dom Γ₀
            head-fv (P-Ctx2 _ _ _ f) = f
        pv' : ((y , t) ∷ Δ ++ Θ ++ Γ) ∣ [] prevalid
        pv' = P-Ctx2 pv (∉-++ʳ L y∉) lt fvt

⟶≤-weaken Δ Θ {Γ} pv (Srs-FunOp {s = s} {α} {t = t} {u} {u'} L F) =
  Srs-FunOp (L ++ dom (Δ ++ Θ ++ Γ)) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , α) ∷ Δ ++ Θ ++ Γ) ∣ s ⊢ (u ^ fvar y) ⟶≤ (u' ^ fvar y)
    body {y} y∉ = ⟶≤-weaken ((y , α) ∷ Δ) Θ pv' (F (∉-++ˡ y∉))
      where
        lα : LC α
        lα = head-lc pv
          where
            head-lc : ∀ {Γ₀} → Γ₀ ∣ (α ∷ s) prevalid → LC α
            head-lc (P-Ctx3 _ l _) = l
        fvα : fv α ⊑ dom (Δ ++ Θ ++ Γ)
        fvα = head-fv pv
          where
            head-fv : ∀ {Γ₀} → Γ₀ ∣ (α ∷ s) prevalid → fv α ⊑ dom Γ₀
            head-fv (P-Ctx3 _ _ f) = f
        pv' : ((y , α) ∷ Δ ++ Θ ++ Γ) ∣ s prevalid
        pv' = prevalid-cons (prevalid-pop pv) (∉-++ʳ L y∉) lα fvα
```

## What this establishes

**Context weakening for λ⊲**, for both the promotion step and the subtyping relation:

> `⊲-weaken : ∀ Δ Θ → (Δ ++ Θ ++ Γ) ∣ s prevalid → (Δ ++ Γ) ∣ s ⊢ p ≤ q → (Δ ++ Θ ++ Γ) ∣ s ⊢ p ≤ q`

Prevalidity of the enlarged extended context is a hypothesis rather than a consequence — a bigger
context is not automatically prevalid. The binder rules re-pick their fresh name to avoid
`dom Θ`, which is the only place the proof does anything beyond threading.

`prevalid-cons` is the small piece that makes the binder cases work under a non-empty stack:
prevalidity puts context bindings only at the empty stack, so adding one means stripping the
stack and re-adding it, which is sound because the domain only grows.

This is the λ⊲ counterpart of v2's Lemmas 19–22, and it is what `PSS/NarrowPoly`'s `Below`
hypothesis needs in order to be established from a fact about the base context.
