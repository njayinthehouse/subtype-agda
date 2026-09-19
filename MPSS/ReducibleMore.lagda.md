# MPSS: reducibility — chains on the left, a change of target, `⊤`, and weakening

`MPSS/Reducible` defines `Good` and closes it under one equivalence step on the left, composition,
and joins of two well-formed terms. The fundamental lemma (`MPSS/CONJ8.md` §17) needs four more
closure properties, proved here:

- a **chain** of equivalence steps on the left, through terms that need not be well-formed;
- a **change of target** to one the old target joins with;
- every well-formed term is good at `⊤`;
- **weakening**: goodness in `Γ` is goodness in `Δ ++ Γ`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.ReducibleMore where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.DomainOrder using (_▷ᵈ_; _◁ᵈ_; ▷-dom; ▷-app; Ranked)
open import MPSS.Reducible
open import MPSS.Weakening using (wf-weaken; ⊑*wf-weaken)
open import MPSS.Conjecture8Star using (app-wf-mid)
open import MPSS.Conj8Reduction using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; app-e*)
open import MPSS.TopLemma using (Top≰lam)
open import MPSS.Unconditional using (Thm-3wf)
```

## A chain of equivalence steps on the left

```agda
expand*-≤ : ∀ {Γ p p′ T} → Γ ⊢ p wf → Γ ∣ [] ⊢ p ⟶ᵉ* p′ → Γ ⊢ p′ wf → Γ ⊢ p′ ≤*wf T → Γ ⊢ p ≤*wf T
expand*-≤ wp L wp′ d =
  Ws-Trs (Ws-Sub wp (lf1* L (Ws-Rfl (wf⇒prevalid wp))) wp′) wp′ d

good-expand* : ∀ {Γ T p p′} (a : Ranked Γ T)
             → Γ ⊢ p wf → Γ ∣ [] ⊢ p ⟶ᵉ* p′ → Good a p′ → Good a p
good-expand* {Γ} {T} {p} {p′} (acc rs) wp L (wp′ , d′ , h) =
  wp , p≤T , λ Δ {v} w e′ gv →
    let r    = h Δ w e′ gv
        pvΔ  = wf⇒prevalid w
        p≤TΔ = ⊑*wf-weaken [] Δ pvΔ p≤T
        wpv  = app-wf-mid p≤TΔ (⊑*wf⇒wfˡ p≤TΔ) w
        Lv   = app-e* (arg-wf′ w) (weaken* Δ pvΔ L)
        ap   = rs (▷-app Δ w)
    in expand*-≤ wpv Lv (good-wf ap (proj₂ r)) (proj₁ r) , good-expand* ap wpv Lv (proj₂ r)
  where
    p≤T = expand*-≤ wp L wp′ d′
```

## A change of target

If the old target `T′` and the new one `T` are well-formed and join by equivalence steps, what is
good at `T′` is good at `T`: `T′` is good at `T` by `good-join`, and goodness composes.

```agda
good-cast : ∀ {Γ T T′ c m} (b : Ranked Γ T′) (a : Ranked Γ T)
          → Γ ⊢ T′ wf → Γ ∣ [] ⊢ T′ ⟶ᵉ* c → Γ ∣ [] ⊢ T ⟶ᵉ* c → Γ ⊢ T wf
          → Good b m → Good a m
good-cast b a wT′ L R wT g = good-trans b a g (good-join a wT′ L R wT)
```

## Every well-formed term is good at `⊤`

`⊤ v` is never well-formed, so the clause about operands is vacuous.

```agda
top-≤ : ∀ {Γ m} → Γ ⊢ m wf → Γ ⊢ m ≤*wf Top
top-≤ wm = Ws-Sub wm (Ws-Lf2 wm (Ms-Top (Pv-Nil pv)) (Wf-Top pv) (Ws-Rfl pv)) (Wf-Top pv)
  where pv = wf⇒prevalid wm

good-top : ∀ {Γ m} (a : Ranked Γ Top) → Γ ⊢ m wf → Good a m
good-top (acc rs) wm = wm , top-≤ wm , λ Δ w e gv → ⊥-elim (Top≰lam (Thm-3wf e))
```

## Weakening

The clause about operands already quantifies over extensions of the context, so weakening is
reassociation: an extension `Δ′` of `Δ ++ Γ` is the extension `Δ′ ++ Δ` of `Γ`.

```agda
good-ctx : ∀ {Γ₁ Γ₂ T m} → Γ₁ ≡ Γ₂ → (a : Ranked Γ₁ T) (b : Ranked Γ₂ T) → Good a m → Good b m
good-ctx refl a b g = good-irr a b g

good-weaken : ∀ (Δ : Ctx) {Γ T m} (a : Ranked Γ T) (b : Ranked (Δ ++ Γ) T)
            → (Δ ++ Γ) prevalid → Good a m → Good b m
good-weaken Δ {Γ} {T} {m} (acc rs) (acc rs′) pv (wm , d , h) =
  wf-weaken [] Δ pv wm , ⊑*wf-weaken [] Δ pv d , λ Δ′ {v} {dd} w e gv →
    let eq  = ++-assoc Δ′ Δ Γ
        w₀  = subst (λ G → G ⊢ app T v wf) (sym eq) w
        e₀  = subst (λ G → G ⊢ T ≤*wf lam dd Top) (sym eq) e
        gv₀ = good-ctx (sym eq) (rs′ (▷-dom Δ′ w e)) (rs (▷-dom (Δ′ ++ Δ) w₀ e₀)) gv
        r   = h (Δ′ ++ Δ) w₀ e₀ gv₀
    in subst (λ G → G ⊢ app m v ≤*wf app T v) eq (proj₁ r)
     , good-ctx eq (rs (▷-app (Δ′ ++ Δ) w₀)) (rs′ (▷-app Δ′ w)) (proj₂ r)
```

## What this establishes

The four closure properties above. With `MPSS/Reducible` these are everything the fundamental
lemma uses about `Good` besides its definition.
