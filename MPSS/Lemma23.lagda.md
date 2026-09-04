# MPSS: Lemma 23 — narrowing preserves well-formedness

> **Lemma 23 (Narrowing of context in well-formedness derivation).** If `Γ, x≤t, Γ′ ⊢ u wf` and
> `Γ; nil ⊢ t ⟶≡ t′` and `Γ ⊢ t′ wf`, then `Γ, x≤t′, Γ′ ⊢ u wf`.

The same three mutually recursive functions as Lemma 7, and the same diagram, for the same
reason: a `Ws-Lf2` forces the conclusion to be starred, and starring an equivalence step through
`Ws-Sub` would need the chain's intermediates well-formed, which they need not be.

Narrowing is the easier of the two in one respect and the harder in another. Easier: it changes no
terms, so every case is free of the `subst-open` transport substitution needs. Harder: the
promotion at a `Ws-Lf2` does not survive intact — `Ms-Pro` on the narrowed variable now yields
`t′` instead of `t` — so the step has to be rebuilt, its new target shown well-formed, and the old
target reconnected to it. Those are `MPSS/CoPromote`, `MPSS/CoNarrow` and one `Ws-Rgh`
respectively, and together they are the third conclusion of Lemma 24 that `MPSS/AUDIT` records as
unestablished in the paper.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Lemma23 where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Weakening using (wf-weaken; ⟶ᵉ-weaken)
open import MPSS.Narrowing using (prevalid-narrow; prevalid-narrowˢ; Lem-25)
open import MPSS.SubstDrop using (no-eqv-x)
open import MPSS.Conjecture8 using (CoCtx; co-fun; co-app; plug)
open import MPSS.CoPair using (CoPair; cp-var; cp-fun; cp-app; coOf; co-tgt; cp-retarget)
open import MPSS.CoPromote using (cp-promote)
open import MPSS.CoNarrow using (Co-step′; Co-wf′)
open import MPSS.Narrow24 using (∈-narrow; narrow-split)
open import MPSS.Congruence using (εᵉ; _◅ᵉ_; _++ᵉ_)
open import MPSS.Lemma7 using (Diag; diag; b→c; b'→c; a→a'; rel; assemble; lf1*)

open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ)

import MPSS.Evaluation as Ev
```

## Lemma 23

```agda
module _ {Γ₀ : Ctx} {x : Name} {t t' : Tm}
         (e : Γ₀ ∣ [] ⊢ t ⟶ᵉ t') (wt' : Γ₀ ⊢ t' wf)
         (lt : LC t) (lt' : LC t') (ft' : fv t' ⊑ dom Γ₀) where

  Old : Ctx → Ctx
  Old Δ = Δ ++ (x , sub , t) ∷ Γ₀

  New : Ctx → Ctx
  New Δ = Δ ++ (x , sub , t') ∷ Γ₀

  x∈New : ∀ (Δ : Ctx) → x ≤ t' ∈ New Δ
  x∈New Δ = ∈-++⁺ʳ Δ (here refl)

  shape : ∀ (Δ : Ctx) → (Δ ++ (x , sub , t') ∷ []) ++ Γ₀ ≡ New Δ
  shape Δ = ++-assoc Δ ((x , sub , t') ∷ []) Γ₀

  Lem-23 : ∀ (Δ : Ctx) {u} → Old Δ ⊢ u wf → New Δ ⊢ u wf

  ⊑*wf-narrow : ∀ (Δ : Ctx) {a b}
              → Old Δ ⊢ a ⊑*wf[ sub-m ] b
              → New Δ ⊢ a ⊑*wf[ sub-m ] b

  aux : ∀ (Δ : Ctx) {a b} → Old Δ ⊢ a ⊑wf[ sub-m ] b → Diag (New Δ) a b
```

**The main induction.** No term moves, so every case is the same rule with a narrowed context. The
narrowed variable itself is well-formed on the strength of its new annotation.

```agda
  Lem-23 Δ {fvar y} (Wf-PrS pv m) = go (x ≟ y)
    where
      pv' = prevalid-narrow Δ lt' ft' pv
      go : Dec (x ≡ y) → New Δ ⊢ fvar y wf
      go (yes refl) = Wf-PrS pv' (x∈New Δ)
      go (no q)     = Wf-PrS pv' (∈-narrow Δ (λ p → q (sym p)) m)

  Lem-23 Δ {fvar y} (Wf-PrE pv m) = go (x ≟ y)
    where
      pv' = prevalid-narrow Δ lt' ft' pv
      go : Dec (x ≡ y) → New Δ ⊢ fvar y wf
      go (yes refl) = ⊥-elim (no-eqv-x Δ pv m)
      go (no q)     = Wf-PrE pv' (∈-narrow Δ (λ p → q (sym p)) m)

  Lem-23 Δ (Wf-Top pv) = Wf-Top (prevalid-narrow Δ lt' ft' pv)

  Lem-23 Δ {lam w u} (Wf-Fun L F ww) =
    Wf-Fun L (λ {z} z∉ → Lem-23 ((z , sub , w) ∷ Δ) (F z∉)) (Lem-23 Δ ww)

  Lem-23 Δ (Wf-App d₁ d₂) = Wf-App (⊑*wf-narrow Δ d₁) (⊑*wf-narrow Δ d₂)

  ⊑*wf-narrow Δ (Ws-Sub w d w')  = assemble (Lem-23 Δ w) (Lem-23 Δ w') (aux Δ d)
  ⊑*wf-narrow Δ (Ws-Trs d₁ w d₂) =
    Ws-Trs (⊑*wf-narrow Δ d₁) (Lem-23 Δ w) (⊑*wf-narrow Δ d₂)
```

**The sub-induction.** `Ws-Lf1` and `Ws-Rgh` transfer verbatim by Lemma 25 — narrowing a subtype
annotation is invisible to `⟶≡`. `Ws-Lf2` is where the work is.

```agda
  aux Δ (Ws-Rfl pv) = diag (εᵉ pv') (εᵉ pv') (εᵉ pv') (inj₁ refl)
    where pv' = Pv-Nil (prevalid-narrow Δ lt' ft' pv)

  aux Δ (Ws-Lf1 e₀ d) with aux Δ d
  ... | diag bc b'c aa' r = diag bc b'c (Lem-25 Δ e e₀ ◅ᵉ aa') r

  aux Δ (Ws-Rgh d e₀) with aux Δ d
  ... | diag bc b'c aa' r = diag (Lem-25 Δ e e₀ ◅ᵉ bc) b'c aa' r

  aux Δ {a} {b} (Ws-Lf2 wa st wa₀ d) with aux Δ d
  ... | diag {A'} {B'} {C} bc b'c a₀a' r = build r
    where
      wA  = Lem-23 Δ wa
      wA₀ = Lem-23 Δ wa₀
      pv  = wf⇒prevalid wA
      pvn = Pv-Nil pv
```

The narrowed promotion. Off the covariant pattern it survives untouched; on it the target moves
from `Co[t]` to `Co[t′]`, and the three pieces are the rebuilt promotion, its well-formedness, and
the equivalence step that reconnects the old target to the new one.

```agda
      eN : New Δ ∣ [] ⊢ t ⟶ᵉ t'
      eN = subst (λ Θ → Θ ∣ [] ⊢ t ⟶ᵉ t')
                 (shape Δ)
                 (⟶ᵉ-weaken [] (Δ ++ (x , sub , t') ∷ [])
                            (subst (λ Θ → Θ ∣ [] prevalid) (sym (shape Δ)) pvn) e)

      wt'N : New Δ ⊢ t' wf
      wt'N = subst (λ Θ → Θ ⊢ t' wf) (shape Δ)
                   (wf-weaken [] (Δ ++ (x , sub , t') ∷ [])
                              (subst _prevalid (sym (shape Δ)) pv) wt')

      a≤a₀ : New Δ ⊢ a ⊑*wf[ sub-m ] _
      a≤a₀ with narrow-split Δ e st
      ... | inj₂ stN = Ws-Sub wA (Ws-Lf2 wA stN wA₀ (Ws-Rfl pv)) wA₀
      ... | inj₁ c   = Ws-Sub wA (Ws-Lf2 wA promo wCt' (Ws-Rgh (Ws-Rfl pv) step)) wA₀
        where
          wCt : New Δ ⊢ plug (coOf c) t wf
          wCt = subst (λ q → New Δ ⊢ q wf) (co-tgt c) wA₀

          wCt' : New Δ ⊢ plug (coOf c) t' wf
          wCt' = Co-wf′ (coOf c) wCt eN wt'N lt lt'

          step : New Δ ∣ [] ⊢ _ ⟶ᵉ plug (coOf c) t'
          step = subst (λ q → New Δ ∣ [] ⊢ q ⟶ᵉ plug (coOf c) t')
                       (sym (co-tgt c))
                       (Co-step′ (coOf c) wCt eN lt lt')

          promo : New Δ ∣ [] ⊢ a ⟶ˢ plug (coOf c) t'
          promo = cp-promote (cp-retarget c) (wf⇒lc wA) (wf-fv wA) lt' (x∈New Δ) pvn

      build : (A' ≡ B') ⊎ (New Δ ⊢ A' ⊑*wf[ sub-m ] B')
            → Diag (New Δ) a b
      build (inj₁ refl) = diag bc (a₀a' ++ᵉ b'c) (εᵉ pvn) (inj₂ a≤a₀)
      build (inj₂ rr)   =
        diag bc b'c (εᵉ pvn) (inj₂ (Ws-Trs (Ws-Trs a≤a₀ wA₀ a₀≤A') wA' rr))
        where
          wA'   = ⊑*wf⇒wfˡ rr
          a₀≤A' = Ws-Sub wA₀ (lf1* a₀a' (Ws-Rfl pv)) wA'
```

## The form Lemma 6 needs

```agda
Lem-23-holds : Ev.Lem-23
Lem-23-holds Δ w wt e wt' =
  Lem-23 e wt' (wf⇒lc wt) (wf⇒lc wt') (wf-fv wt') Δ w
```

## What this establishes

Lemma 23, unconditionally, and `Lem-23-holds`, which discharges `MPSS/Evaluation`'s last
hypothesis. Preservation now rests on Lemmas 1 and 2, Conjecture 8, and the repaired
Proposition 17 — and of those only the conjecture is one the paper flags.
