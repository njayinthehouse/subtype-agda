# MPSS: narrowing an annotation, and context reduction at the empty stack

Three of v2's owed obligations.

> **Lemma 36 (Commutativity — context weakening).** If `Γ;s ↣ Γ′;s′` then `Γ;nil ↣ Γ′;nil`.
>
> **Lemma 26 (Narrowing prevalidity).** If `Γ, x⊲t, Γ′; s` is prevalid and `Γ;s ⊢ t ⟶ᵉ t′`, then
> `Γ, x⊲t′, Γ′; s` is prevalid.
>
> **Lemma 25 (Narrowing of context in equivalence reductions).** If `Γ, x≤t, Γ′; s ⊢ u ⟶ᵉ v` and
> `Γ;nil ⊢ t ⟶ᵉ t′`, then `Γ, x≤t′, Γ′ ⊢ u ⟶ᵉ v`.

Lemma 25 is the easy half of narrowing, and it is worth saying why: `Me-Pro` reads only
**equivalence** annotations, and the entry being narrowed is a **subtype** annotation, so no rule
of `⟶ᵉ` consults it. Narrowing is therefore invisible to equivalence reduction, and only
prevalidity has to be rebuilt. Its counterpart for promotion (Lemma 24) is not invisible, because
`Ms-Pro` does read subtype annotations, and that is why the paper has to state it with an
existential.

Contexts are lists with the newest entry first, so the paper's `Γ, x⊲t, Γ′` is `Δ ++ (x,c,t) ∷ Γ`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Narrowing where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Narrow using (Transfer; ⟶ᵉ-transfer)
open import MPSS.Preserve using (fv-⟶ᵉ-dom)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Subst.Base using (dom-++; suffix-prevalid)
open Transfer
```

## Lemma 36

Reducing an extended context reduces the underlying logical context at the empty stack: the
stack rule contributes nothing to the context.

```agda
Lem-36 : ∀ {Γ s Γ′ s′} → Γ ∣ s ↣ Γ′ ∣ s′ → Γ ∣ [] ↣ Γ′ ∣ []
Lem-36 Ct-Refl      = Ct-Refl
Lem-36 (Ct-Ann d e) = Ct-Ann (Lem-36 d) e
Lem-36 (Ct-Stk d e) = Lem-36 d
```

## Lemma 26

Domains are untouched by narrowing, so every scoping side condition survives; the entry itself
needs the new annotation to be a locally closed term scoped in the older part.

```agda
dom-narrow : ∀ (Δ : Ctx) {Γ x c t t′}
           → dom (Δ ++ (x , c , t) ∷ Γ) ≡ dom (Δ ++ (x , c , t′) ∷ Γ)
dom-narrow Δ {Γ} {x} {c} {t} {t′} =
  trans (dom-++ Δ ((x , c , t) ∷ Γ)) (sym (dom-++ Δ ((x , c , t′) ∷ Γ)))

prevalid-narrow : ∀ (Δ : Ctx) {Γ x c t t′}
                → LC t′ → fv t′ ⊑ dom Γ
                → (Δ ++ (x , c , t) ∷ Γ) prevalid
                → (Δ ++ (x , c , t′) ∷ Γ) prevalid
prevalid-narrow [] {c = sub} lt′ ft′ (Pv-Ctx pv x∉ _ _) = Pv-Ctx pv x∉ lt′ ft′
prevalid-narrow [] {c = eqv} lt′ ft′ (Pv-EqA pv x∉ _ _) = Pv-EqA pv x∉ lt′ ft′
prevalid-narrow ((z , sub , w) ∷ Δ) {Γ} {x} {c} {t} {t′} lt′ ft′ (Pv-Ctx pv z∉ lw fw) =
  Pv-Ctx (prevalid-narrow Δ lt′ ft′ pv)
         (subst (z ∉_) (dom-narrow Δ {Γ} {x} {c} {t} {t′}) z∉) lw
         (λ h → subst (_ ∈_) (dom-narrow Δ {Γ} {x} {c} {t} {t′}) (fw h))
prevalid-narrow ((z , eqv , w) ∷ Δ) {Γ} {x} {c} {t} {t′} lt′ ft′ (Pv-EqA pv z∉ lw fw) =
  Pv-EqA (prevalid-narrow Δ lt′ ft′ pv)
         (subst (z ∉_) (dom-narrow Δ {Γ} {x} {c} {t} {t′}) z∉) lw
         (λ h → subst (_ ∈_) (dom-narrow Δ {Γ} {x} {c} {t} {t′}) (fw h))

prevalid-narrowˢ : ∀ (Δ : Ctx) {Γ x c t t′ s}
                 → LC t′ → fv t′ ⊑ dom Γ
                 → (Δ ++ (x , c , t) ∷ Γ) ∣ s prevalid
                 → (Δ ++ (x , c , t′) ∷ Γ) ∣ s prevalid
prevalid-narrowˢ Δ lt′ ft′ (Pv-Nil pv) = Pv-Nil (prevalid-narrow Δ lt′ ft′ pv)
prevalid-narrowˢ Δ {Γ} {x} {c} {t} {t′} lt′ ft′ (Pv-Sta pv lα fα) =
  Pv-Sta (prevalid-narrowˢ Δ lt′ ft′ pv) lα
         (λ h → subst (_ ∈_) (dom-narrow Δ {Γ} {x} {c} {t} {t′}) (fα h))
```

The annotation's replacement is a term scoped in the older part whenever it is a reduct of the
old one, which is `⟶ᵉ-lc` and `fv-⟶ᵉ`.

```agda
ann-lc : ∀ (Δ : Ctx) {Γ x c t} → (Δ ++ (x , c , t) ∷ Γ) prevalid → LC t
ann-lc Δ pv = head-lc (suffix-prevalid Δ pv)

ann-fv : ∀ (Δ : Ctx) {Γ x c t} → (Δ ++ (x , c , t) ∷ Γ) prevalid → fv t ⊑ dom Γ
ann-fv Δ pv = head-fv (suffix-prevalid Δ pv)

Lem-26 : ∀ (Δ : Ctx) {Γ x c t t′ s s′}
       → (Δ ++ (x , c , t) ∷ Γ) ∣ s prevalid
       → Γ ∣ s′ ⊢ t ⟶ᵉ t′
       → (Δ ++ (x , c , t′) ∷ Γ) ∣ s prevalid
Lem-26 Δ pv e =
  prevalid-narrowˢ Δ (⟶ᵉ-lc (ann-lc Δ (prevalid-ctx pv)) e)
                     (fv-⟶ᵉ-dom e (ann-fv Δ (prevalid-ctx pv))) pv
```

## Lemma 25

An equivalence lookup never lands on the narrowed entry, because that entry is a subtype
annotation.

```agda
≐-narrow : ∀ (Δ : Ctx) {Γ x t t′ y β}
         → y ≐ β ∈ (Δ ++ (x , sub , t) ∷ Γ)
         → y ≐ β ∈ (Δ ++ (x , sub , t′) ∷ Γ)
≐-narrow Δ m with ∈-++⁻ Δ m
... | inj₁ p         = ∈-++⁺ˡ p
... | inj₂ (there p) = ∈-++⁺ʳ Δ (there p)

narrow-transfer : ∀ (Δ : Ctx) {Γ x t t′}
                → LC t′ → fv t′ ⊑ dom Γ
                → Transfer (Δ ++ (x , sub , t) ∷ Γ) (Δ ++ (x , sub , t′) ∷ Γ)
narrow-transfer Δ {Γ} {x} {t} {t′} lt′ ft′ = record
  { t-dom = dom-narrow Δ {Γ} {x} {sub} {t} {t′}
  ; t-pv  = prevalid-narrow Δ lt′ ft′
  ; t-≐   = ≐-narrow Δ }

Lem-25 : ∀ (Δ : Ctx) {Γ x t t′ s s′ u v}
       → Γ ∣ s′ ⊢ t ⟶ᵉ t′
       → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v
       → (Δ ++ (x , sub , t′) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v
Lem-25 Δ e d =
  ⟶ᵉ-transfer (narrow-transfer Δ (⟶ᵉ-lc (ann-lc Δ ctx) e)
                                 (fv-⟶ᵉ-dom e (ann-fv Δ ctx))) d
  where ctx = prevalid-ctx (⟶ᵉ-prevalid d)
```

## What this establishes

Lemmas 36, 26 and 25, the last with the observation that narrowing a *subtype* annotation is
invisible to equivalence reduction, since `Me-Pro` reads only equivalence annotations.
