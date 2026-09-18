# MPSS: Lemmas 7 and 9 need Conjecture 8 at one pair only

`MPSS/Lemma9` and `MPSS/Lemma7` take the whole of Conjecture 8 as a hypothesis. They use it at a
single pair: the substituend `α` and the bound `t` it replaces, in the contexts that extend the
one `α ≤*wf t` lives in. This module restates both with that hypothesis, `C8At Γ₀ α t`, and
nothing else changes: the proofs are those of the two modules with the call to the conjecture
replaced by the call to the local hypothesis.

It matters for the recursion `MPSS/CONJ8.md` §7–9 describes. `FunLift` for an abstraction
`λx≤t.u` under an operand `v` needs Lemmas 7 and 9 for the substitution `x := v`, hence the
conjecture at the pair `(v, t)` and at no other — which is what lets the recursion be followed
pair by pair, along the domain order on bounds.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conj8Pair where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.Rename using (substCtx; x∉-domΓ; prevalid-suffix)
open import MPSS.Weakening using (wf-weaken; ⊑*wf-weaken)
open import MPSS.Subst28 using (Lem-28-ctx)
open import MPSS.SubstDrop using (⟶ᵉ-drop; ∈-drop; no-eqv-x; no-sub-x)
open import MPSS.Congruence using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; _++ᵉ_)
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug)
open import MPSS.CoPair using (CoPair; coOf; co-src; co-tgt)
open import MPSS.Lemma2930 using (Lem-29-30)
open import MPSS.Lemma9 using (substCo; plug-subst)
open import MPSS.Lemma7 using (Diag; diag; assemble; lf1*; rgh*)
open import MPSS.Narrow using (wf-fv)

open import PSS.Syntax
  using (subst-open; subst-fvar-≡; subst-fvar-≢; subst-fresh;
         ∉-++ˡ; ∉-++ʳ; ∉-tail)
```

## The hypothesis

Conjecture 8 for the one pair `(α, t)`, in every context that extends `Γ₀`.

```agda
C8At : Ctx → Tm → Tm → Set
C8At Γ₀ α t = ∀ (Δ : Ctx) (C : CoCtx)
            → (Δ ++ Γ₀) ⊢ plug C α wf → (Δ ++ Γ₀) ⊢ plug C t wf
            → (Δ ++ Γ₀) ⊢ plug C α ⊑*wf[ sub-m ] plug C t
```

## Lemma 9

```agda
Lem-9ᵖ : ∀ (Δ : Ctx) {Γ x t α u v}
       → (∀ (C : CoCtx) → (substCtx x α Δ ++ Γ) ⊢ plug C α wf → (substCtx x α Δ ++ Γ) ⊢ plug C t wf
                        → (substCtx x α Δ ++ Γ) ⊢ plug C α ⊑*wf[ sub-m ] plug C t)
      → LC α → LC t → fv α ⊑ dom Γ
      → (substCtx x α Δ ++ Γ) ⊢ (u [ x := α ]) wf
      → (substCtx x α Δ ++ Γ) ⊢ (v [ x := α ]) wf
      → (substCtx x α Δ ++ Γ) ⊢ α ⊑*wf[ sub-m ] t
      → (Δ ++ (x , sub , t) ∷ Γ) ∣ [] ⊢ u ⟶ˢ v
      → (substCtx x α Δ ++ Γ) ⊢ (u [ x := α ]) ⊑*wf[ sub-m ] (v [ x := α ])
Lem-9ᵖ Δ {Γ} {x} {t} {α} {u} {v} conj8 lα lt fα wu wv α≤t d
  with Lem-29-30 Δ {α = α} lα fα d

... | inj₂ st = Ws-Sub wu (Ws-Lf2 wu st wv (Ws-Rfl (wf⇒prevalid wu))) wv

... | inj₁ c = transport (conj8 C′ wu′ wv′)
  where
    ctx : (Δ ++ (x , sub , t) ∷ Γ) prevalid
    ctx = prevalid-ctx (⟶ˢ-prevalid d)

    x∉t : x ∉ fv t
    x∉t h = x∉-domΓ Δ ctx (head-fv (prevalid-suffix Δ ctx) h)

    C′ : CoCtx
    C′ = substCo x α (coOf c)

    eu : (u [ x := α ]) ≡ plug C′ α
    eu = trans (cong (_[ x := α ]) (co-src c))
               (trans (plug-subst (coOf c) x α (fvar x))
                      (cong (plug C′) (subst-fvar-≡ {x} α)))

    ev : (v [ x := α ]) ≡ plug C′ t
    ev = trans (cong (_[ x := α ]) (co-tgt c))
               (trans (plug-subst (coOf c) x α t)
                      (cong (plug C′) (subst-fresh {t} x α x∉t)))

    wu′ : (substCtx x α Δ ++ Γ) ⊢ plug C′ α wf
    wu′ = subst (λ q → (substCtx x α Δ ++ Γ) ⊢ q wf) eu wu

    wv′ : (substCtx x α Δ ++ Γ) ⊢ plug C′ t wf
    wv′ = subst (λ q → (substCtx x α Δ ++ Γ) ⊢ q wf) ev wv

    transport : (substCtx x α Δ ++ Γ) ⊢ plug C′ α ⊑*wf[ sub-m ] plug C′ t
              → (substCtx x α Δ ++ Γ) ⊢ (u [ x := α ]) ⊑*wf[ sub-m ] (v [ x := α ])
    transport h rewrite eu | ev = h
```

## Lemma 7

```agda
module _ {Γ₀ : Ctx} {x : Name} {t α : Tm} (c8 : C8At Γ₀ α t)
         (lα : LC α) (lt : LC t) (fα : fv α ⊑ dom Γ₀)
         (wα : Γ₀ ⊢ α wf) (α≤t : Γ₀ ⊢ α ⊑*wf[ sub-m ] t) where

  Sub : Ctx → Ctx
  Sub Δ = substCtx x α Δ ++ Γ₀

  Old : Ctx → Ctx
  Old Δ = Δ ++ (x , sub , t) ∷ Γ₀

  Lem-7ᵖ : ∀ (Δ : Ctx) {u} → Old Δ ⊢ u wf → Sub Δ ⊢ (u [ x := α ]) wf

  ⊑*wf-subᵖ : ∀ (Δ : Ctx) {a b}
           → Old Δ ⊢ a ⊑*wf[ sub-m ] b
           → Sub Δ ⊢ (a [ x := α ]) ⊑*wf[ sub-m ] (b [ x := α ])

  auxᵖ : ∀ (Δ : Ctx) {a b}
      → Old Δ ⊢ a ⊑wf[ sub-m ] b
      → Diag (Sub Δ) (a [ x := α ]) (b [ x := α ])

  Lem-7ᵖ Δ {fvar y} (Wf-PrS pv m) = go (x ≟ y)
    where
      go : Dec (x ≡ y) → Sub Δ ⊢ ((fvar y) [ x := α ]) wf
      go (yes refl) rewrite subst-fvar-≡ {x} α =
        wf-weaken [] (substCtx x α Δ) (Lem-28-ctx Δ lα fα pv) wα
      go (no q) rewrite subst-fvar-≢ {x} {y} α q =
        Wf-PrS (Lem-28-ctx Δ lα fα pv) (∈-drop Δ pv (λ p → q (sym p)) m)

  Lem-7ᵖ Δ {fvar y} (Wf-PrE pv m) = go (x ≟ y)
    where
      go : Dec (x ≡ y) → Sub Δ ⊢ ((fvar y) [ x := α ]) wf
      go (yes refl) = ⊥-elim (no-eqv-x Δ pv m)
      go (no q) rewrite subst-fvar-≢ {x} {y} α q =
        Wf-PrE (Lem-28-ctx Δ lα fα pv) (∈-drop Δ pv (λ p → q (sym p)) m)

  Lem-7ᵖ Δ (Wf-Top pv) = Wf-Top (Lem-28-ctx Δ lα fα pv)

  Lem-7ᵖ Δ {lam w u} (Wf-Fun L F ww) =
    Wf-Fun (x ∷ L ++ dom (Old Δ)) body (Lem-7ᵖ Δ ww)
    where
      body : ∀ {z} → z ∉ (x ∷ L ++ dom (Old Δ))
           → ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u [ x := α ]) ^ fvar z) wf
      body {z} z∉ = tr (Lem-7ᵖ ((z , sub , w) ∷ Δ) (F (∉-++ˡ (∉-tail z∉))))
        where
          x≢z : x ≢ z
          x≢z p = z∉ (here (sym p))

          eq = trans (subst-open lα 0 (fvar z) u x)
                     (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))

          tr : ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u ^ fvar z) [ x := α ]) wf
             → ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u [ x := α ]) ^ fvar z) wf
          tr h rewrite sym eq = h

  Lem-7ᵖ Δ (Wf-App d₁ d₂) = Wf-App (⊑*wf-subᵖ Δ d₁) (⊑*wf-subᵖ Δ d₂)

  ⊑*wf-subᵖ Δ (Ws-Sub w d w')  = assemble (Lem-7ᵖ Δ w) (Lem-7ᵖ Δ w') (auxᵖ Δ d)
  ⊑*wf-subᵖ Δ (Ws-Trs d₁ w d₂) =
    Ws-Trs (⊑*wf-subᵖ Δ d₁) (Lem-7ᵖ Δ w) (⊑*wf-subᵖ Δ d₂)

  auxᵖ Δ (Ws-Rfl pv) = diag (εᵉ pv') (εᵉ pv') (εᵉ pv') (inj₁ refl)
    where pv' = Pv-Nil (Lem-28-ctx Δ lα fα pv)

  auxᵖ Δ (Ws-Lf1 e d) with auxᵖ Δ d
  ... | diag b→c b'→c a→a' r = diag b→c b'→c (⟶ᵉ-drop Δ lα fα e ◅ᵉ a→a') r

  auxᵖ Δ (Ws-Rgh d e) with auxᵖ Δ d
  ... | diag b→c b'→c a→a' r = diag (⟶ᵉ-drop Δ lα fα e ◅ᵉ b→c) b'→c a→a' r

  auxᵖ Δ {a} {b} (Ws-Lf2 wa st wa₀ d) with auxᵖ Δ d
  ... | diag {A'} {B'} {C} b→c b'→c a₀→a' r = build r
    where
      wA  = Lem-7ᵖ Δ wa
      wA₀ = Lem-7ᵖ Δ wa₀
      pv' = Pv-Nil (wf⇒prevalid wA)

      a≤a₀ : Sub Δ ⊢ (a [ x := α ]) ⊑*wf[ sub-m ] _
      a≤a₀ = Lem-9ᵖ Δ (c8 (substCtx x α Δ)) lα lt fα wA wA₀ (⊑*wf-weaken [] (substCtx x α Δ) (wf⇒prevalid wA) α≤t) st

      build : (A' ≡ B') ⊎ (Sub Δ ⊢ A' ⊑*wf[ sub-m ] B')
            → Diag (Sub Δ) (a [ x := α ]) (b [ x := α ])
      build (inj₁ refl) =
        diag b→c (a₀→a' ++ᵉ b'→c) (εᵉ pv') (inj₂ a≤a₀)
      build (inj₂ rr) =
        diag b→c b'→c (εᵉ pv') (inj₂ (Ws-Trs (Ws-Trs a≤a₀ wA₀ a₀≤A') wA' rr))
        where
          wA' = ⊑*wf⇒wfˡ rr
          a₀≤A' = Ws-Sub wA₀ (lf1* a₀→a' (Ws-Rfl (wf⇒prevalid wA))) wA'

```

## What this establishes

`Lem-9ᵖ` and `Lem-7ᵖ`: promotion under substitution and substitution preserving well-formedness,
for the substitution `x := α` with `α ≤*wf t`, from Conjecture 8 at the pair `(α, t)` alone.
