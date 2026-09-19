# MPSS: Lemmas 7 and 6 and Theorem 5 over contexts with well-formed annotations

`MPSS/Conj8Refuted` refutes Conjecture 8, Lemmas 6 and 7 and Theorem 5 as stated; `MPSS/WfCtx`
restates them over contexts whose annotations are well-formed. This module carries the paper's
chain of proofs over to the restated forms: Lemma 7, Lemma 6 and Theorem 5 follow from
`Conj-8ʷᶜ` alone, as they followed from `Conj-8` before the refutation.

The point that needed checking is that Lemma 7's induction stays inside `WfCtx`. It calls the
conjecture at `Δ[x := α] ++ Γ`, so that context has to be `WfCtx` at every call. The premise is
threaded through the induction: the only case that extends `Δ` is `Wf-Fun`, which adds
`z ≤ w[x := α]`, and `w[x := α]` is well-formed there by the induction hypothesis on the
annotation. No separate lemma that substitution preserves `WfCtx` is needed.

```agda
{-# OPTIONS --safe #-}

module MPSS.WfCtxSafety where

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
open import MPSS.Static using (Lem-15; Lem-16; ⊑*wf⇒wfʳ)
open import MPSS.Rename using (substCtx)
open import MPSS.Weakening using (wf-weaken; ⊑*wf-weaken)
open import MPSS.Subst28 using (Lem-28-ctx; outof)
open import MPSS.SubstDrop using (⟶ᵉ-drop; ∈-drop; no-eqv-x)
open import MPSS.Congruence using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; _++ᵉ_)
open import MPSS.Conj8Pair using (Lem-9ᵖ)
open import MPSS.Lemma7 using (Diag; diag; assemble; lf1*)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Unconditional using (Lem-10; Thm-4′)
open import MPSS.Prop17Chain using (Prop-17ʷ; narrow-chain)
open import MPSS.Preservation17 using (Prop-27ʷ)
open import MPSS.WfCtx using (WfCtx; wc-sub; Conj-8ʷᶜ; Lem-6ʷᶜ; Preservationʷᶜ)

open import PSS.Syntax
  using (subst-open; subst-intro; subst-fvar-≡; subst-fvar-≢; fresh; fresh-∉;
         ∉-++ˡ; ∉-++ʳ; ∉-tail)
```

A name of `Δ ++ Γ` is a name of `Δ ++ e ∷ Γ`.

```agda
dom-mid : ∀ (Δ : Ctx) {Γ e z} → z ∈ dom (Δ ++ Γ) → z ∈ dom (Δ ++ e ∷ Γ)
dom-mid []            h         = there h
dom-mid (_ ∷ Δ)       (here p)  = here p
dom-mid (_ ∷ Δ)       (there h) = there (dom-mid Δ h)
```

## Lemma 7

`MPSS/Conj8Pair`'s proof, with `WfCtx (Δ[x := α] ++ Γ₀)` carried along and handed to the
conjecture at the one place it is called, the `Ws-Lf2` case, through Lemma 9.

```agda
module _ {Γ₀ : Ctx} {x : Name} {t α : Tm} (c8 : Conj-8ʷᶜ)
         (lα : LC α) (lt : LC t) (fα : fv α ⊑ dom Γ₀)
         (wα : Γ₀ ⊢ α wf) (α≤t : Γ₀ ⊢ α ⊑*wf[ sub-m ] t) where

  Sub : Ctx → Ctx
  Sub Δ = substCtx x α Δ ++ Γ₀

  Old : Ctx → Ctx
  Old Δ = Δ ++ (x , sub , t) ∷ Γ₀

  Lem-7ʷ : ∀ (Δ : Ctx) {u} → WfCtx (Sub Δ) → Old Δ ⊢ u wf → Sub Δ ⊢ (u [ x := α ]) wf

  ⊑*wf-subʷ : ∀ (Δ : Ctx) {a b} → WfCtx (Sub Δ)
           → Old Δ ⊢ a ⊑*wf[ sub-m ] b
           → Sub Δ ⊢ (a [ x := α ]) ⊑*wf[ sub-m ] (b [ x := α ])

  auxʷ : ∀ (Δ : Ctx) {a b} → WfCtx (Sub Δ)
      → Old Δ ⊢ a ⊑wf[ sub-m ] b
      → Diag (Sub Δ) (a [ x := α ]) (b [ x := α ])

  Lem-7ʷ Δ {fvar y} wc (Wf-PrS pv m) = go (x ≟ y)
    where
      go : Dec (x ≡ y) → Sub Δ ⊢ ((fvar y) [ x := α ]) wf
      go (yes refl) rewrite subst-fvar-≡ {x} α =
        wf-weaken [] (substCtx x α Δ) (Lem-28-ctx Δ lα fα pv) wα
      go (no q) rewrite subst-fvar-≢ {x} {y} α q =
        Wf-PrS (Lem-28-ctx Δ lα fα pv) (∈-drop Δ pv (λ p → q (sym p)) m)

  Lem-7ʷ Δ {fvar y} wc (Wf-PrE pv m) = go (x ≟ y)
    where
      go : Dec (x ≡ y) → Sub Δ ⊢ ((fvar y) [ x := α ]) wf
      go (yes refl) = ⊥-elim (no-eqv-x Δ pv m)
      go (no q) rewrite subst-fvar-≢ {x} {y} α q =
        Wf-PrE (Lem-28-ctx Δ lα fα pv) (∈-drop Δ pv (λ p → q (sym p)) m)

  Lem-7ʷ Δ wc (Wf-Top pv) = Wf-Top (Lem-28-ctx Δ lα fα pv)

  Lem-7ʷ Δ {lam w u} wc (Wf-Fun L F ww) =
    Wf-Fun (x ∷ L ++ dom (Old Δ)) body (Lem-7ʷ Δ wc ww)
    where
      body : ∀ {z} → z ∉ (x ∷ L ++ dom (Old Δ))
           → ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u [ x := α ]) ^ fvar z) wf
      body {z} z∉ = tr (Lem-7ʷ ((z , sub , w) ∷ Δ) (wc-sub wc z∉S (Lem-7ʷ Δ wc ww)) (F (∉-++ˡ (∉-tail z∉))))
        where
          z∉S : z ∉ dom (Sub Δ)
          z∉S h = ∉-++ʳ L (∉-tail z∉) (dom-mid Δ (outof x α Δ Γ₀ h))

          x≢z : x ≢ z
          x≢z p = z∉ (here (sym p))

          eq = trans (subst-open lα 0 (fvar z) u x)
                     (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))

          tr : ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u ^ fvar z) [ x := α ]) wf
             → ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u [ x := α ]) ^ fvar z) wf
          tr h rewrite sym eq = h

  Lem-7ʷ Δ wc (Wf-App d₁ d₂) = Wf-App (⊑*wf-subʷ Δ wc d₁) (⊑*wf-subʷ Δ wc d₂)

  ⊑*wf-subʷ Δ wc (Ws-Sub w d w')  = assemble (Lem-7ʷ Δ wc w) (Lem-7ʷ Δ wc w') (auxʷ Δ wc d)
  ⊑*wf-subʷ Δ wc (Ws-Trs d₁ w d₂) =
    Ws-Trs (⊑*wf-subʷ Δ wc d₁) (Lem-7ʷ Δ wc w) (⊑*wf-subʷ Δ wc d₂)

  auxʷ Δ wc (Ws-Rfl pv) = diag (εᵉ pv') (εᵉ pv') (εᵉ pv') (inj₁ refl)
    where pv' = Pv-Nil (Lem-28-ctx Δ lα fα pv)

  auxʷ Δ wc (Ws-Lf1 e d) with auxʷ Δ wc d
  ... | diag b→c b'→c a→a' r = diag b→c b'→c (⟶ᵉ-drop Δ lα fα e ◅ᵉ a→a') r

  auxʷ Δ wc (Ws-Rgh d e) with auxʷ Δ wc d
  ... | diag b→c b'→c a→a' r = diag (⟶ᵉ-drop Δ lα fα e ◅ᵉ b→c) b'→c a→a' r

  auxʷ Δ {a} {b} wc (Ws-Lf2 wa st wa₀ d) with auxʷ Δ wc d
  ... | diag {A'} {B'} {C} b→c b'→c a₀→a' r = build r
    where
      wA  = Lem-7ʷ Δ wc wa
      wA₀ = Lem-7ʷ Δ wc wa₀
      pv' = Pv-Nil (wf⇒prevalid wA)

      α≤t′ = ⊑*wf-weaken [] (substCtx x α Δ) (wf⇒prevalid wA) α≤t

      a≤a₀ : Sub Δ ⊢ (a [ x := α ]) ⊑*wf[ sub-m ] _
      a≤a₀ = Lem-9ᵖ Δ (λ C → c8 C wc lα lt α≤t′) lα lt fα wA wA₀ α≤t′ st

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

## Lemma 7 as Lemma 6 uses it

```agda
module _ (c8 : Conj-8ʷᶜ) where

  Lem-7₀ʷᶜ : ∀ {Γ u w} v (L : List Name) → WfCtx Γ
           → (∀ {x} → x ∉ L → ((x , sub , u) ∷ Γ) ⊢ (v ^ fvar x) wf)
           → Γ ⊢ w ⊑*wf[ sub-m ] u
           → Γ ⊢ (v ^ w) wf
  Lem-7₀ʷᶜ {Γ} {u} {w} v L wc F w≤u = tr (Lem-7ʷ c8 lw lu fw ww w≤u [] wc (F z∉L))
    where
      A   = L ++ fv v ++ dom Γ
      z   = fresh A
      z∉  = fresh-∉ A
      z∉L = ∉-++ˡ z∉
      z∉v : z ∉ fv v
      z∉v = ∉-++ˡ (∉-++ʳ L z∉)

      ww = ⊑*wf⇒wfˡ w≤u
      lw = wf⇒lc ww
      lu = wf⇒lc (⊑*wf⇒wfʳ w≤u)
      fw = wf-fv ww

      tr : Γ ⊢ ((v ^ fvar z) [ z := w ]) wf → Γ ⊢ (v ^ w) wf
      tr h rewrite subst-intro {v} lw z z∉v = h
```

## Lemma 6 and Theorem 5

`MPSS/Preservation17`'s proof. The one case that goes under a binder, `E-Lam-r`, extends the
context by the abstraction's annotation, which is well-formed.

```agda
  lem-6ʷᶜ : Lem-6ʷᶜ
  lem-6ʷᶜ wc (Wf-App {u = lam a b} {v = c} d₁ d₂) (E-App _ _)
    with ⊑*wf⇒wfˡ d₁ | ⊑*wf⇒wfʳ d₁
  ... | Wf-Fun L F wa | Wf-Fun _ _ wz =
        Lem-7₀ʷᶜ b L wc F (Ws-Trs d₂ wz (Ws-Sub wz (Lem-16 (Lem-15 (Lem-10 d₁))) wa))
  lem-6ʷᶜ wc (Wf-Fun L F wu) (E-Lam-l st) =
    Wf-Fun L (λ {x} x∉ → narrow-chain (F x∉) wu ch) wu'
    where
      wu' = lem-6ʷᶜ wc wu st
      ch  = Prop-17ʷ wu st wu'
  lem-6ʷᶜ {Γ} wc (Wf-Fun L F wu) (E-Lam-r L' F') =
    Wf-Fun (dom Γ ++ L ++ L')
           (λ {x} x∉ → lem-6ʷᶜ (wc-sub wc (∉-++ˡ x∉) wu)
                                (F (∉-++ˡ (∉-++ʳ (dom Γ) x∉)))
                                (F' (∉-++ʳ L (∉-++ʳ (dom Γ) x∉))))
           wu
  lem-6ʷᶜ wc (Wf-App d₁ d₂) (E-App-l st) =
    Wf-App (Prop-27ʷ d₁ st (lem-6ʷᶜ wc (⊑*wf⇒wfˡ d₁) st)) d₂
  lem-6ʷᶜ wc (Wf-App d₁ d₂) (E-App-r st) =
    Wf-App d₁ (Prop-27ʷ d₂ st (lem-6ʷᶜ wc (⊑*wf⇒wfˡ d₂) st))

  preservationʷᶜ : Preservationʷᶜ
  preservationʷᶜ wc d st = Prop-27ʷ d st (lem-6ʷᶜ wc (⊑*wf⇒wfˡ d) st)

  type-safetyʷᶜ : (∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')) × Preservationʷᶜ
  type-safetyʷᶜ = Thm-4′ , preservationʷᶜ
```

## What this establishes

Type safety of MPSS over contexts with well-formed annotations — progress, and preservation for
`WfCtx Γ` — from `Conj-8ʷᶜ` and nothing else. The refutation in `MPSS/Conj8Refuted` does not
reach these statements: its context is not `WfCtx` (`MPSS/WfCtx`, `¬WfCtx-Γ₀`). What is left
open is `Conj-8ʷᶜ` itself.
