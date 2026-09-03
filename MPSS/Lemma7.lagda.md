# MPSS: Lemma 7 — substitution preserves well-formedness

> **Lemma 7 (Substitution preserves well-formedness).** If `Γ, x≤t, Γ′ ⊢ u wf` and
> `Γ ⊢ α ≤*wf t`, then `Γ, Γ′[x\α] ⊢ u[x\α] wf`.

Three mutually recursive functions, following the three mutually inductive judgements. The one
with content is the middle one, and it is the paper's own device.

Substituting into a `≤wf` chain cannot be done step by step: the conclusion has to be starred as
soon as a `Ws-Lf2` is met, since Lemma 9 turns a single promotion into a whole `≤*wf` derivation,
and starring an equivalence step through `Ws-Sub` would need the *intermediate* terms of the chain
to be well-formed — which `Ws-Lf1` and `Ws-Rgh` do not provide, and which is false in general
(`MPSS/EqvWf`).

The way out is to accumulate the equivalence steps as reduction sequences instead. The sub-induction
returns a diagram

> `a[x\α] ⟶≡↠ a′`, `b[x\α] ⟶≡↠ c`, `b′ ⟶≡↠ c`, and `a′ ≤*wf b′` unless `a′ = b′`

in which well-formedness is needed only where it is available: at the chain's endpoints, supplied
by `Ws-Sub`, and at the `Ws-Lf2` nodes, which carry it as premises. Reassembling the diagram into
a `≤*wf` derivation is then routine, because `Ws-Lf1` and `Ws-Rgh` consume a reduction sequence
without asking for anything.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Lemma7 where

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
open import MPSS.Assumed using (Conj-8)
open import MPSS.Lemma9 using (Lem-9)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Evaluation using (Lem-7₀)

open import PSS.Syntax
  using (subst-open; subst-fvar-≡; subst-fvar-≢; subst-intro;
         ∉-++ˡ; ∉-++ʳ; ∉-tail; fresh; fresh-∉)
```

## Consuming a reduction sequence

`Ws-Lf1` walks the left endpoint along a sequence, `Ws-Rgh` the right, and neither needs a
well-formedness premise.

```agda
lf1* : ∀ {Γ m a a' b} → Γ ∣ [] ⊢ a ⟶ᵉ* a' → Γ ⊢ a' ⊑wf[ m ] b → Γ ⊢ a ⊑wf[ m ] b
lf1* (εᵉ _)   d = d
lf1* (e ◅ᵉ p) d = Ws-Lf1 e (lf1* p d)

rgh* : ∀ {Γ m v b c} → Γ ∣ [] ⊢ b ⟶ᵉ* c → Γ ⊢ v ⊑wf[ m ] c → Γ ⊢ v ⊑wf[ m ] b
rgh* (εᵉ _)   d = d
rgh* (e ◅ᵉ p) d = Ws-Rgh (rgh* p d) e
```

## The diagram

```agda
record Diag (Γ : Ctx) (A B : Tm) : Set where
  constructor diag
  field
    {A' B' C} : Tm
    b→c   : Γ ∣ [] ⊢ B ⟶ᵉ* C
    b'→c  : Γ ∣ [] ⊢ B' ⟶ᵉ* C
    a→a'  : Γ ∣ [] ⊢ A ⟶ᵉ* A'
    rel   : (A' ≡ B') ⊎ (Γ ⊢ A' ⊑*wf[ sub-m ] B')
open Diag
```

Reassembly. With `A′ = B′` the two sides already meet at `C`, so one `Ws-Sub` suffices; otherwise
the relation in the middle is flanked by the two sequences.

```agda
assemble : ∀ {Γ A B} → Γ ⊢ A wf → Γ ⊢ B wf → Diag Γ A B → Γ ⊢ A ⊑*wf[ sub-m ] B
assemble {Γ} {A} {B} wA wB (diag {A'} {B'} {C} b→c b'→c a→a' (inj₁ refl)) =
  Ws-Sub wA (rgh* b→c (lf1* (a→a' ++ᵉ b'→c) (Ws-Rfl (wf⇒prevalid wA)))) wB
assemble {Γ} {A} {B} wA wB (diag {A'} {B'} {C} b→c b'→c a→a' (inj₂ r)) =
  Ws-Trs (Ws-Trs A≤A' wA' r) wB' B'≤B
  where
    wA' = ⊑*wf⇒wfˡ r
    wB' = ⊑*wf⇒wfʳ r
    pv  = wf⇒prevalid wA

    A≤A' : Γ ⊢ A ⊑*wf[ sub-m ] A'
    A≤A' = Ws-Sub wA (lf1* a→a' (Ws-Rfl pv)) wA'

    B'≤B : Γ ⊢ B' ⊑*wf[ sub-m ] B
    B'≤B = Ws-Sub wB' (rgh* b→c (lf1* b'→c (Ws-Rfl pv))) wB
```

## Lemma 7

```agda
module _ (conj8 : Conj-8) {Γ₀ : Ctx} {x : Name} {t α : Tm}
         (lα : LC α) (lt : LC t) (fα : fv α ⊑ dom Γ₀)
         (wα : Γ₀ ⊢ α wf) (α≤t : Γ₀ ⊢ α ⊑*wf[ sub-m ] t) where

  Sub : Ctx → Ctx
  Sub Δ = substCtx x α Δ ++ Γ₀

  Old : Ctx → Ctx
  Old Δ = Δ ++ (x , sub , t) ∷ Γ₀

  Lem-7 : ∀ (Δ : Ctx) {u} → Old Δ ⊢ u wf → Sub Δ ⊢ (u [ x := α ]) wf

  ⊑*wf-sub : ∀ (Δ : Ctx) {a b}
           → Old Δ ⊢ a ⊑*wf[ sub-m ] b
           → Sub Δ ⊢ (a [ x := α ]) ⊑*wf[ sub-m ] (b [ x := α ])

  aux : ∀ (Δ : Ctx) {a b}
      → Old Δ ⊢ a ⊑wf[ sub-m ] b
      → Diag (Sub Δ) (a [ x := α ]) (b [ x := α ])
```

**The main induction.** A variable is either the one being substituted — where the result is `α`,
well-formed in `Γ₀` and weakened — or another, whose entry survives with its annotation
substituted.

```agda
  Lem-7 Δ {fvar y} (Wf-PrS pv m) = go (x ≟ y)
    where
      go : Dec (x ≡ y) → Sub Δ ⊢ ((fvar y) [ x := α ]) wf
      go (yes refl) rewrite subst-fvar-≡ {x} α =
        wf-weaken [] (substCtx x α Δ) (Lem-28-ctx Δ lα fα pv) wα
      go (no q) rewrite subst-fvar-≢ {x} {y} α q =
        Wf-PrS (Lem-28-ctx Δ lα fα pv) (∈-drop Δ pv (λ p → q (sym p)) m)

  Lem-7 Δ {fvar y} (Wf-PrE pv m) = go (x ≟ y)
    where
      go : Dec (x ≡ y) → Sub Δ ⊢ ((fvar y) [ x := α ]) wf
      go (yes refl) = ⊥-elim (no-eqv-x Δ pv m)
      go (no q) rewrite subst-fvar-≢ {x} {y} α q =
        Wf-PrE (Lem-28-ctx Δ lα fα pv) (∈-drop Δ pv (λ p → q (sym p)) m)

  Lem-7 Δ (Wf-Top pv) = Wf-Top (Lem-28-ctx Δ lα fα pv)

  Lem-7 Δ {lam w u} (Wf-Fun L F ww) =
    Wf-Fun (x ∷ L ++ dom (Old Δ)) body (Lem-7 Δ ww)
    where
      body : ∀ {z} → z ∉ (x ∷ L ++ dom (Old Δ))
           → ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u [ x := α ]) ^ fvar z) wf
      body {z} z∉ = tr (Lem-7 ((z , sub , w) ∷ Δ) (F (∉-++ˡ (∉-tail z∉))))
        where
          x≢z : x ≢ z
          x≢z p = z∉ (here (sym p))

          eq = trans (subst-open lα 0 (fvar z) u x)
                     (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))

          tr : ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u ^ fvar z) [ x := α ]) wf
             → ((z , sub , w [ x := α ]) ∷ Sub Δ) ⊢ ((u [ x := α ]) ^ fvar z) wf
          tr h rewrite sym eq = h

  Lem-7 Δ (Wf-App d₁ d₂) = Wf-App (⊑*wf-sub Δ d₁) (⊑*wf-sub Δ d₂)
```

**The transitive closure.** Endpoint well-formedness comes from `Ws-Sub`, and is exactly what
`assemble` needs.

```agda
  ⊑*wf-sub Δ (Ws-Sub w d w')  = assemble (Lem-7 Δ w) (Lem-7 Δ w') (aux Δ d)
  ⊑*wf-sub Δ (Ws-Trs d₁ w d₂) =
    Ws-Trs (⊑*wf-sub Δ d₁) (Lem-7 Δ w) (⊑*wf-sub Δ d₂)
```

**The sub-induction.** `Ws-Lf1` and `Ws-Rgh` lengthen a sequence. `Ws-Lf2` is the only case that
does anything: Lemma 9 converts the promotion into a `≤*wf` derivation, and the diagram is rebuilt
around it with `a` itself as the new `a′`.

```agda
  aux Δ (Ws-Rfl pv) = diag (εᵉ pv') (εᵉ pv') (εᵉ pv') (inj₁ refl)
    where pv' = Pv-Nil (Lem-28-ctx Δ lα fα pv)

  aux Δ (Ws-Lf1 e d) with aux Δ d
  ... | diag b→c b'→c a→a' r = diag b→c b'→c (⟶ᵉ-drop Δ lα fα e ◅ᵉ a→a') r

  aux Δ (Ws-Rgh d e) with aux Δ d
  ... | diag b→c b'→c a→a' r = diag (⟶ᵉ-drop Δ lα fα e ◅ᵉ b→c) b'→c a→a' r

  aux Δ {a} {b} (Ws-Lf2 wa st wa₀ d) with aux Δ d
  ... | diag {A'} {B'} {C} b→c b'→c a₀→a' r = build r
    where
      wA  = Lem-7 Δ wa
      wA₀ = Lem-7 Δ wa₀
      pv' = Pv-Nil (wf⇒prevalid wA)

      a≤a₀ : Sub Δ ⊢ (a [ x := α ]) ⊑*wf[ sub-m ] _
      a≤a₀ = Lem-9 conj8 Δ lα lt fα wA wA₀ (⊑*wf-weaken [] (substCtx x α Δ) (wf⇒prevalid wA) α≤t) st

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

## The form the β case needs

`MPSS/Evaluation` states Lemma 7 at an empty context suffix, where substitution for the bound
variable is opening. That is this lemma with `Δ = []`, at a fresh name.

```agda
Lem-7₀-holds : Conj-8 → Lem-7₀
Lem-7₀-holds conj8 {Γ} {u} {w} v L F w≤u = tr (Lem-7 conj8 lw lu fw ww w≤u [] (F z∉L))
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

## What this establishes

Lemma 7, modulo Conjecture 8 alone — through Lemma 9, which is the only place the conjecture is
used — and `Lem-7₀-holds`, which discharges the hypothesis `MPSS/Evaluation` was carrying. The
assumption list for preservation therefore loses Lemma 7 and gains Conjecture 8, which the paper
itself flags as its one outstanding obligation.
