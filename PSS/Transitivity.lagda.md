# System λ⊲: Theorems 4.4 and 4.3

**Transitivity elimination** — the missing piece in Hutchins' theory — and the lemma that
progress rests on, that no abstraction is a supertype of `Top`.

The content of 4.4 is binary transitivity of `≤`, and it is where Theorem 4.5 is spent. Given
`t ≤ u` and `u ≤ v`, the first derivation may end in `As-Right`, having reduced the *target*:
it establishes `t ≤ u'` for some `u ⟶≡ u'`. To use the second derivation that step must be
pushed along it, and pushing a `⟶≡` step past a `⟶≤` step is precisely Theorem 4.5.

```agda
{-# OPTIONS --safe #-}

module PSS.Transitivity where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed
open import PSS.Equivalence
open import PSS.Promotion using (prevalid-nil)
open import PSS.Scope
open import PSS.Commutation
```

## Proposition B.3 — well-subtyping exhibits both endpoints as well-formed

```agda
≤wf⇒both  : ∀ {Γ s u v} → Γ ∣ s ⊢ u ≤wf  v → (Γ ∣ s ⊢ u wf) × (Γ ∣ s ⊢ v wf)
≤*wf⇒both : ∀ {Γ s u v} → Γ ∣ s ⊢ u ≤*wf v → (Γ ∣ s ⊢ u wf) × (Γ ∣ s ⊢ v wf)

≤wf⇒both  (Wf-Rule wu wv _)  = wu , wv
≤*wf⇒both (Wf-Sub d)         = ≤wf⇒both d
≤*wf⇒both (Wf-Trans d₁ d₂ _) = proj₁ (≤*wf⇒both d₁) , proj₂ (≤*wf⇒both d₂)
```

## Well-formed terms are terms

The source's local closure is extracted directly rather than through `≤*wf⇒both`, whose
`proj₁` the termination checker cannot see as structural.

```agda
wf⇒lc    : ∀ {Γ s t} → Γ ∣ s ⊢ t wf → LC t
≤wf⇒lcˡ  : ∀ {Γ s u v} → Γ ∣ s ⊢ u ≤wf  v → LC u
≤*wf⇒lcˡ : ∀ {Γ s u v} → Γ ∣ s ⊢ u ≤*wf v → LC u

wf⇒lc (W-Var _ _ _)    = lc-fvar
wf⇒lc (W-Top _)        = lc-Top
wf⇒lc (W-Fun L F wt)   = lc-lam L (wf⇒lc wt) (λ x∉ → wf⇒lc (F x∉))
wf⇒lc (W-FunOp L F wt) = lc-lam L (wf⇒lc wt) (λ x∉ → wf⇒lc (F x∉))
wf⇒lc (W-App d₁ d₂)    = lc-app (≤*wf⇒lcˡ d₁) (≤*wf⇒lcˡ d₂)

≤wf⇒lcˡ  (Wf-Rule wu _ _)  = wf⇒lc wu
≤*wf⇒lcˡ (Wf-Sub d)        = ≤wf⇒lcˡ d
≤*wf⇒lcˡ (Wf-Trans d₁ _ _) = ≤*wf⇒lcˡ d₁
```

## Pushing an equivalence step along a subtyping derivation

If `u ⟶≡ u'` and `u ≤ v`, then `u' ≤ v`. The `As-Left-1` case is the one that fires Theorem
4.5: the derivation's first move is a promotion out of `u`, and the equivalence step has to be
commuted past it. The context does not change, so the theorem is applied at the reflexive
context reduction.

```agda
push≡ : ∀ {Γ s u u' v} → LC u → u ⟶≡ u' → Γ ∣ s ⊢ u ≤ v → Γ ∣ s ⊢ u' ≤ v
push≡ lu e (As-Refl pv)    = As-Right (As-Refl pv) e
push≡ lu e (As-Right d e') = As-Right (push≡ lu e d) e'
push≡ lu e (As-Left-1 st d)
  with Thm-4·5 lu (CtxRed-refl (prevalid-nil (⟶≤-prevalid st)))
                  (StkRed-refl (prevalid-stkLC (⟶≤-prevalid st))) e st
... | t₃ , p , q = As-Left-1 q (push≡ (⟶≤-lc lu st) p d)
```

## Binary transitivity

```agda
⊲-trans : ∀ {Γ s t u v} → LC t → LC u
        → Γ ∣ s ⊢ t ≤ u → Γ ∣ s ⊢ u ≤ v → Γ ∣ s ⊢ t ≤ v
⊲-trans lt lu (As-Refl _)      d₂ = d₂
⊲-trans lt lu (As-Left-1 st d) d₂ = As-Left-1 st (⊲-trans (⟶≤-lc lt st) lu d d₂)
⊲-trans lt lu (As-Right d e)   d₂ = ⊲-trans lt (⟶≡-lc lu e) d (push≡ lu e d₂)
```

## Theorem 4.4 — transitivity is admissible

Stated for `≤*wf`, which is how §4 uses it. The local closure of the intermediate term comes
from the `Γ ∣ s ⊢ u wf` premise that `Wf-Trans` carries — the reason that premise is in the
rule at all.

```agda
Thm-4·4 : ∀ {Γ s u v} → Γ ∣ s ⊢ u ≤*wf v → Γ ∣ s ⊢ u ≤ v
Thm-4·4 (Wf-Sub (Wf-Rule _ _ d)) = d
Thm-4·4 (Wf-Trans d₁ d₂ wu) =
  ⊲-trans (≤*wf⇒lcˡ d₁) (wf⇒lc wu) (Thm-4·4 d₁) (Thm-4·4 d₂)
```

The plain `⊲*` form holds too, given local closure of the terms it passes through; `⊲-trans`
above is that content, and `Wf-Trans` is the packaging that supplies the hypothesis.

## Theorem 4.3 — no supertype of `Top`

`Top` promotes only to itself, and an abstraction equivalence-reduces only to an abstraction,
so the two can never meet.

```agda
Top≰lam : ∀ {Γ s t u} → ¬ (Γ ∣ s ⊢ Top ≤ lam t u)
Top≰lam (As-Left-1 (Srs-Top _) d)         = Top≰lam d
Top≰lam (As-Left-1 (Srs-Eq _ Cr-Top) d)   = Top≰lam d
Top≰lam (As-Right d (Cr-Fun _ _ _))       = Top≰lam d

Thm-4·3 : ∀ {Γ s t u} → ¬ (Γ ∣ s ⊢ Top ≤*wf lam t u)
Thm-4·3 d = Top≰lam (Thm-4·4 d)
```

## What this establishes

Transitivity elimination (4.4) and no-supertype-of-`Top` (4.3), plus Proposition B.3 and the
fact that well-formed terms are locally closed.

**Next:** progress (4.1) and preservation (4.2), i.e. type safety.
