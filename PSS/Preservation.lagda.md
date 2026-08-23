# System λ⊲: Lemma B.4 and Theorem 4.2 — preservation

**Lemma B.4**: reduction preserves well-formedness. **Theorem 4.2**: reduction preserves
well-subtyping. Together with progress (4.1) this is type safety, and it completes §4.

Every input is now in hand: B.3 exhibits both endpoints of a well-subtyping derivation as
well-formed, B.5 handles the `E-App` case, narrowing handles the two congruence cases where an
annotation or a stacked operand moves, and Theorem 4.4 handles the rest.

```agda
{-# OPTIONS --safe #-}

module PSS.Preservation where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed
open import PSS.Equivalence
open import PSS.Promotion
open import PSS.Rename using (substStack-id)
open import PSS.Scope
open import PSS.Commutation
open import PSS.Transitivity
open import PSS.Narrowing
open import PSS.Substitution
open import PSS.Progress
```

## Lemma B.4

By induction on local closure, reading the well-formedness derivation and the reduction step
alongside. Because the induction is on the term and not on the context, the induction
hypothesis is available at *any* extended context — which is exactly the `WfStep` witness that
narrowing demands.

```agda
Lem-B·4 : ∀ {Γ s t t'} → LC t → Γ ∣ s ⊢ t wf → t ↦ t' → Γ ∣ s ⊢ t' wf
```

**`E-App`** — the redex fires and the operand is substituted for the formal parameter. The
operator's well-formedness at a non-empty stack can only come from `W-FunOp`, which binds the
parameter to the operand; Lemma B.5 then substitutes it away.

```agda
Lem-B·4 {Γ} {s} (lc-app llam lc) (W-App d₁ d₂) (E-App {a} {b} {c} _ _) =
  result
  where
    pvS : Γ ∣ (c ∷ s) prevalid
    pvS = ≤*wf⇒prevalid d₁

    fvc : fv c ⊑ dom Γ
    fvc = fv-stack-head pvS

    lam-wf : Γ ∣ (c ∷ s) ⊢ lam a b wf
    lam-wf = proj₁ (≤*wf⇒both d₁)

    open-body : ∀ {L} → (∀ {x} → x ∉ L → ((x , c) ∷ Γ) ∣ s ⊢ (b ^ fvar x) wf)
              → Γ ∣ s ⊢ (b ^ c) wf
    open-body {L} F = transport (wf-subst x [] lc x∉c fvc (F x∉L))
      where
        A  = L ++ fv b ++ fv c ++ fvStack s
        x  = fresh A
        a∉ = fresh-∉ A

        x∉L  = ∉-++ˡ a∉
        x∉b : x ∉ fv b
        x∉b  = ∉-++ˡ (∉-++ʳ L a∉)
        x∉c : x ∉ fv c
        x∉c  = ∉-++ˡ (∉-++ʳ (fv b) (∉-++ʳ L a∉))
        x∉s : x ∉ fvStack s
        x∉s  = ∉-++ʳ (fv c) (∉-++ʳ (fv b) (∉-++ʳ L a∉))

        transport₀ : Γ ∣ substStack x c s ⊢ ((b ^ fvar x) [ x := c ]) wf
                   → Γ ∣ substStack x c s ⊢ (b ^ c) wf
        transport₀ h rewrite subst-intro {b} lc x x∉b = h

        transport : Γ ∣ substStack x c s ⊢ ((b ^ fvar x) [ x := c ]) wf
                  → Γ ∣ s ⊢ (b ^ c) wf
        transport h = subst (λ σ → Γ ∣ σ ⊢ (b ^ c) wf)
                            (substStack-id x c s x∉s) (transport₀ h)

    result : Γ ∣ s ⊢ (b ^ c) wf
    result with lam-wf
    ... | W-FunOp L F _ = open-body {L} F
```

**`E-Lam-l`** — the annotation steps. With an operand waiting the parameter is bound to the
operand, so nothing moves in the context; with an empty stack the parameter is bound to the
annotation, and the body must be narrowed.

```agda
Lem-B·4 (lc-lam {a} {b} L₀ la F₀) (W-Fun L F wa) (E-Lam-l st) =
  W-Fun L (λ {x} x∉ → wf-narrow (crw-cons (CtxRedW-refl (strip (wf⇒prevalid (F x∉))))
                                          (↦⇒⟶≡ la st) step)
                                srw-nil (F x∉))
          (Lem-B·4 la wa st)
  where
    step : WfStep a _
    step h = Lem-B·4 la h st

    strip : ∀ {Γ₀ x t} → ((x , t) ∷ Γ₀) ∣ [] prevalid → Γ₀ ∣ [] prevalid
    strip (P-Ctx2 p _ _ _) = p

Lem-B·4 (lc-lam L₀ la F₀) (W-FunOp L F wa) (E-Lam-l st) =
  W-FunOp L F (Lem-B·4 la wa st)
```

**`E-Lam-r`** — the body steps, at every sufficiently fresh name.

```agda
Lem-B·4 (lc-lam L₀ la F₀) (W-Fun L F wa) (E-Lam-r L' F') =
  W-Fun (L₀ ++ L ++ L') body wa
  where
    body : ∀ {x} → x ∉ (L₀ ++ L ++ L') → _
    body {x} x∉ = Lem-B·4 (F₀ (∉-++ˡ x∉))
                          (F (∉-++ˡ (∉-++ʳ L₀ x∉)))
                          (F' (∉-++ʳ L (∉-++ʳ L₀ x∉)))

Lem-B·4 (lc-lam L₀ la F₀) (W-FunOp L F wa) (E-Lam-r L' F') =
  W-FunOp (L₀ ++ L ++ L') body wa
  where
    body : ∀ {x} → x ∉ (L₀ ++ L ++ L') → _
    body {x} x∉ = Lem-B·4 (F₀ (∉-++ˡ x∉))
                          (F (∉-++ˡ (∉-++ʳ L₀ x∉)))
                          (F' (∉-++ʳ L (∉-++ʳ L₀ x∉)))
```

**`E-App-l`** — the operator steps. Its reduct is a subtype of it (one `⟶≡` step read as
`As-Right` over `As-Refl`), so transitivity re-establishes the `W-App` premise.

```agda
Lem-B·4 (lc-app lu lv) (W-App d₁ d₂) (E-App-l st) =
  W-App (Wf-Sub (Wf-Rule wu' (proj₂ (≤*wf⇒both d₁))
                 (⊲-trans (wf⇒lc wu') (wf⇒lc wu) below (Thm-4·4 d₁))))
        d₂
  where
    wu  = proj₁ (≤*wf⇒both d₁)
    wu' = Lem-B·4 lu wu st

    below = As-Right (As-Refl (wf⇒prevalid wu)) (↦⇒⟶≡ lu st)
```

**`E-App-r`** — the operand steps, so it moves both in the stack and in the second premise.
The stack move is narrowing; the second premise is transitivity again.

```agda
Lem-B·4 (lc-app lu lv) (W-App d₁ d₂) (E-App-r st) =
  W-App (≤*wf-narrow (CtxRedW-refl (prevalid-nil pv)) stkred d₁)
        (Wf-Sub (Wf-Rule wv' (proj₂ (≤*wf⇒both d₂))
                 (⊲-trans (wf⇒lc wv') (wf⇒lc wv) below (Thm-4·4 d₂))))
  where
    pv  = ≤*wf⇒prevalid d₁

    wv  = proj₁ (≤*wf⇒both d₂)
    wv' = Lem-B·4 lv wv st

    below = As-Right (As-Refl (wf⇒prevalid wv)) (↦⇒⟶≡ lv st)

    step : WfStep _ _
    step h = Lem-B·4 lv h st

    stkred = srw-cons (StkRedW-refl (prevalid-stkLC (prevalid-pop pv)))
                      (↦⇒⟶≡ lv st) step
```

## Theorem 4.2 — preservation

```agda
Thm-4·2 : ∀ {Γ s t t' u} → LC t → Γ ∣ s ⊢ t ≤*wf u → t ↦ t' → Γ ∣ s ⊢ t' ≤*wf u
Thm-4·2 lt d st =
  Wf-Sub (Wf-Rule wt' (proj₂ (≤*wf⇒both d))
          (⊲-trans (wf⇒lc wt') (wf⇒lc wt) below (Thm-4·4 d)))
  where
    wt  = proj₁ (≤*wf⇒both d)
    wt' = Lem-B·4 lt wt st
    below = As-Right (As-Refl (wf⇒prevalid wt)) (↦⇒⟶≡ lt st)
```

## Type safety

```agda
type-safety : ∀ {Γ s t u} → LC t → Γ ∣ s ⊢ t ≤*wf u
            → (NF t) ⊎ (∃[ t' ] ((t ↦ t') × (Γ ∣ s ⊢ t' ≤*wf u)))
type-safety lt d with Thm-4·1 lt (proj₁ (≤*wf⇒both d))
... | inj₁ nf          = inj₁ nf
... | inj₂ (t' , st)   = inj₂ (t' , st , Thm-4·2 lt d st)
```

## What this establishes

**§4 is complete.** Progress (4.1), preservation (4.2), no supertype of `Top` (4.3),
transitivity elimination (4.4) and strong commutation (4.5), with Lemmas B.3–B.6, B.9–B.12 and
B.17–B.19 along the way.
