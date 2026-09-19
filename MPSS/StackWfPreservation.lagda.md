# MPSS, candidate C: Lemma 6 and Theorem 5 — preservation, and type safety

For the stack-reading judgements of `MPSS/StackWf`. **Lemma 6**: evaluation preserves
well-formedness. **Theorem 5**: evaluation preserves well-subtyping. With progress (`Thm-4ˢ`) this
is type safety. The proof is `PSS/Preservation` (`Lem-B·4`, `Thm-4·2`, `type-safety`) case by case,
with these replacements:

- the β case is `wfˢ-subst≡-head` of `MPSS/StackWfSubst`;
- where v1 reads an evaluation step as one `⟶≡` step, here it is a chain of `⟶ᵉ` steps at the
  configuration in hand (`↦⇒⟶ᵉ*` of `MPSS/EvalChain`), and the reduct is below the redex by
  `↦⇒≥`; the scoping this asks for comes from `wfˢ-fv`;
- narrowing is `wfˢ-narrow` and `≤*wfˢ-narrow` of `MPSS/StackWfNarrow`;
- where v1 appends by `⊲-trans`, here the redex is well-formed, so `Wc-Trs` appends.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfPreservation where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)

open import MPSS.Subtyping
open import MPSS.StackWf
open import MPSS.StackWfNarrow
open import MPSS.StackWfSubst using (wfˢ-subst≡-head)
open import MPSS.EvalChain using (↦⇒⟶ᵉ*; ↦⇒≥)
open import PSS.Reduction
  using (_↦_; E-App; E-Lam-l; E-Lam-r; E-App-l; E-App-r; NF)
```

## The reduct is below the redex, with both well-formed

```agda
below : ∀ {Γ s t t′} → LC t → Γ ∣ s ⊢ t wfˢ → Γ ∣ s ⊢ t′ wfˢ → t ↦ t′ → Γ ∣ s ⊢ t′ ≤*wfˢ t
below lt wt wt′ st = Wc-Sub (Wc-Rule wt′ wt (↦⇒≥ lt (wfˢ-fv wt) (wfˢ⇒prevalid wt) st))
```

## Lemma 6

By induction on local closure, as `Lem-B·4`: the induction hypothesis holds at every
configuration, which is the `WfStep` witness narrowing asks for.

```agda
Lem-6ˢ : ∀ {Γ s t t′} → LC t → Γ ∣ s ⊢ t wfˢ → t ↦ t′ → Γ ∣ s ⊢ t′ wfˢ
```

**`E-App`.** The operator is well-formed at the stack holding the operand (`≤*wfˢ⇒both`), which
can only be by `Wc-FOp`: the body is well-formed with the parameter bound `x ≡ c`, and
`wfˢ-subst≡-head` substitutes the operand for it.

```agda
Lem-6ˢ {Γ} {s} (lc-app llam lc) (Wc-App d₁ d₂) (E-App {a} {b} {c} _ _) = result
  where
    lam-wf : Γ ∣ (c ∷ s) ⊢ lam a b wfˢ
    lam-wf = proj₁ (≤*wfˢ⇒both d₁)

    open-body : ∀ {L} → (∀ {x} → x ∉ L → ((x , eqv , c) ∷ Γ) ∣ s ⊢ (b ^ fvar x) wfˢ)
              → Γ ∣ s ⊢ (b ^ c) wfˢ
    open-body {L} F = wfˢ-subst≡-head {u = b} x x∉b x∉s (F x∉L)
      where
        A  = L ++ fv b ++ fvStack s
        x  = fresh A
        a∉ = fresh-∉ A

        x∉L  = ∉-++ˡ a∉
        x∉b : x ∉ fv b
        x∉b  = ∉-++ˡ (∉-++ʳ L a∉)
        x∉s : x ∉ fvStack s
        x∉s  = ∉-++ʳ (fv b) (∉-++ʳ L a∉)

    result : Γ ∣ s ⊢ (b ^ c) wfˢ
    result with lam-wf
    ... | Wc-FOp L F _ = open-body {L} F
```

**`E-Lam-l`.** At the empty stack the parameter is bound to the annotation, and the body is
narrowed along the annotation's chain at `Γ ∣ []`. With an operand waiting the parameter is bound
to the operand and only the annotation premise changes.

```agda
Lem-6ˢ (lc-lam {a} {b} L₀ la F₀) (Wc-Fun L F wa) (E-Lam-l st) =
  Wc-Fun L (λ {x} x∉ → wfˢ-narrow (crw-cons (CtxRedW-refl (prevalid-ctx pv))
                                            (↦⇒⟶ᵉ* la (wfˢ-fv wa) pv st) step)
                                  srw-nil (F x∉))
           (Lem-6ˢ la wa st)
  where
    pv = wfˢ⇒prevalid wa

    step : WfStep a _
    step h = Lem-6ˢ la h st

Lem-6ˢ (lc-lam L₀ la F₀) (Wc-FOp L F wa) (E-Lam-l st) =
  Wc-FOp L F (Lem-6ˢ la wa st)
```

**`E-Lam-r`.** The body steps, at every sufficiently fresh name.

```agda
Lem-6ˢ (lc-lam L₀ la F₀) (Wc-Fun L F wa) (E-Lam-r L′ F′) =
  Wc-Fun (L₀ ++ L ++ L′) body wa
  where
    body : ∀ {x} → x ∉ (L₀ ++ L ++ L′) → _
    body {x} x∉ = Lem-6ˢ (F₀ (∉-++ˡ x∉))
                         (F (∉-++ˡ (∉-++ʳ L₀ x∉)))
                         (F′ (∉-++ʳ L (∉-++ʳ L₀ x∉)))

Lem-6ˢ (lc-lam L₀ la F₀) (Wc-FOp L F wa) (E-Lam-r L′ F′) =
  Wc-FOp (L₀ ++ L ++ L′) body wa
  where
    body : ∀ {x} → x ∉ (L₀ ++ L ++ L′) → _
    body {x} x∉ = Lem-6ˢ (F₀ (∉-++ˡ x∉))
                         (F (∉-++ˡ (∉-++ʳ L₀ x∉)))
                         (F′ (∉-++ʳ L (∉-++ʳ L₀ x∉)))
```

**`E-App-l`.** The operator's reduct is well-formed at the stack holding the operand, by the
induction hypothesis, and is below the operator there; `Wc-Trs` puts it in front of the first
premise of `Wc-App`.

```agda
Lem-6ˢ (lc-app lu lv) (Wc-App d₁ d₂) (E-App-l st) =
  Wc-App (Wc-Trs (below lu wu (Lem-6ˢ lu wu st) st) d₁) d₂
  where
    wu = proj₁ (≤*wfˢ⇒both d₁)
```

**`E-App-r`.** The operand moves in the stack and in the second premise: the first premise is
narrowed along the operand's chain at `Γ ∣ []`, the second is extended as in `E-App-l`.

```agda
Lem-6ˢ (lc-app lu lv) (Wc-App {s = s} d₁ d₂) (E-App-r st) =
  Wc-App (≤*wfˢ-narrow (CtxRedW-refl (prevalid-ctx pv)) stkred d₁)
         (Wc-Trs (below lv wv (Lem-6ˢ lv wv st) st) d₂)
  where
    wv = proj₁ (≤*wfˢ⇒both d₂)
    pv = wfˢ⇒prevalid wv

    step : WfStep _ _
    step h = Lem-6ˢ lv h st

    stkred = srw-cons (StkRedW-refl (prevalid-ctx pv) s)
                      (↦⇒⟶ᵉ* lv (wfˢ-fv wv) pv st) step
```

## Theorem 5 — preservation

```agda
Thm-5ˢ : ∀ {Γ s t t′ u} → LC t → Γ ∣ s ⊢ t ≤*wfˢ u → t ↦ t′ → Γ ∣ s ⊢ t′ ≤*wfˢ u
Thm-5ˢ lt d st = Wc-Trs (below lt wt (Lem-6ˢ lt wt st) st) d
  where
    wt = proj₁ (≤*wfˢ⇒both d)
```

## Type safety

```agda
type-safetyˢ : ∀ {Γ s t u} → LC t → Γ ∣ s ⊢ t ≤*wfˢ u
             → NF t ⊎ ∃[ t′ ] ((t ↦ t′) × (Γ ∣ s ⊢ t′ ≤*wfˢ u))
type-safetyˢ lt d with Thm-4ˢ lt (proj₁ (≤*wfˢ⇒both d))
... | inj₁ nf        = inj₁ nf
... | inj₂ (t′ , st) = inj₂ (t′ , st , Thm-5ˢ lt d st)
```

For a well-formed term; local closure is `wfˢ⇒lc`. In particular for a closed term at the empty
stack.

```agda
wf-safetyˢ : ∀ {Γ s t} → Γ ∣ s ⊢ t wfˢ → NF t ⊎ ∃[ t′ ] ((t ↦ t′) × (Γ ∣ s ⊢ t′ wfˢ))
wf-safetyˢ w with Thm-4ˢ (wfˢ⇒lc w) w
... | inj₁ nf        = inj₁ nf
... | inj₂ (t′ , st) = inj₂ (t′ , st , Lem-6ˢ (wfˢ⇒lc w) w st)

closed-safetyˢ : ∀ {t} → [] ∣ [] ⊢ t wfˢ → NF t ⊎ ∃[ t′ ] ((t ↦ t′) × ([] ∣ [] ⊢ t′ wfˢ))
closed-safetyˢ = wf-safetyˢ
```

## What this establishes

For candidate C — v1's well-formedness, indexed by the operand stack, over MPSS's machine —
Lemma 6 (`Lem-6ˢ`), Theorem 5 (`Thm-5ˢ`) and type safety (`type-safetyˢ`, `wf-safetyˢ`,
`closed-safetyˢ`) at every configuration, with no hypothesis beyond local closure of the term,
which `wfˢ⇒lc` supplies. Nothing is assumed. What is spent: `wfˢ-subst≡-head`
(`MPSS/StackWfSubst`), `↦⇒⟶ᵉ*` and `↦⇒≥` (`MPSS/EvalChain`), narrowing and `wfˢ-fv`
(`MPSS/StackWfNarrow`, which rests on `≤-↣` of `MPSS/MachineNarrow`), and progress `Thm-4ˢ`
(`MPSS/StackWf`).
