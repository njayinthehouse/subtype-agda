# Faithfulness to the source: our λ⊲ is the paper's λ⊲

`PSS/` mechanizes **arXiv:2407.13882v1**, *Pure Subtype Systems Are Type-Safe*. Its Figure 2 is
titled "Subtyping and equivalence in System λ⊲" and its rule names are ours: `Srs-Prom`,
`Srs-Top`, `Srs-Eq`, `Srs-App`, `Srs-FunOp`, `Srs-Fun`, `As-Refl`, `As-Left`, `As-Right`,
`Ast-Sub`, `Ast-Trans`.

We deviate from the printed rules in exactly three places. This module proves each deviation
harmless, so that `type-safety` is the paper's theorem and not an artefact of the encoding.
A fourth deviation is at the level of theorem *statements*, not rules, and is recorded here
rather than discharged.

| deviation | status |
| --- | --- |
| `As-Left` split into `As-Left-1` / `As-Left-2` | the metavariable instantiation — proved identical |
| `⟶≡` drops the paper's `Γ ∣ s` index | proved vacuous — the two relations coincide |
| prevalidity carries extra `LC` premises | characterised exactly, and the `LC` hypothesis on `type-safety` is proved **redundant** |
| Theorem 4.4 and Lemma 5.7 stated over `≤*wf`, the paper states them over `≤*` | **recorded, not discharged** — see Deviation 4 below |

```agda
{-# OPTIONS --safe #-}

module PSS.Faithfulness where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.Scope using (StkLC; slc-nil; slc-cons; prevalid-stkLC)
open import PSS.Transitivity using (≤*wf⇒lcˡ; wf⇒lc; Thm-4·3)
open import PSS.WellFormed using (_∣_⊢_≤*wf_; _∣_⊢_wf)
open import PSS.Progress using (Thm-4·1)
open import PSS.Preservation using (Thm-4·2; type-safety)
```

## Deviation 1 — `As-Left`

The paper writes `⊲` as a **metavariable** ranging over `≤` and `≡`, so its single `As-Left`

> `Γ ∣ s ⊢ v ⟶⊲ v'  →  Γ ∣ s ⊢ v' ⊲ t  →  Γ ∣ s ⊢ v ⊲ t`

is two rules once the metavariable is instantiated: the step relation is `⟶≤` in the subtyping
reading and `⟶≡` in the equivalence reading. Our `⊲` is already mode-indexed, so we can define
the step relation the metavariable denotes and recover the paper's rule verbatim.

```agda
_∣_⊢_⟶[_]_ : Ctx → Stack → Tm → Mode → Tm → Set
Γ ∣ s ⊢ v ⟶[ sub ] v' = Γ ∣ s ⊢ v ⟶≤ v'
Γ ∣ s ⊢ v ⟶[ eqv ] v' = v ⟶≡ v'

As-Left-paper : ∀ {Γ s v v' t m}
              → Γ ∣ s ⊢ v ⟶[ m ] v'
              → Γ ∣ s ⊢ v' ⊲[ m ] t
              → Γ ∣ s ⊢ v  ⊲[ m ] t
As-Left-paper {m = sub} st d = As-Left-1 st d
As-Left-paper {m = eqv} st d = As-Left-2 st d
```

And the split constructors are not merely derivable from it — they *are* it, on the nose.

```agda
As-Left-1-is-paper : ∀ {Γ s v v' t} (st : Γ ∣ s ⊢ v ⟶≤ v') (d : Γ ∣ s ⊢ v' ⊲[ sub ] t)
                   → As-Left-paper {m = sub} st d ≡ As-Left-1 st d
As-Left-1-is-paper st d = refl

As-Left-2-is-paper : ∀ {Γ s v v' t} (st : v ⟶≡ v') (d : Γ ∣ s ⊢ v' ⊲[ eqv ] t)
                   → As-Left-paper {m = eqv} st d ≡ As-Left-2 st d
As-Left-2-is-paper st d = refl
```

So the split adds nothing and loses nothing; it is the instantiation the paper's notation
abbreviates.

## Deviation 2 — the index on equivalence reduction

The paper's equivalence reduction is written `Γ ∣ s ⊢ u ⟶≡ v`. Ours is `u ⟶≡ v`. Transcribing
the paper's judgement exactly — index threaded through every rule, as printed — makes the reason
visible: **no rule ever reads the index.** Unlike the `Srs-*` rules there is not even a
prevalidity premise, and unlike `Srs-Fun` the abstraction rule does not extend the context.

```agda
infix 3 _∣_⊢_⟶≡ᵢ_
data _∣_⊢_⟶≡ᵢ_ : Ctx → Stack → Tm → Tm → Set where
  iCr-Var    : ∀ {Γ s x} → Γ ∣ s ⊢ fvar x ⟶≡ᵢ fvar x
  iCr-Top    : ∀ {Γ s} → Γ ∣ s ⊢ Top ⟶≡ᵢ Top
  iCr-App    : ∀ {Γ s u u' v v'}
             → Γ ∣ s ⊢ u ⟶≡ᵢ u' → Γ ∣ s ⊢ v ⟶≡ᵢ v'
             → Γ ∣ s ⊢ app u v ⟶≡ᵢ app u' v'
  iCr-Fun    : ∀ {Γ s t t' u u'} (L : List Name)
             → Γ ∣ s ⊢ t ⟶≡ᵢ t'
             → (∀ {x} → x ∉ L → Γ ∣ s ⊢ (u ^ fvar x) ⟶≡ᵢ (u' ^ fvar x))
             → Γ ∣ s ⊢ lam t u ⟶≡ᵢ lam t' u'
  iCr-Beta   : ∀ {Γ s t u u' v v'} (L : List Name)
             → (∀ {x} → x ∉ L → Γ ∣ s ⊢ (u ^ fvar x) ⟶≡ᵢ (u' ^ fvar x))
             → Γ ∣ s ⊢ v ⟶≡ᵢ v'
             → Γ ∣ s ⊢ app (lam t u) v ⟶≡ᵢ (u' ^ v')
  iCr-TopApp : ∀ {Γ s u} → Γ ∣ s ⊢ app Top u ⟶≡ᵢ Top
```

The index is vacuous: the indexed relation holds at *some* extended context exactly when the
unindexed one holds, and then it holds at *every* extended context.

```agda
⟶≡ᵢ⇒⟶≡ : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶≡ᵢ v → u ⟶≡ v
⟶≡ᵢ⇒⟶≡ iCr-Var           = Cr-Var
⟶≡ᵢ⇒⟶≡ iCr-Top           = Cr-Top
⟶≡ᵢ⇒⟶≡ (iCr-App d e)     = Cr-App (⟶≡ᵢ⇒⟶≡ d) (⟶≡ᵢ⇒⟶≡ e)
⟶≡ᵢ⇒⟶≡ (iCr-Fun L d F)   = Cr-Fun L (⟶≡ᵢ⇒⟶≡ d) (λ x∉ → ⟶≡ᵢ⇒⟶≡ (F x∉))
⟶≡ᵢ⇒⟶≡ (iCr-Beta {u' = u'} L F e) =
  Cr-Beta {u' = u'} L (λ x∉ → ⟶≡ᵢ⇒⟶≡ (F x∉)) (⟶≡ᵢ⇒⟶≡ e)
⟶≡ᵢ⇒⟶≡ iCr-TopApp        = Cr-TopApp

⟶≡⇒⟶≡ᵢ : ∀ {Γ s u v} → u ⟶≡ v → Γ ∣ s ⊢ u ⟶≡ᵢ v
⟶≡⇒⟶≡ᵢ Cr-Var           = iCr-Var
⟶≡⇒⟶≡ᵢ Cr-Top           = iCr-Top
⟶≡⇒⟶≡ᵢ (Cr-App d e)     = iCr-App (⟶≡⇒⟶≡ᵢ d) (⟶≡⇒⟶≡ᵢ e)
⟶≡⇒⟶≡ᵢ (Cr-Fun L d F)   = iCr-Fun L (⟶≡⇒⟶≡ᵢ d) (λ x∉ → ⟶≡⇒⟶≡ᵢ (F x∉))
⟶≡⇒⟶≡ᵢ (Cr-Beta {u' = u'} L F e) =
  iCr-Beta {u' = u'} L (λ x∉ → ⟶≡⇒⟶≡ᵢ (F x∉)) (⟶≡⇒⟶≡ᵢ e)
⟶≡⇒⟶≡ᵢ Cr-TopApp        = iCr-TopApp

⟶≡-index-irrelevant : ∀ {Γ s Γ' s' u v} → Γ ∣ s ⊢ u ⟶≡ᵢ v → Γ' ∣ s' ⊢ u ⟶≡ᵢ v
⟶≡-index-irrelevant d = ⟶≡⇒⟶≡ᵢ (⟶≡ᵢ⇒⟶≡ d)
```

Dropping the index is therefore sound and complete, not a simplification of the system.

## Deviation 3 — local closure in prevalidity

The paper's prevalidity, transcribed exactly. `P-Ctx2` requires `x ∉ dom Γ` and
`fv t ⊆ dom Γ`; `P-Ctx3` requires `fv α ⊆ dom Γ`. There is no local-closure premise, because in
a named presentation every context entry is a term by construction.

```agda
infix 3 _∣_prevalidᵥ
data _∣_prevalidᵥ : Ctx → Stack → Set where
  V-Ctx1 : [] ∣ [] prevalidᵥ
  V-Ctx2 : ∀ {Γ x t}
         → Γ ∣ [] prevalidᵥ → x ∉ dom Γ → fv t ⊑ dom Γ
         → ((x , t) ∷ Γ) ∣ [] prevalidᵥ
  V-Ctx3 : ∀ {Γ s α}
         → Γ ∣ s prevalidᵥ → fv α ⊑ dom Γ
         → Γ ∣ (α ∷ s) prevalidᵥ
```

Locally nameless syntax admits raw terms with dangling indices, so "is a term" has to be said.
Our prevalidity is exactly the paper's *restricted to locally closed data* — both directions.

```agda
data CtxLC : Ctx → Set where
  clc-nil  : CtxLC []
  clc-cons : ∀ {Γ x t} → LC t → CtxLC Γ → CtxLC ((x , t) ∷ Γ)

prevalid⇒ᵥ : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ s prevalidᵥ
prevalid⇒ᵥ P-Ctx1                = V-Ctx1
prevalid⇒ᵥ (P-Ctx2 pv x∉ _ fvt)  = V-Ctx2 (prevalid⇒ᵥ pv) x∉ fvt
prevalid⇒ᵥ (P-Ctx3 pv _ fvα)     = V-Ctx3 (prevalid⇒ᵥ pv) fvα

prevalid⇒ctxLC : ∀ {Γ s} → Γ ∣ s prevalid → CtxLC Γ
prevalid⇒ctxLC P-Ctx1                = clc-nil
prevalid⇒ctxLC (P-Ctx2 pv _ lt _)    = clc-cons lt (prevalid⇒ctxLC pv)
prevalid⇒ctxLC (P-Ctx3 pv _ _)       = prevalid⇒ctxLC pv

ᵥ+LC⇒prevalid : ∀ {Γ s} → Γ ∣ s prevalidᵥ → CtxLC Γ → StkLC s → Γ ∣ s prevalid
ᵥ+LC⇒prevalid V-Ctx1 _ _ = P-Ctx1
ᵥ+LC⇒prevalid (V-Ctx2 pv x∉ fvt) (clc-cons lt clc) sl =
  P-Ctx2 (ᵥ+LC⇒prevalid pv clc slc-nil) x∉ lt fvt
ᵥ+LC⇒prevalid (V-Ctx3 pv fvα) clc (slc-cons lα sl) =
  P-Ctx3 (ᵥ+LC⇒prevalid pv clc sl) lα fvα
```

So the deviation is precisely "restrict to locally closed data", which the named presentation
assumes silently rather than states.

## The theorems, with no encoding hypothesis

The one place the deviations could still weaken the results is the `LC` premise carried by the
numbered theorems. It does not: local closure of the subject is *derivable* from
well-formedness, so every such premise is redundant and can be discharged. Below, each statement
is v1's as printed.

> **Theorem 4.1 (Progress).** Let `C` be a term. For every extended context `Γ ∣ B`, if
> `Γ ∣ B ⊢ C wf` then either `C` is in normal form, or there exists a term `C'` such that
> `C ↦ C'`.

```agda
Thm-4·1-paper : ∀ {Γ s t} → Γ ∣ s ⊢ t wf → (NF t) ⊎ (∃[ t' ] (t ↦ t'))
Thm-4·1-paper d = Thm-4·1 (wf⇒lc d) d
```

> **Theorem 4.2 (Preservation).** Let `Γ ∣ B` be an extended context. Let `C`, `C'` and `D` be
> terms. If `Γ ∣ B ⊢ C ≤*wf D` and `C ↦ C'`, then `Γ ∣ B ⊢ C' ≤*wf D`.

```agda
Thm-4·2-paper : ∀ {Γ s t t' u} → Γ ∣ s ⊢ t ≤*wf u → t ↦ t' → Γ ∣ s ⊢ t' ≤*wf u
Thm-4·2-paper d st = Thm-4·2 (≤*wf⇒lcˡ d) d st
```

> **Theorem 4.3 (No supertype of `Top`).** Let `Γ ∣ B` be an extended context. Let `λx≤C.D` be a
> term. We cannot have `Γ ∣ B ⊢ Top ≤*wf λx≤C.D`.

Ours already carries no encoding premise:

```agda
Thm-4·3-paper : ∀ {Γ s t u} → ¬ (Γ ∣ s ⊢ Top ≤*wf lam t u)
Thm-4·3-paper = Thm-4·3
```

Their combination, which is what "type safety" names:

```agda
type-safety-paper : ∀ {Γ s t u}
                  → Γ ∣ s ⊢ t ≤*wf u
                  → (NF t) ⊎ (∃[ t' ] ((t ↦ t') × (Γ ∣ s ⊢ t' ≤*wf u)))
type-safety-paper d = type-safety (≤*wf⇒lcˡ d) d
```

## What this establishes

Theorems 4.1, 4.2 and 4.3 are stated here exactly as v1 prints them, with **no hypothesis the
paper does not have**, and `type-safety-paper` is their combination. Theorem 4.4 and Lemma 5.7
are **not** yet stated as printed (Deviation 4). The three deviations from the printed rules are
each proved inert:

1. `As-Left`'s split is the metavariable instantiation, identical on the nose.
2. The `Γ ∣ s` index on `⟶≡` is never read by any rule, and the indexed and unindexed relations
   are inter-derivable.
3. Prevalidity's `LC` premises characterise exactly the locally closed fragment, and the
   subject's local closure is recovered from well-formedness rather than assumed.

## Deviation 4 — Theorem 4.4 and Lemma 5.7 are stated over `≤*wf`

v1 prints both over plain transitive subtyping:

> **Theorem 4.4.** If `Γ;s ⊢ u ≤* v` then `Γ;s ⊢ u ≤ v`.
>
> **Lemma 5.7.** If `Γ;s ⊢ (λx≤t.u) ≤* (λx≤t′.u′)` then `Γ;s ⊢ t ≡ t′`.

`Thm-4·4` in `PSS/Transitivity` and `Lem-5·7` in `PSS/Minimal` take `≤*wf` instead, which puts a
well-formedness premise on every intermediate term of the transitive chain. That is a strictly
stronger hypothesis than the paper's. The reason is again local closure: `⊲*` on raw syntax can
pass through non-terms (`Cr-TopApp` fires on `app Top u` for any `u`), and binary transitivity
needs the middle term locally closed. The paper's named presentation has that for free. The
faithful transcription is a transitive closure whose `Ast-Trans` carries `LC` of its middle term,
over which both statements follow from `⊲-trans` with no new ideas. **That form is owed**; until
it lands, 4.4 and 5.7 are mechanized only in the shape §4 consumes them, not as printed.

## The remaining gap

The gap between this and the paper that will not close is the binding representation itself —
locally nameless with cofinite quantification, versus the paper's named binders with a variable
convention. That is `../PLAN.md` D1, and it is the standard trade.

**On arXiv v2 (CSL 2026).** v2 replaces λ⊲ by a different system, MPSS, and proves progress and
preservation for it only *conditionally*, on its Conjecture 8 (`../PLAN.md`, "Conjecture 8").
Its abstract does not describe v1's argument as flawed; it says the original type-safety attempt
— Hutchins' — rested on a conjectured commutativity. So the accurate comparison is: v1 claimed
type safety unconditionally for λ⊲, v2 claims it conditionally for MPSS, and
`type-safety-paper` is an unconditional machine-checked proof for v1's system as printed, subject
to the four deviations above.
