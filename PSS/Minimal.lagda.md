# System λ⊲: Lemma 5.1 and Lemma 5.7

**Lemma 5.1** — minimal promotion is deterministic, so the minimal superpath is well defined.
**Lemma 5.7** — the inversion lemma: if one abstraction is a subtype of another, their
annotations are equivalent. This is what makes typechecking composable (Theorem 5.8).

```agda
{-# OPTIONS --safe #-}

module PSS.Minimal where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed
open import PSS.Close
open import PSS.Equivalence
open import PSS.Promotion using (prevalid-nil)
open import PSS.Scope
open import PSS.Commutation using (⟶≤-prevalid; ⟶≤-lc)
open import PSS.Transitivity using (Thm-4·4; wf⇒lc)
open import PSS.Narrowing
open import PSS.Confluence
open import PSS.Algorithms
```

## A prevalid context is functional

```agda
∈-dom : ∀ {Γ x t} → (x , t) ∈ Γ → x ∈ dom Γ
∈-dom (here refl) = here refl
∈-dom (there m)   = there (∈-dom m)

prevalid-functional : ∀ {Γ x t t'} → Γ ∣ [] prevalid
                    → (x , t) ∈ Γ → (x , t') ∈ Γ → t ≡ t'
prevalid-functional (P-Ctx2 p x∉ _ _) (here refl) (here refl) = refl
prevalid-functional (P-Ctx2 p x∉ _ _) (here refl) (there m)   = ⊥-elim (x∉ (∈-dom m))
prevalid-functional (P-Ctx2 p x∉ _ _) (there m)   (here refl) = ⊥-elim (x∉ (∈-dom m))
prevalid-functional (P-Ctx2 p _ _ _)  (there m)   (there m')  = prevalid-functional p m m'
```

## `Top` does not promote minimally

`Top` is already at the top of every superpath.

```agda
no-mp-Top : ∀ {Γ s v} → ¬ (Γ ∣ s ⊢ Top ⟶mp v)
no-mp-Top (mp-nf ¬nf _ _ _) = ¬nf nf-Top
```

## Lemma 5.1 — minimal promotion is deterministic

```agda
mp-unique : ∀ {Γ s u v v'} → LC u → Γ ∣ s ⊢ u ⟶mp v → Γ ∣ s ⊢ u ⟶mp v' → v ≡ v'

mp-unique lu (mp-nf _ _ c nf) (mp-nf _ _ c' nf') = nf-unique lu c c' nf nf'

mp-unique lu (mp-nf ¬nf _ _ _) (mp-var _ _)      = ⊥-elim (¬nf (nf-ne ne-var))
mp-unique lu (mp-nf ¬nf _ _ _) (mp-app ne nfv _) = ⊥-elim (¬nf (nf-ne (ne-app ne nfv)))
mp-unique lu (mp-nf ¬nf _ _ _) (mp-fun _ nf _)   = ⊥-elim (¬nf nf)
mp-unique lu (mp-nf ¬nf _ _ _) (mp-funop _ nf _) = ⊥-elim (¬nf nf)
mp-unique lu (mp-nf ¬nf _ _ _) (mp-top _ nf)     = ⊥-elim (¬nf nf)

mp-unique lu (mp-var _ _)      (mp-nf ¬nf _ _ _) = ⊥-elim (¬nf (nf-ne ne-var))
mp-unique lu (mp-app ne nfv _) (mp-nf ¬nf _ _ _) = ⊥-elim (¬nf (nf-ne (ne-app ne nfv)))
mp-unique lu (mp-fun _ nf _)   (mp-nf ¬nf _ _ _) = ⊥-elim (¬nf nf)
mp-unique lu (mp-funop _ nf _) (mp-nf ¬nf _ _ _) = ⊥-elim (¬nf nf)
mp-unique lu (mp-top _ nf)     (mp-nf ¬nf _ _ _) = ⊥-elim (¬nf nf)

mp-unique lu (mp-var pv m) (mp-var _ m') = prevalid-functional (prevalid-nil pv) m m'

mp-unique (lc-app lu lv) (mp-app _ _ d) (mp-app _ _ d') =
  cong (λ z → app z _) (mp-unique lu d d')

mp-unique (lc-lam {t} {u} L₀ lt F₀) (mp-fun {u' = a} L _ F) (mp-fun {u' = b} L' _ F') =
  cong (lam t) (open-inj 0 x a b x∉a x∉b (mp-unique (F₀ x∉L₀) (F x∉L) (F' x∉L')))
  where
    A  = L₀ ++ L ++ L' ++ fv a ++ fv b
    x  = fresh A
    a∉ = fresh-∉ A
    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ L' r₂
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉L' = ∉-++ˡ r₂
    x∉a : x ∉ fv a
    x∉a  = ∉-++ˡ r₃
    x∉b : x ∉ fv b
    x∉b  = ∉-++ʳ (fv a) r₃

mp-unique (lc-lam {t} {u} L₀ lt F₀) (mp-funop {u' = a} L _ F) (mp-funop {u' = b} L' _ F') =
  cong (lam t) (open-inj 0 x a b x∉a x∉b (mp-unique (F₀ x∉L₀) (F x∉L) (F' x∉L')))
  where
    A  = L₀ ++ L ++ L' ++ fv a ++ fv b
    x  = fresh A
    a∉ = fresh-∉ A
    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ L' r₂
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉L' = ∉-++ˡ r₂
    x∉a : x ∉ fv a
    x∉a  = ∉-++ˡ r₃
    x∉b : x ∉ fv b
    x∉b  = ∉-++ʳ (fv a) r₃

mp-unique lu (mp-top _ _) (mp-top _ _) = refl

mp-unique (lc-lam L₀ lt F₀) (mp-fun L _ F) (mp-top _ _) =
  ⊥-elim (no-mp-Top (F (fresh-∉ L)))
mp-unique (lc-lam L₀ lt F₀) (mp-top _ _) (mp-fun L _ F) =
  ⊥-elim (no-mp-Top (F (fresh-∉ L)))
mp-unique (lc-lam L₀ lt F₀) (mp-funop L _ F) (mp-top _ _) =
  ⊥-elim (no-mp-Top (F (fresh-∉ L)))
mp-unique (lc-lam L₀ lt F₀) (mp-top _ _) (mp-funop L _ F) =
  ⊥-elim (no-mp-Top (F (fresh-∉ L)))
```

## Promotion out of an abstraction

Every promotion step from an abstraction either keeps it an abstraction — with the annotation
either untouched (`Srs-Fun`, `Srs-FunOp`) or equivalence-reduced (`Srs-Eq` through `Cr-Fun`) —
or jumps to `Top` (`Srs-Top`). Iterating, a chain out of an abstraction ends at an abstraction
whose annotation is an equivalence-reduct, or at `Top`.

```agda
Top-only : ∀ {Γ s w} → Γ ∣ s ⊢ Top ⟶≤* w → w ≡ Top
Top-only εₚ                       = refl
Top-only (Srs-Top _ ◅ₚ c)         = Top-only c
Top-only (Srs-Eq _ Cr-Top ◅ₚ c)   = Top-only c

lam-promote* : ∀ {Γ s a b w} → Γ ∣ s ⊢ lam a b ⟶≤* w
             → (∃[ a' ] ∃[ b' ] ((w ≡ lam a' b') × (a ⟶≡* a'))) ⊎ (w ≡ Top)
lam-promote* εₚ                              = inj₁ (_ , _ , refl , εₑ)
lam-promote* (Srs-Top _ ◅ₚ c)                = inj₂ (Top-only c)
lam-promote* (Srs-Eq _ (Cr-Fun _ st _) ◅ₚ c) with lam-promote* c
... | inj₁ (a' , b' , refl , cc) = inj₁ (a' , b' , refl , (st ◅ₑ cc))
... | inj₂ p                     = inj₂ p
lam-promote* (Srs-Fun _ _ ◅ₚ c)              with lam-promote* c
... | inj₁ (a' , b' , refl , cc) = inj₁ (a' , b' , refl , cc)
... | inj₂ p                     = inj₂ p
lam-promote* (Srs-FunOp _ _ ◅ₚ c)            with lam-promote* c
... | inj₁ (a' , b' , refl , cc) = inj₁ (a' , b' , refl , cc)
... | inj₂ p                     = inj₂ p
```

An abstraction never equivalence-reduces to `Top`.

```agda
lam-⟶≡*-not-Top : ∀ {a b} → ¬ (lam a b ⟶≡* Top)
lam-⟶≡*-not-Top (Cr-Fun _ _ _ ◅ₑ c) = lam-⟶≡*-not-Top c
```

The annotation chain is read off a chain of `Cr-Fun` steps.

```agda
lam-⟶≡*-ann : ∀ {a b a' b'} → lam a b ⟶≡* lam a' b' → a ⟶≡* a'
lam-⟶≡*-ann εₑ                   = εₑ
lam-⟶≡*-ann (Cr-Fun _ st _ ◅ₑ c) = st ◅ₑ lam-⟶≡*-ann c
```

## Lemma 5.7 — the inversion lemma

If one abstraction is a subtype of another, their annotations are equivalent. Reading the
subtyping derivation diagrammatically, the promotion chain out of the left abstraction cannot
reach `Top` — the right-hand equivalence chain would then have to take an abstraction to `Top`,
which `Cr-Fun` cannot do. So both annotations reduce to a common one.

**Stated over `≤*wf`, not as printed.** v1's Lemma 5.7 has hypothesis `Γ;s ⊢ (λx≤t.u) ≤* (λx≤t′.u′)`,
over plain transitive subtyping. Ours takes `≤*wf` because it goes through `Thm-4·4`, which is
itself mechanized only in the `≤*wf` form. This is Deviation 4 in `PSS/Faithfulness`; the
printed form is owed together with the printed Theorem 4.4.

```agda
≋-left* : ∀ {Γ s u u' w} → Γ ∣ s ⊢ u' ≋ w → u ⟶≡* u' → Γ ∣ s ⊢ u ≋ w
≋-left* d εₑ       = d
≋-left* d (e ◅ₑ c) = As-Left-2 e (≋-left* d c)

≋-right* : ∀ {Γ s u t w} → Γ ∣ s ⊢ u ≋ w → t ⟶≡* w → Γ ∣ s ⊢ u ≋ t
≋-right* d εₑ       = d
≋-right* d (e ◅ₑ c) = As-Right (≋-right* d c) e

Lem-5·7 : ∀ {Γ s t u t' u'}
        → Γ ∣ s ⊢ lam t u ≤*wf lam t' u'
        → Γ ∣ s ⊢ t ≋ t'
Lem-5·7 d with ⊲⇒diag (Thm-4·4 d)
... | w , chain , c with lam-promote* chain
...   | inj₂ refl                  = ⊥-elim (lam-⟶≡*-not-Top c)
...   | inj₁ (a' , b' , refl , cc) =
        ≋-left* (≋-right* (As-Refl (≤*wf⇒prevalid d)) (lam-⟶≡*-ann c)) cc
```

## What this establishes

**Lemma 5.1** (minimal promotion is deterministic, so the minimal superpath is well defined;
`mp-unique` here — `PSS/MinimalUnique` later re-proved it as `Lem-5·1`, a duplicate) and
**Lemma 5.7** (the inversion lemma, in the `≤*wf` form). Existence of the minimal promotion is
*conditional*:
`mp-nf` requires the term to have a normal form, and λ⊲ is not normalising, so the algorithm
may fail to make a step — which is exactly the termination side condition the paper attaches to
Theorems 5.5 and 5.6.

### A finding about Definition 5.2

Definition 5.2 says a promotion `Γ;s ⊢ uₙ ⟶≤ v` is *minimal* when, for every `w` with
`Γ;s ⊢ uₙ ⟶≤ w`, also `Γ;s ⊢ v ⟶≤* w`. As printed this cannot hold. `Srs-Eq` with a reflexive
equivalence step gives `Γ;s ⊢ uₙ ⟶≤ uₙ` for any locally closed `uₙ`, so `w := uₙ` is always a
legal choice, and minimality would demand `Γ;s ⊢ v ⟶≤* uₙ` — which fails whenever `v` is
strictly above `uₙ`. Take `uₙ = x` with `x ≤ t ∈ Γ`: minimal promotion gives `v = t`, and `t`
does not promote back down to `x`.

The definition presumably means to quantify over *proper* promotions, i.e. to exclude the
reflexive `Srs-Eq` case. Lemma 5.3 is therefore left unmechanized rather than mechanized
against a statement that is refutable as written; the direction of it that the correctness
proofs actually consume — that a minimal-promotion step *is* a promotion — is `mp⇒⟶≤*` in
`PSS.Algorithms`.
