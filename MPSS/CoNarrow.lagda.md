# MPSS: narrowing inside a covariant context

Lemma 24's third conclusion — that the narrowed promotion's target is well-formed — reduces to
this: replacing `t` by an equivalence-reduct `t′` inside a covariant context preserves
well-formedness. `MPSS/AUDIT` records why the paper's own argument for it does not work; this is
the route sketched there, carried out.

Two facts are proved together, by induction on the well-formedness derivation:

- `Co-step`, that `Co[t] ⟶≡ Co[t′]` — the congruence of `⟶≡` through a covariant context;
- `Co-wf`, that `Co[t′]` is well-formed when `Co[t]` is.

They have to be simultaneous. `Co-wf`'s application case needs `Co′[t] ≤*wf λy≤z.Top` moved to
`Co′[t′] ≤*wf λy≤z.Top`, and `push≡*wf` does that only when handed the step; `Co-step`'s
abstraction case needs the family under the binder, which is where the well-formedness derivation
supplies the fresh names.

The abstraction case recurses at a *different* covariant context: `(Co[t]) ^ z` is `(Co ^ z)[t]`,
since opening reaches the context's own terms and leaves the locally closed plug alone. That is
not a structural subterm, and neither is the well-formedness derivation available at the
application node, where the operator's is extracted from a subtyping premise rather than being
one. Both recursions do shrink the context's *depth*, though, and opening preserves it, so that
is the measure carried.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CoNarrow where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug)
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.Narrow using (wf-fv)
open import MPSS.StackPush using (⟶ᵉ-refl; pushᵉ)
open import MPSS.Weakening using (⟶ᵉ-weaken; wf-weaken₁)
open import MPSS.Preservation using (push≡*wf)

open import PSS.Syntax using (open-lc-id; ∉-++ˡ; ∉-++ʳ)
```

## Opening a covariant context

Opening reaches the context's own terms and leaves a locally closed plug alone.

```agda
openCo : ℕ → Tm → CoCtx → CoCtx
openCo k u ∙            = ∙
openCo k u (co-fun t C) = co-fun (openRec k u t) (openCo (suc k) u C)
openCo k u (co-app C v) = co-app (openCo k u C) (openRec k u v)

plug-open : ∀ C k z {w} → LC w → openRec k (fvar z) (plug C w) ≡ plug (openCo k (fvar z) C) w
plug-open ∙            k z lw = sym (open-lc-id lw k (fvar z))
plug-open (co-fun t C) k z lw = cong (lam (openRec k (fvar z) t)) (plug-open C (suc k) z lw)
plug-open (co-app C v) k z lw = cong (λ q → app q (openRec k (fvar z) v)) (plug-open C k z lw)
```

Its depth, which opening leaves alone, is the measure both recursions shrink.

```agda
coSize : CoCtx → ℕ
coSize ∙            = zero
coSize (co-fun _ C) = suc (coSize C)
coSize (co-app C _) = suc (coSize C)

coSize-open : ∀ k u C → coSize (openCo k u C) ≡ coSize C
coSize-open k u ∙            = refl
coSize-open k u (co-fun t C) = cong suc (coSize-open (suc k) u C)
coSize-open k u (co-app C v) = cong suc (coSize-open k u C)
```

## The two facts

```agda
Co-step : ∀ {Γ t t'} n C → coSize C ≤ n
        → Γ ⊢ plug C t wf
        → Γ ∣ [] ⊢ t ⟶ᵉ t'
        → LC t → LC t'
        → Γ ∣ [] ⊢ plug C t ⟶ᵉ plug C t'

Co-wf : ∀ {Γ t t'} n C → coSize C ≤ n
      → Γ ⊢ plug C t wf
      → Γ ∣ [] ⊢ t ⟶ᵉ t'
      → Γ ⊢ t' wf
      → LC t → LC t'
      → Γ ⊢ plug C t' wf
```

**The congruence.** At an application node the operator's step has to be re-taken at the pushed
stack, which is `pushᵉ`; the operand stays put, by reflexivity. At an abstraction node the
annotation stays put the same way, and the body's family comes from the well-formedness
derivation's own.

```agda
Co-step n ∙ le w e lt lt' = e
Co-step {Γ} {t} {t'} (suc n) (co-app C v) (s≤s le) (Wf-App d₁ d₂) e lt lt' =
  Me-App (pushᵉ (Co-step n C le (⊑*wf⇒wfˡ d₁) e lt lt') (Pv-Sta (Pv-Nil pv) lv fv'))
         (⟶ᵉ-refl (Pv-Nil pv) lv fv')
  where
    wv  = ⊑*wf⇒wfˡ d₂
    pv  = wf⇒prevalid wv
    lv  = wf⇒lc wv
    fv' = wf-fv wv
Co-step {Γ} {t} {t'} (suc n) (co-fun w C) (s≤s le) (Wf-Fun L F ww) e lt lt' =
  Me-Fun (L ++ dom Γ) (⟶ᵉ-refl (Pv-Nil (wf⇒prevalid ww)) (wf⇒lc ww) (wf-fv ww)) fam
  where
    fam : ∀ {z} → z ∉ (L ++ dom Γ)
        → ((z , sub , w) ∷ Γ) ∣ [] ⊢ ((plug C t) ^ fvar z) ⟶ᵉ ((plug C t') ^ fvar z)
    fam {z} z∉ = tr (Co-step n (openCo 0 (fvar z) C) le' (tr₀ (F (∉-++ˡ z∉))) e' lt lt')
      where
        pvz = wf⇒prevalid (F (∉-++ˡ z∉))
        e'  = ⟶ᵉ-weaken [] ((z , sub , w) ∷ []) (Pv-Nil pvz) e
        le' : coSize (openCo 0 (fvar z) C) ≤ n
        le' = subst (_≤ n) (sym (coSize-open 0 (fvar z) C)) le

        tr₀ : ((z , sub , w) ∷ Γ) ⊢ ((plug C t) ^ fvar z) wf
            → ((z , sub , w) ∷ Γ) ⊢ plug (openCo 0 (fvar z) C) t wf
        tr₀ h rewrite sym (plug-open C 0 z lt) = h

        tr : ((z , sub , w) ∷ Γ) ∣ [] ⊢ plug (openCo 0 (fvar z) C) t
                                          ⟶ᵉ plug (openCo 0 (fvar z) C) t'
           → ((z , sub , w) ∷ Γ) ∣ [] ⊢ ((plug C t) ^ fvar z) ⟶ᵉ ((plug C t') ^ fvar z)
        tr h rewrite plug-open C 0 z lt | plug-open C 0 z lt' = h
```

**Well-formedness.** The application node is the only one that consults a subtyping derivation,
and `push≡*wf` is what carries it across the step the congruence supplies.

```agda
Co-wf n ∙ le w e wt' lt lt' = wt'
Co-wf {Γ} {t} {t'} (suc n) (co-app C v) (s≤s le) (Wf-App d₁ d₂) e wt' lt lt' =
  Wf-App (push≡*wf (Co-step n C le (⊑*wf⇒wfˡ d₁) e lt lt') d₁
                   (Co-wf n C le (⊑*wf⇒wfˡ d₁) e wt' lt lt'))
         d₂
Co-wf {Γ} {t} {t'} (suc n) (co-fun w C) (s≤s le) (Wf-Fun L F ww) e wt' lt lt' =
  Wf-Fun (L ++ dom Γ) fam ww
  where
    fam : ∀ {z} → z ∉ (L ++ dom Γ) → ((z , sub , w) ∷ Γ) ⊢ ((plug C t') ^ fvar z) wf
    fam {z} z∉ = tr (Co-wf n (openCo 0 (fvar z) C) le' (tr₀ (F (∉-++ˡ z∉))) e' wt'' lt lt')
      where
        pvz  = wf⇒prevalid (F (∉-++ˡ z∉))
        e'   = ⟶ᵉ-weaken [] ((z , sub , w) ∷ []) (Pv-Nil pvz) e
        wt'' = wf-weaken₁ pvz wt'
        le' : coSize (openCo 0 (fvar z) C) ≤ n
        le' = subst (_≤ n) (sym (coSize-open 0 (fvar z) C)) le

        tr₀ : ((z , sub , w) ∷ Γ) ⊢ ((plug C t) ^ fvar z) wf
            → ((z , sub , w) ∷ Γ) ⊢ plug (openCo 0 (fvar z) C) t wf
        tr₀ h rewrite sym (plug-open C 0 z lt) = h

        tr : ((z , sub , w) ∷ Γ) ⊢ plug (openCo 0 (fvar z) C) t' wf
           → ((z , sub , w) ∷ Γ) ⊢ ((plug C t') ^ fvar z) wf
        tr h rewrite plug-open C 0 z lt' = h
```

Applied at the context's own depth, the fuel is invisible.

```agda
Co-step′ : ∀ {Γ t t'} C → Γ ⊢ plug C t wf → Γ ∣ [] ⊢ t ⟶ᵉ t' → LC t → LC t'
         → Γ ∣ [] ⊢ plug C t ⟶ᵉ plug C t'
Co-step′ C = Co-step (coSize C) C ≤-refl

Co-wf′ : ∀ {Γ t t'} C → Γ ⊢ plug C t wf → Γ ∣ [] ⊢ t ⟶ᵉ t' → Γ ⊢ t' wf → LC t → LC t'
       → Γ ⊢ plug C t' wf
Co-wf′ C = Co-wf (coSize C) C ≤-refl
```

## What this establishes

Lemma 24's third conclusion, on the branch where it has content: when the narrowed promotion's
target really does move, from `Co[t]` to `Co[t′]`, the new target is well-formed. Together with
`MPSS/Narrow24`'s split — where the other branch leaves the target alone and inherits its
well-formedness from the hypothesis — this is the ingredient Lemma 23 was missing.
