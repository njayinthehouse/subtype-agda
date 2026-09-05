# MPSS: what a context reduction carries

Two facts about `↣` that the commutation theorem needs at its leaves, and that nothing else in the
development has had to state: a reduced extended context is still prevalid, and a subtype
annotation survives the reduction as a reduct of itself.

The second is the `Ct-Ann` extraction the paper performs by hand — "because `Γ₀` is of the form
`Γ₀′, x ≡ α₀, Γ₀″`, we have `Γ₂ = Γ₂′, x ≡ α₂, Γ₂″`" — packaged as a lemma so that the case
using it does not have to take the context apart.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CtxReduce where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ-dom)
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Weakening using (⟶ᵉ-weaken)
```

## Prevalidity survives a reduction

Domains are untouched by `↣`, so every scoping side condition transfers by rewriting; each
annotation and each stack entry is replaced by a reduct, which is locally closed and scoped
wherever the original was.

```agda
↣-ctx : ∀ {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → Γ prevalid → Γ' prevalid
↣-ctx Ct-Refl      pv = pv
↣-ctx (Ct-Stk d _) pv = ↣-ctx d pv
↣-ctx (Ct-Ann {c = sub} d e) (Pv-Ctx pv x∉ lt ft) =
  Pv-Ctx (↣-ctx d pv)
         (λ h → x∉ (subst (_ ∈_) (sym (↣-dom d)) h))
         (⟶ᵉ-lc lt e)
         (λ h → subst (_ ∈_) (↣-dom d) (fv-⟶ᵉ-dom e ft h))
↣-ctx (Ct-Ann {c = eqv} d e) (Pv-EqA pv x∉ lt ft) =
  Pv-EqA (↣-ctx d pv)
         (λ h → x∉ (subst (_ ∈_) (sym (↣-dom d)) h))
         (⟶ᵉ-lc lt e)
         (λ h → subst (_ ∈_) (↣-dom d) (fv-⟶ᵉ-dom e ft h))

↣-nil : ∀ {Γ Γ' s'} → Γ ∣ [] ↣ Γ' ∣ s' → s' ≡ []
↣-nil Ct-Refl      = refl
↣-nil (Ct-Ann d _) = ↣-nil d
```

**Prevalidity along a reduction is not proved here, and the reason is a fact about `↣` worth
recording.** `PSS/Scope` proves the corresponding lemma for v1 by projecting the reduction into a
context part and a stack part and transferring each separately, which works there because v1's
`⟶≡` is context-free. In MPSS the projection does not survive `Ct-Ann`:

> `Ct-Ann : Γ ∣ s ↣ Γ' ∣ s' → Γ ∣ [] ⊢ t ⟶ᵉ t' → ((x , c , t) ∷ Γ) ∣ s ↣ ((x , c , t') ∷ Γ') ∣ s'`

The stack is reduced by the premise, at the **tail** context `Γ`, so every stack entry must be
scoped in `dom Γ`. But the conclusion's prevalidity scopes those same entries in
`dom ((x , c , t) ∷ Γ)`, which is `x ∷ dom Γ`. The two disagree exactly on entries mentioning `x`,
and `Pv-Sta` permits them.

So `↣` silently restricts to stacks that do not mention the variables bound to its right, and the
transfer is not the routine fact it looks like. `MPSS/Commutation` takes it as a hypothesis rather
than assume that restriction is harmless.

## An annotation survives as a reduct of itself

```agda
↣-sub : ∀ {Γ s Γ' s' x t} → Γ prevalid → Γ ∣ s ↣ Γ' ∣ s' → x ≤ t ∈ Γ
      → ∃[ t' ] ((x ≤ t' ∈ Γ') × (Γ ∣ [] ⊢ t ⟶ᵉ t'))
↣-sub {t = t} pv Ct-Refl m =
  t , m , ⟶ᵉ-refl (Pv-Nil pv) (prevalid-bound-lc pv m) (prevalid-bound-fv pv m)
↣-sub pv (Ct-Stk d _) m = ↣-sub pv d m
↣-sub {x = x} pv (Ct-Ann {x = y} {c = c} {t = t₀} d e) (here refl) =
  _ , here refl , ⟶ᵉ-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e
↣-sub pv (Ct-Ann {x = y} {c = c} {t = t₀} d e) (there m)
  with ↣-sub (tail-prevalid pv) d m
... | t' , m' , e' =
      t' , there m' , ⟶ᵉ-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e'

↣-empty : ∀ {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → Γ ∣ [] ↣ Γ' ∣ []
↣-empty Ct-Refl      = Ct-Refl
↣-empty (Ct-Ann d e) = Ct-Ann (↣-empty d) e
↣-empty (Ct-Stk d _) = ↣-empty d

↣-eqv : ∀ {Γ s Γ' s' x α} → Γ prevalid → Γ ∣ s ↣ Γ' ∣ s' → x ≐ α ∈ Γ
      → ∃[ α' ] ((x ≐ α' ∈ Γ') × (Γ ∣ [] ⊢ α ⟶ᵉ α'))
↣-eqv {α = α} pv Ct-Refl m =
  α , m , ⟶ᵉ-refl (Pv-Nil pv) (prevalid-bound-lc pv m) (prevalid-bound-fv pv m)
↣-eqv pv (Ct-Stk d _) m = ↣-eqv pv d m
↣-eqv pv (Ct-Ann {x = y} {c = c} {t = t₀} d e) (here refl) =
  _ , here refl , ⟶ᵉ-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e
↣-eqv pv (Ct-Ann {x = y} {c = c} {t = t₀} d e) (there m)
  with ↣-eqv (tail-prevalid pv) d m
... | α' , m' , e' =
      α' , there m' , ⟶ᵉ-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e'
```

## What this establishes

`↣-prevalid`, `↣-sub` and `↣-eqv` — what a leaf of the commutation and diamond proofs reads off a
context reduction. `↣-eqv` is `↣-sub` verbatim with the annotation kind changed; neither proof ever
inspects the kind, which is why the same argument serves both.
