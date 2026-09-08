# MPSS: context reduction over the variant

Figure 3's context reduction `↣` with the variant `⟶ᵉ′` as the relation on the annotations and
stack entries. A variant context reduction is an original one, so every fact about the shape of a
reduced configuration — domain, stack length, prevalidity — comes through the embedding; what has
to be rebuilt is the replay of a lookup (`↣′-eqv`), since it produces a variant piece.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantCtx where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-ctx; ↣-nil)
open import MPSS.CtxPrevalid using (↣-prevalid)
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-weaken; ⟶ᵉ′-refl)
```

## The relation

```agda
infix 3 _∣_↣′_∣_
data _∣_↣′_∣_ : Ctx → Stack → Ctx → Stack → Set where

  Ct-Refl′ : ∀ {Γ s} → Γ ∣ s ↣′ Γ ∣ s

  Ct-Ann′  : ∀ {Γ s Γ' s' x c t t'}
           → Γ ∣ s ↣′ Γ' ∣ s'
           → Γ ∣ [] ⊢ t ⟶ᵉ′ t'
           → ((x , c , t) ∷ Γ) ∣ s ↣′ ((x , c , t') ∷ Γ') ∣ s'

  Ct-Stk′  : ∀ {Γ s Γ' s' α α'}
           → Γ ∣ s ↣′ Γ' ∣ s'
           → Γ ∣ [] ⊢ α ⟶ᵉ′ α'
           → Γ ∣ (α ∷ s) ↣′ Γ' ∣ (α' ∷ s')

↣′⊆↣ : ∀ {Γ s Γ' s'} → Γ ∣ s ↣′ Γ' ∣ s' → Γ ∣ s ↣ Γ' ∣ s'
↣′⊆↣ Ct-Refl′      = Ct-Refl
↣′⊆↣ (Ct-Ann′ c d) = Ct-Ann (↣′⊆↣ c) (⟶ᵉ′⊆⟶ᵉ d)
↣′⊆↣ (Ct-Stk′ c d) = Ct-Stk (↣′⊆↣ c) (⟶ᵉ′⊆⟶ᵉ d)
```

## Facts through the embedding

```agda
↣′-dom : ∀ {Γ s Γ' s'} → Γ ∣ s ↣′ Γ' ∣ s' → dom Γ ≡ dom Γ'
↣′-dom c = ↣-dom (↣′⊆↣ c)

↣′-nil : ∀ {Γ Γ' s'} → Γ ∣ [] ↣′ Γ' ∣ s' → s' ≡ []
↣′-nil c = ↣-nil (↣′⊆↣ c)

↣′-ctx : ∀ {Γ s Γ' s'} → Γ ∣ s ↣′ Γ' ∣ s' → Γ prevalid → Γ' prevalid
↣′-ctx c pv = ↣-ctx (↣′⊆↣ c) pv

↣′-prevalid : ∀ {Γ s Γ' s'} → Γ ∣ s prevalid → Γ ∣ s ↣′ Γ' ∣ s' → Γ' ∣ s' prevalid
↣′-prevalid pv c = ↣-prevalid pv (↣′⊆↣ c)
```

## Emptying the stack, and replaying a lookup

```agda
↣′-empty : ∀ {Γ s Γ' s'} → Γ ∣ s ↣′ Γ' ∣ s' → Γ ∣ [] ↣′ Γ' ∣ []
↣′-empty Ct-Refl′      = Ct-Refl′
↣′-empty (Ct-Ann′ d e) = Ct-Ann′ (↣′-empty d) e
↣′-empty (Ct-Stk′ d _) = ↣′-empty d

↣′-eqv : ∀ {Γ s Γ' s' x α} → Γ prevalid → Γ ∣ s ↣′ Γ' ∣ s' → x ≐ α ∈ Γ
       → ∃[ α' ] ((x ≐ α' ∈ Γ') × (Γ ∣ [] ⊢ α ⟶ᵉ′ α'))
↣′-eqv {α = α} pv Ct-Refl′ m =
  α , m , ⟶ᵉ′-refl (Pv-Nil pv) (prevalid-bound-lc pv m) (prevalid-bound-fv pv m)
↣′-eqv pv (Ct-Stk′ d _) m = ↣′-eqv pv d m
↣′-eqv pv (Ct-Ann′ {x = y} {c = c} {t = t₀} d e) (here refl) =
  _ , here refl , ⟶ᵉ′-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e
↣′-eqv pv (Ct-Ann′ {x = y} {c = c} {t = t₀} d e) (there m)
  with ↣′-eqv (tail-prevalid pv) d m
... | α' , m' , e' =
      α' , there m' , ⟶ᵉ′-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e'
```

## What this establishes

`↣′` with the four facts the variant's diamond reads off a context reduction: its domain and
stack shape, prevalidity of the reduced configuration, and the piece replaying a lookup.
