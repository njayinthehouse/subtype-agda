# MPSS: well-formedness and well-subtyping (v2 Figure 4)

The static system v2 §4 *sketches*. Everything here is transcribed from Figure 4, including the
extra well-formedness premises on `Ws-Lf2` that the paper adds when stating Conjecture 8 ("we
believe that the conjecture holds with the additional well-formedness requirements that both `v`
and `v'` are well-formed in `Γ` in Rule `Ws-Lf2`").

The three judgements are mutually inductive: `Wf-App` needs well-subtyping, and `Ws-Lf2` needs
well-formedness.

Note that all three are stated over a **logical** context only — the paper writes `Γ ⊢ t wf`,
and the reduction premises are taken at the empty stack. That detail is what Conjecture 8 turns
on.

```agda
{-# OPTIONS --safe #-}

module MPSS.WellFormed where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.Subtyping public
open import PSS.Reduction using (_↦_; E-App; E-App-l; E-App-r; E-Lam-l; E-Lam-r; NF) public
```

## The three judgements

```agda
infix 3 _⊢_wf _⊢_⊑wf[_]_ _⊢_⊑*wf[_]_

data _⊢_wf       : Ctx → Tm → Set
data _⊢_⊑wf[_]_  : Ctx → Tm → Mode → Tm → Set
data _⊢_⊑*wf[_]_ : Ctx → Tm → Mode → Tm → Set

data _⊢_wf where

  Wf-PrS : ∀ {Γ x t}
         → Γ prevalid → x ≤ t ∈ Γ
         → Γ ⊢ fvar x wf

  Wf-PrE : ∀ {Γ x α}
         → Γ prevalid → x ≐ α ∈ Γ
         → Γ ⊢ fvar x wf

  Wf-Top : ∀ {Γ}
         → Γ prevalid
         → Γ ⊢ Top wf

  Wf-Fun : ∀ {Γ t u} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ⊢ (u ^ fvar x) wf)
         → Γ ⊢ t wf
         → Γ ⊢ lam t u wf

  Wf-App : ∀ {Γ u v t}
         → Γ ⊢ u ⊑*wf[ sub-m ] lam t Top
         → Γ ⊢ v ⊑*wf[ sub-m ] t
         → Γ ⊢ app u v wf

data _⊢_⊑wf[_]_ where

  Ws-Rfl : ∀ {Γ t m}
         → Γ prevalid
         → Γ ⊢ t ⊑wf[ m ] t

  Ws-Lf1 : ∀ {Γ v v' t m}
         → Γ ∣ [] ⊢ v ⟶ᵉ v'
         → Γ ⊢ v' ⊑wf[ m ] t
         → Γ ⊢ v  ⊑wf[ m ] t

  Ws-Lf2 : ∀ {Γ v v' t}
         → Γ ⊢ v wf
         → Γ ∣ [] ⊢ v ⟶ˢ v'
         → Γ ⊢ v' wf
         → Γ ⊢ v' ⊑wf[ sub-m ] t
         → Γ ⊢ v  ⊑wf[ sub-m ] t

  Ws-Rgh : ∀ {Γ v t t' m}
         → Γ ⊢ v ⊑wf[ m ] t'
         → Γ ∣ [] ⊢ t ⟶ᵉ t'
         → Γ ⊢ v ⊑wf[ m ] t

data _⊢_⊑*wf[_]_ where

  Ws-Sub : ∀ {Γ v t m}
         → Γ ⊢ v wf
         → Γ ⊢ v ⊑wf[ m ] t
         → Γ ⊢ t wf
         → Γ ⊢ v ⊑*wf[ m ] t

  Ws-Trs : ∀ {Γ v u t m}
         → Γ ⊢ v ⊑*wf[ m ] u
         → Γ ⊢ u wf
         → Γ ⊢ u ⊑*wf[ m ] t
         → Γ ⊢ v ⊑*wf[ m ] t
```

Abbreviations matching the paper's notation.

```agda
infix 3 _⊢_≤wf_ _⊢_≤*wf_

_⊢_≤wf_ : Ctx → Tm → Tm → Set
Γ ⊢ v ≤wf t = Γ ⊢ v ⊑wf[ sub-m ] t

_⊢_≤*wf_ : Ctx → Tm → Tm → Set
Γ ⊢ v ≤*wf t = Γ ⊢ v ⊑*wf[ sub-m ] t
```

## Prevalidity is recoverable

```agda
wf⇒prevalid  : ∀ {Γ t} → Γ ⊢ t wf → Γ prevalid
⊑wf⇒prevalid : ∀ {Γ v t m} → Γ ⊢ v ⊑wf[ m ] t → Γ prevalid

wf⇒prevalid (Wf-PrS pv _)  = pv
wf⇒prevalid (Wf-PrE pv _)  = pv
wf⇒prevalid (Wf-Top pv)    = pv
wf⇒prevalid (Wf-Fun L F d) = wf⇒prevalid d
wf⇒prevalid (Wf-App d _)   = go d
  where
    go : ∀ {Γ v t m} → Γ ⊢ v ⊑*wf[ m ] t → Γ prevalid
    go (Ws-Sub w _ _)   = wf⇒prevalid w
    go (Ws-Trs d₁ _ _)  = go d₁

⊑wf⇒prevalid (Ws-Rfl pv)        = pv
⊑wf⇒prevalid (Ws-Lf1 st _)      = prevalid-ctx (⟶ᵉ-prevalid st)
⊑wf⇒prevalid (Ws-Lf2 _ st _ _)  = prevalid-ctx (⟶ˢ-prevalid st)
⊑wf⇒prevalid (Ws-Rgh d _)       = ⊑wf⇒prevalid d

⊑*wf⇒prevalid : ∀ {Γ v t m} → Γ ⊢ v ⊑*wf[ m ] t → Γ prevalid
⊑*wf⇒prevalid (Ws-Sub w _ _)  = wf⇒prevalid w
⊑*wf⇒prevalid (Ws-Trs d _ _)  = ⊑*wf⇒prevalid d
```

## Local closure

`Ws-Rfl` carries no well-formedness premise, so local closure is not recoverable from `⊑wf`
alone — but it is from the *transitive* relation, whose introduction rule `Ws-Sub` does carry
one. That is enough for `Wf-App`.

```agda
wf⇒lc     : ∀ {Γ t} → Γ ⊢ t wf → LC t
⊑*wf⇒lcˡ  : ∀ {Γ v t m} → Γ ⊢ v ⊑*wf[ m ] t → LC v

wf⇒lc (Wf-PrS _ _)  = lc-fvar
wf⇒lc (Wf-PrE _ _)  = lc-fvar
wf⇒lc (Wf-Top _)    = lc-Top
wf⇒lc (Wf-Fun L F d) = lc-lam L (wf⇒lc d) (λ x∉ → wf⇒lc (F x∉))
wf⇒lc (Wf-App d₁ d₂) = lc-app (⊑*wf⇒lcˡ d₁) (⊑*wf⇒lcˡ d₂)

⊑*wf⇒lcˡ (Ws-Sub w _ _) = wf⇒lc w
⊑*wf⇒lcˡ (Ws-Trs d _ _) = ⊑*wf⇒lcˡ d
```

The same argument recovers the left-hand term's well-formedness, which is what inverting
`Wf-App` needs.

```agda
⊑*wf⇒wfˡ : ∀ {Γ v t m} → Γ ⊢ v ⊑*wf[ m ] t → Γ ⊢ v wf
⊑*wf⇒wfˡ (Ws-Sub w _ _) = w
⊑*wf⇒wfˡ (Ws-Trs d _ _) = ⊑*wf⇒wfˡ d
```

## What this establishes

Figure 4 of v2, transcribed. The operational semantics is v1's `↦`, re-exported unchanged — v2's
evaluation contexts `C ::= □ | λx≤C.t | λx≤t.C | C t | t C` are the same congruence closure.
