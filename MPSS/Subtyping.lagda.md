# MPSS: subtyping and equivalence

Figure 3 of v2. Structurally unchanged from v1 — `⊲` is still a metavariable over `≤` and `≡`,
so `As-Left` is still two rules once instantiated (see `../PSS/Faithfulness`). What changed is
underneath: the step relation in the equivalence reading is now context-indexed.

```agda
{-# OPTIONS --safe #-}

module MPSS.Subtyping where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_; _∉_)

open import MPSS.Reduction public
```

```agda
data Mode : Set where
  sub-m : Mode
  eqv-m : Mode

infix 3 _∣_⊢_⊲[_]_
data _∣_⊢_⊲[_]_ : Ctx → Stack → Tm → Mode → Tm → Set where

  As-Refl   : ∀ {Γ s t m}
            → Γ ∣ s prevalid
            → Γ ∣ s ⊢ t ⊲[ m ] t

  As-Left-1 : ∀ {Γ s v v' t}
            → Γ ∣ s ⊢ v ⟶ˢ v'
            → Γ ∣ s ⊢ v' ⊲[ sub-m ] t
            → Γ ∣ s ⊢ v  ⊲[ sub-m ] t

  As-Left-2 : ∀ {Γ s v v' t}
            → Γ ∣ s ⊢ v ⟶ᵉ v'
            → Γ ∣ s ⊢ v' ⊲[ eqv-m ] t
            → Γ ∣ s ⊢ v  ⊲[ eqv-m ] t

  As-Right  : ∀ {Γ s v t t' m}
            → Γ ∣ s ⊢ v ⊲[ m ] t'
            → Γ ∣ s ⊢ t ⟶ᵉ t'
            → Γ ∣ s ⊢ v ⊲[ m ] t

infix 3 _∣_⊢_≤_ _∣_⊢_≋_

_∣_⊢_≤_ : Ctx → Stack → Tm → Tm → Set
Γ ∣ s ⊢ v ≤ t = Γ ∣ s ⊢ v ⊲[ sub-m ] t

_∣_⊢_≋_ : Ctx → Stack → Tm → Tm → Set
Γ ∣ s ⊢ v ≋ t = Γ ∣ s ⊢ v ⊲[ eqv-m ] t

infix 3 _∣_⊢_⊲*[_]_
data _∣_⊢_⊲*[_]_ : Ctx → Stack → Tm → Mode → Tm → Set where

  Ast-Sub   : ∀ {Γ s v t m}
            → Γ ∣ s ⊢ v ⊲[ m ] t
            → Γ ∣ s ⊢ v ⊲*[ m ] t

  Ast-Trans : ∀ {Γ s v u t m}
            → Γ ∣ s ⊢ v ⊲*[ m ] u
            → Γ ∣ s ⊢ u ⊲*[ m ] t
            → Γ ∣ s ⊢ v ⊲*[ m ] t
```

Note the shift in `As-Right`: v1's premise was the context-free `t ⟶≡ t'`, MPSS's is
`Γ ∣ s ⊢ t ⟶ᵉ t'`.

```agda
chain-prevalid : ∀ {Γ s u t m} → Γ ∣ s ⊢ u ⊲[ m ] t → Γ ∣ s prevalid
chain-prevalid (As-Refl pv)     = pv
chain-prevalid (As-Left-1 st _) = ⟶ˢ-prevalid st
chain-prevalid (As-Left-2 st _) = ⟶ᵉ-prevalid st
chain-prevalid (As-Right d _)   = chain-prevalid d
```

## What this establishes

Figure 3 of v2. The rule shapes are v1's; the change is that both step relations now carry the
extended context.
