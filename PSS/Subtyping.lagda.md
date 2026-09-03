# System λ⊲: subtyping and equivalence

The bottom of Figure 2 — the relation `⊲` and its transitive closure `⊲*` — and Figure 3's
equivalence reduction on extended contexts.

## `⊲` is a metavariable, not a relation

The paper defines **two** relations, subtyping `≤` and equivalence `≡`, and writes `⊲` for
"either one". Reading `⊲` as a single relation collapses the distinction and is wrong; the
rules differ in exactly one place:

- **`As-Refl`** — both relations are reflexive.
- **`As-Left-1`** — a `≤`-derivation extends by a vertical **promotion** step `v ⟶≤ v'`.
- **`As-Left-2`** — a `≡`-derivation extends by a vertical **equivalence** step `v ⟶≡ v'`.
- **`As-Right`** — either extends by a horizontal **equivalence** step on the right.

So the relation is indexed by a mode saying which of the two is meant. Generation 0's version
had one untagged `⊲` with a single `As-Left` (`../PLAN.md` D4).

Diagrammatically, `u ⊲ t` is a derivation growing down-and-right from `u`: vertical steps are
`⟶≤` or `⟶≡` according to the mode, horizontal steps are always `⟶≡`.

```agda
{-# OPTIONS --safe #-}

module PSS.Subtyping where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PSS.Syntax
open import PSS.Reduction
```

## The mode

```agda
data Mode : Set where
  sub : Mode      -- ≤ , subtyping
  eqv : Mode      -- ≡ , equivalence
```

## `⊲` — subtyping and equivalence

```agda
infix 3 _∣_⊢_⊲[_]_
data _∣_⊢_⊲[_]_ : Ctx → Stack → Tm → Mode → Tm → Set where

  As-Refl   : ∀ {Γ s t m}
            → Γ ∣ s prevalid
            → Γ ∣ s ⊢ t ⊲[ m ] t

  As-Left-1 : ∀ {Γ s v v' t}
            → Γ ∣ s ⊢ v ⟶≤ v'
            → Γ ∣ s ⊢ v' ⊲[ sub ] t
            → Γ ∣ s ⊢ v  ⊲[ sub ] t

  As-Left-2 : ∀ {Γ s v v' t}
            → v ⟶≡ v'
            → Γ ∣ s ⊢ v' ⊲[ eqv ] t
            → Γ ∣ s ⊢ v  ⊲[ eqv ] t

  As-Right  : ∀ {Γ s v t t' m}
            → Γ ∣ s ⊢ v ⊲[ m ] t'
            → t ⟶≡ t'
            → Γ ∣ s ⊢ v ⊲[ m ] t
```

Abbreviations matching the paper's notation.

```agda
infix 3 _∣_⊢_≤_ _∣_⊢_≋_

_∣_⊢_≤_ : Ctx → Stack → Tm → Tm → Set
Γ ∣ s ⊢ v ≤ t = Γ ∣ s ⊢ v ⊲[ sub ] t

_∣_⊢_≋_ : Ctx → Stack → Tm → Tm → Set
Γ ∣ s ⊢ v ≋ t = Γ ∣ s ⊢ v ⊲[ eqv ] t
```

## `⊲*` — the transitive closure

`Ast-Trans` is the rule Theorem 4.4 will show admissible.

```agda
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

## Figure 3 — equivalence reduction on extended contexts

Theorem 4.5 does not commute the two reductions over a *fixed* extended context; it allows the
context to have been reduced too. `Γ ∣ s ↣ Γ' ∣ s'` reduces the bounds in `Γ` and the operands
on `s`, pointwise, leaving the binding structure alone.

This relation is what generation 0's formulation omitted, and its absence is why the reduction
of Theorem 4.4 to "two diamonds" there never closed (`../PLAN.md` D4).

The paper names the reflexive rule `Ctx-Sym`; it is called `Ctx-Refl` here, since that is what
it is. The other two names are the paper's.

```agda
infix 3 _∣_↣_∣_
data _∣_↣_∣_ : Ctx → Stack → Ctx → Stack → Set where

  Ctx-Refl       : ∀ {Γ s} → Γ ∣ s ↣ Γ ∣ s

  Ctx-Annotation : ∀ {Γ s Γ' s' x t t'}
                 → Γ ∣ s ↣ Γ' ∣ s'
                 → t ⟶≡ t'
                 → ((x , t) ∷ Γ) ∣ s ↣ ((x , t') ∷ Γ') ∣ s'

  Ctx-Stack      : ∀ {Γ s Γ' s' α α'}
                 → Γ ∣ s ↣ Γ' ∣ s'
                 → α ⟶≡ α'
                 → Γ ∣ (α ∷ s) ↣ Γ' ∣ (α' ∷ s')
```

## Equivalence is contained in subtyping

Promotion subsumes equivalence reduction by `Srs-Eq`, and that lifts to the relations: every
`≡`-derivation is a `≤`-derivation. Prevalidity is threaded through because `Srs-Eq` requires
it, and none of the four rules changes the extended context.

```agda
≋⇒≤ : ∀ {Γ s v t}
    → Γ ∣ s prevalid
    → Γ ∣ s ⊢ v ≋ t
    → Γ ∣ s ⊢ v ≤ t
≋⇒≤ pv (As-Refl p)      = As-Refl p
≋⇒≤ pv (As-Left-2 st d) = As-Left-1 (Srs-Eq pv st) (≋⇒≤ pv d)
≋⇒≤ pv (As-Right d st)  = As-Right (≋⇒≤ pv d) st
```

## Reflexivity of `⊲*`

```agda
⊲*-refl : ∀ {Γ s t m} → Γ ∣ s prevalid → Γ ∣ s ⊢ t ⊲*[ m ] t
⊲*-refl p = Ast-Sub (As-Refl p)
```

## What this establishes

The subtyping and equivalence relations of Figure 2, correctly separated by mode; their
transitive closure; Figure 3's context reduction; and the containment `≡ ⊆ ≤`.

**Next** (`PSS/Metatheory`): Theorem 4.5, the strong commutation of `⟶≤` and `⟶≡` over a
reduced extended context. It is the paper's main technical contribution and everything else —
transitivity admissibility (4.4), no supertype of `Top` (4.3), progress (4.1) and preservation
(4.2) — rests on it.
