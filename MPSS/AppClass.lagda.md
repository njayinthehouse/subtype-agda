# MPSS: a class of terms that both reductions preserve and that contains no abstraction at the root

For the refutation of Conjecture 8 (`MPSS/Conj8Refuted`). The left side of the instance is `δ δ`
with `δ = λx≤R. x x`, and what has to be shown is that no chain of promotions and equivalence
steps takes it to an abstraction. The reason is syntactic: on the head path of `δ δ` every
abstraction is entered under an operand, so its parameter is bound by `≡` to a term of the same
kind; every body is an application or `⊤`; and `R`, whose definition is what unfolds to an
abstraction, occurs only inside annotations, which never reach a head position.

`Cl` is the class of pieces, `Bd` the class of bodies and of whole terms:

    Cl ::= bound variable | free variable other than R | ⊤ | λx≤(anything). Bd | Cl Cl
    Bd ::= Cl Cl | ⊤

Both are closed under `⟶ᵉ` at any configuration whose stack entries are in `Cl` and whose
`≡`-annotations (other than `R`'s) are in `Cl`; and under `⟶ˢ` when moreover the context has no
subtype entry — so that `Ms-Pro` cannot fire — and, for `Cl`, the stack is not empty — so that
`Ms-Fun` cannot. `Bd` contains no abstraction.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.AppClass where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import MPSS.Reduction
open import PSS.Syntax using (fresh; fresh-∉)

R : Name
R = 0
```

## The class

```agda
data Cl : Tm → Set
data Bd : Tm → Set

data Cl where
  c-bvar : ∀ {i} → Cl (bvar i)
  c-fvar : ∀ {x} → x ≢ R → Cl (fvar x)
  c-top  : Cl Top
  c-lam  : ∀ {w b} → Bd b → Cl (lam w b)
  c-app  : ∀ {a b} → Cl a → Cl b → Cl (app a b)

data Bd where
  b-app : ∀ {a b} → Cl a → Cl b → Bd (app a b)
  b-top : Bd Top

Bd⇒Cl : ∀ {t} → Bd t → Cl t
Bd⇒Cl (b-app ca cb) = c-app ca cb
Bd⇒Cl b-top         = c-top

-- no abstraction is a body
Bd-lam : ∀ {w b} → Bd (lam w b) → ⊥
Bd-lam ()
```

## Opening

```agda
open-Cl : ∀ {v} → Cl v → ∀ k {t} → Cl t → Cl (openRec k v t)
open-Bd : ∀ {v} → Cl v → ∀ k {t} → Bd t → Bd (openRec k v t)

open-Cl cv k {bvar i} c-bvar with k ≟ i
... | yes _ = cv
... | no  _ = c-bvar
open-Cl cv k (c-fvar p)    = c-fvar p
open-Cl cv k c-top         = c-top
open-Cl cv k (c-lam bd)    = c-lam (open-Bd cv (suc k) bd)
open-Cl cv k (c-app ca cb) = c-app (open-Cl cv k ca) (open-Cl cv k cb)

open-Bd cv k (b-app ca cb) = b-app (open-Cl cv k ca) (open-Cl cv k cb)
open-Bd cv k b-top         = b-top

unopen-Cl : ∀ k x t → Cl (openRec k (fvar x) t) → Cl t
unopen-Bd : ∀ k x t → Bd (openRec k (fvar x) t) → Bd t

unopen-Cl k x (bvar i)  _             = c-bvar
unopen-Cl k x (fvar y)  c             = c
unopen-Cl k x Top       _             = c-top
unopen-Cl k x (lam w b) (c-lam bd)    = c-lam (unopen-Bd (suc k) x b bd)
unopen-Cl k x (app a b) (c-app ca cb) = c-app (unopen-Cl k x a ca) (unopen-Cl k x b cb)

unopen-Bd k x (bvar i) bd with k ≟ i
unopen-Bd k x (bvar i) () | yes _
unopen-Bd k x (bvar i) () | no  _
unopen-Bd k x Top       _             = b-top
unopen-Bd k x (app a b) (b-app ca cb) = b-app (unopen-Cl k x a ca) (unopen-Cl k x b cb)

fresh≢R : ∀ l → fresh l ≢ R
fresh≢R l ()
```

## The conditions on a configuration

```agda
CtxOK : Ctx → Set
CtxOK Γ = ∀ {y α} → y ≐ α ∈ Γ → y ≢ R → Cl α

NoSub : Ctx → Set
NoSub Γ = ∀ {y t} → y ≤ t ∈ Γ → ⊥

ok-sub : ∀ {Γ x t} → CtxOK Γ → CtxOK ((x , sub , t) ∷ Γ)
ok-sub ok (there m) = ok m

ok-eqv : ∀ {Γ x α} → Cl α → CtxOK Γ → CtxOK ((x , eqv , α) ∷ Γ)
ok-eqv cα ok (here refl) _ = cα
ok-eqv cα ok (there m)   p = ok m p

ns-eqv : ∀ {Γ x α} → NoSub Γ → NoSub ((x , eqv , α) ∷ Γ)
ns-eqv ns (there m) = ns m
```

## Equivalence reduction preserves the class

```agda
presᵉ-Cl : ∀ {Γ s t t′} → CtxOK Γ → All Cl s → Cl t → Γ ∣ s ⊢ t ⟶ᵉ t′ → Cl t′
presᵉ-Bd : ∀ {Γ s t t′} → CtxOK Γ → All Cl s → Bd t → Γ ∣ s ⊢ t ⟶ᵉ t′ → Bd t′

presᵉ-Cl ok as c            (Me-Var _)      = c
presᵉ-Cl ok as c            (Me-Top _)      = c-top
presᵉ-Cl ok as (c-fvar p)   (Me-Pro _ m d)  = presᵉ-Cl ok as (ok m p) d
presᵉ-Cl ok as (c-app ca cb) d@(Me-App _ _) = Bd⇒Cl (presᵉ-Bd ok as (b-app ca cb) d)
presᵉ-Cl ok as (c-app ca cb) d@(Me-TAp _)   = Bd⇒Cl (presᵉ-Bd ok as (b-app ca cb) d)
presᵉ-Cl ok as (c-app ca cb) d@(Me-Bet _ _ _) = Bd⇒Cl (presᵉ-Bd ok as (b-app ca cb) d)
presᵉ-Cl ok [] (c-lam {b = b} bd) (Me-Fun {u' = u′} L _ F) =
  c-lam (unopen-Bd 0 x u′ (presᵉ-Bd (ok-sub ok) [] (open-Bd (c-fvar (fresh≢R L)) 0 bd) (F (fresh-∉ L))))
  where x = fresh L
presᵉ-Cl ok (cα ∷ as) (c-lam {b = b} bd) (Me-FOp {u' = u′} L _ F) =
  c-lam (unopen-Bd 0 x u′ (presᵉ-Bd (ok-eqv cα ok) as (open-Bd (c-fvar (fresh≢R L)) 0 bd) (F (fresh-∉ L))))
  where x = fresh L

presᵉ-Bd ok as (b-app ca cb) (Me-App d₁ d₂) =
  b-app (presᵉ-Cl ok (cb ∷ as) ca d₁) (presᵉ-Cl ok [] cb d₂)
presᵉ-Bd ok as (b-app ca cb) (Me-TAp _) = b-top
presᵉ-Bd ok as (b-app (c-lam bd) cb) (Me-Bet {u' = u′} L F dv) =
  open-Bd (presᵉ-Cl ok [] cb dv) 0
          (unopen-Bd 0 x u′ (presᵉ-Bd ok as (open-Bd (c-fvar (fresh≢R L)) 0 bd) (F (fresh-∉ L))))
  where x = fresh L
presᵉ-Bd ok as b-top (Me-Top _) = b-top
```

## Promotion preserves the class

```agda
presˢ-Bd : ∀ {Γ s t t′} → CtxOK Γ → NoSub Γ → All Cl s → Bd t → Γ ∣ s ⊢ t ⟶ˢ t′ → Bd t′
presˢ-Cl : ∀ {Γ α s t t′} → CtxOK Γ → NoSub Γ → All Cl (α ∷ s) → Cl t → Γ ∣ (α ∷ s) ⊢ t ⟶ˢ t′ → Cl t′

presˢ-Bd ok ns as bd            (Ms-Top _)   = b-top
presˢ-Bd ok ns as bd            (Ms-Equ _ e) = presᵉ-Bd ok as bd e
presˢ-Bd ok ns as (b-app ca cb) (Ms-App d)   = b-app (presˢ-Cl ok ns (cb ∷ as) ca d) cb

presˢ-Cl ok ns as c             (Ms-Top _)   = c-top
presˢ-Cl ok ns as c             (Ms-Equ _ e) = presᵉ-Cl ok as c e
presˢ-Cl ok ns as (c-fvar _)    (Ms-Pro _ m) = ⊥-elim (ns m)
presˢ-Cl ok ns as (c-app ca cb) (Ms-App d)   = c-app (presˢ-Cl ok ns (cb ∷ as) ca d) cb
presˢ-Cl ok ns (cα ∷ as) (c-lam bd) (Ms-FOp {u' = u′} L F) =
  c-lam (unopen-Bd 0 x u′ (presˢ-Bd (ok-eqv cα ok) (ns-eqv ns) as (open-Bd (c-fvar (fresh≢R L)) 0 bd) (F (fresh-∉ L))))
  where x = fresh L
```

## What this establishes

`presᵉ-Bd` and `presˢ-Bd`: from a term of `Bd` — an application of pieces, or `⊤` — at a
configuration with no subtype entry, pieces on the stack and pieces as the `≡`-annotations other
than `R`'s, every equivalence step and every promotion lands in `Bd` again. `Bd` contains no
abstraction (`Bd-lam`).
