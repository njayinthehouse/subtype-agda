# MPSS: annotations, contexts, and prevalidity

This tree mechanizes **arXiv:2407.13882v2**, *Towards the type safety of Pure Subtype Systems*
(CSL 2026) — the system the authors call **MPSS**, Machine-Based PSS. `../PSS/` mechanizes **v1**,
System λ⊲. They are not the same system, and this module is where the first two differences live.

The terms are unchanged, so we reuse v1's locally nameless syntax verbatim.

> `t, u, v, α ::= x | Top | λx≤t.u | u v`

What changes is the context. v1 stored only **subtype** annotations `x ≤ t`. MPSS stores two
kinds — subtype annotations `x ≤ t` **and equivalence annotations `x ≡ α`** — with a metavariable
`C` ranging over both:

> `Γ ::= ε | Γ, x ≤ t | Γ, x ≡ α`   ·   `s ::= nil | α :: s`

The paper's own gloss on the Greek letter is the clue to why: "α is a metavariable for terms
that originate as operands from the stack." Equivalence annotations are what a *popped operand*
becomes. In v1 popping bound the parameter by `x ≤ α`; in MPSS it binds `x ≡ α`, which is
strictly more informative — the parameter *is* the operand, not merely below it.

```agda
{-# OPTIONS --safe #-}

module MPSS.Context where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PSS.Syntax
  using (Tm; bvar; fvar; Top; lam; app; Name; fv; openRec; _^_; _[_:=_];
         LC; lc-fvar; lc-Top; lc-lam; lc-app; fresh; fresh-∉;
         ∉-++ˡ; ∉-++ʳ; ∉-tail)
  public

open import PSS.Reduction using (_⊑_) public
```

## Annotations

```agda
data Ann : Set where
  sub : Ann      -- x ≤ t
  eqv : Ann      -- x ≡ α

Ctx : Set
Ctx = List (Name × Ann × Tm)

Stack : Set
Stack = List Tm

dom : Ctx → List Name
dom = map proj₁
```

The paper reads `x ≤ t ∈ Γ` as "`x ≤ t` is the **rightmost** annotation for `x` in `Γ`", and
likewise for `x ≡ α`. Prevalidity forbids a name being bound twice, so rightmost is the same as
only, and plain membership suffices — as in v1.

Crucially the two lookups are **disjoint**: a variable bound by an equivalence annotation is not
found by the subtype lookup, so it cannot fire `Ms-Pro`. It reaches subtyping only through
`Ms-Equ`.

```agda
infix 4 _≤_∈_ _≐_∈_

_≤_∈_ : Name → Tm → Ctx → Set
x ≤ t ∈ Γ = (x , sub , t) ∈ Γ

_≐_∈_ : Name → Tm → Ctx → Set
x ≐ α ∈ Γ = (x , eqv , α) ∈ Γ
```

## Prevalidity

v1 had a single judgement mixing contexts and stacks. MPSS factors it in two — `Γ prevalid` for
logical contexts, `Γ ∣ s prevalid` for extended ones — which is the third difference.

```agda
infix 3 _prevalid _∣_prevalid

data _prevalid : Ctx → Set where

  Pv-Emp : [] prevalid

  Pv-Ctx : ∀ {Γ x t}
         → Γ prevalid → x ∉ dom Γ → LC t → fv t ⊑ dom Γ
         → ((x , sub , t) ∷ Γ) prevalid

  Pv-EqA : ∀ {Γ x α}
         → Γ prevalid → x ∉ dom Γ → LC α → fv α ⊑ dom Γ
         → ((x , eqv , α) ∷ Γ) prevalid

data _∣_prevalid : Ctx → Stack → Set where

  Pv-Nil : ∀ {Γ}
         → Γ prevalid
         → Γ ∣ [] prevalid

  Pv-Sta : ∀ {Γ s α}
         → Γ ∣ s prevalid → LC α → fv α ⊑ dom Γ
         → Γ ∣ (α ∷ s) prevalid
```

As in v1, the `LC` premises are an artefact of locally nameless syntax, not an addition to the
system; `../PSS/Faithfulness` proves the corresponding v1 deviation inert, and the same argument
applies here verbatim.

## Basic properties

```agda
prevalid-ctx : ∀ {Γ s} → Γ ∣ s prevalid → Γ prevalid
prevalid-ctx (Pv-Nil pv)     = pv
prevalid-ctx (Pv-Sta pv _ _) = prevalid-ctx pv

prevalid-pop : ∀ {Γ s α} → Γ ∣ (α ∷ s) prevalid → Γ ∣ s prevalid
prevalid-pop (Pv-Sta pv _ _) = pv

prevalid-nil : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ [] prevalid
prevalid-nil pv = Pv-Nil (prevalid-ctx pv)

prevalid-head-lc : ∀ {Γ s α} → Γ ∣ (α ∷ s) prevalid → LC α
prevalid-head-lc (Pv-Sta _ lα _) = lα

prevalid-head-fv : ∀ {Γ s α} → Γ ∣ (α ∷ s) prevalid → fv α ⊑ dom Γ
prevalid-head-fv (Pv-Sta _ _ f) = f
```

Bound lookup respects prevalidity, for either kind of annotation.

```agda
∈-dom : ∀ {Γ x a t} → (x , a , t) ∈ Γ → x ∈ dom Γ
∈-dom (here refl) = here refl
∈-dom (there m)   = there (∈-dom m)

prevalid-bound-lc : ∀ {Γ x a t} → Γ prevalid → (x , a , t) ∈ Γ → LC t
prevalid-bound-lc (Pv-Ctx _ _ lt _) (here refl) = lt
prevalid-bound-lc (Pv-EqA _ _ lα _) (here refl) = lα
prevalid-bound-lc (Pv-Ctx pv _ _ _) (there m)   = prevalid-bound-lc pv m
prevalid-bound-lc (Pv-EqA pv _ _ _) (there m)   = prevalid-bound-lc pv m

prevalid-bound-fv : ∀ {Γ x a t} → Γ prevalid → (x , a , t) ∈ Γ → fv t ⊑ dom Γ
prevalid-bound-fv (Pv-Ctx _ _ _ f)  (here refl) = λ h → there (f h)
prevalid-bound-fv (Pv-EqA _ _ _ f)  (here refl) = λ h → there (f h)
prevalid-bound-fv (Pv-Ctx pv _ _ _) (there m)   = λ h → there (prevalid-bound-fv pv m h)
prevalid-bound-fv (Pv-EqA pv _ _ _) (there m)   = λ h → there (prevalid-bound-fv pv m h)
```

## Free variables of a stack, and strengthening

Every binder rule of MPSS opens its body at a fresh name and extends the context. Recovering
prevalidity of the *un*extended context needs that name to be fresh for the stack too — the same
freshness argument v1 needed, since the stack survives the pop in `Me-FOp` and `Ms-FOp`.

```agda
fvStack : Stack → List Name
fvStack []      = []
fvStack (α ∷ s) = fv α ++ fvStack s

prevalid-strengthen : ∀ {Γ x a t s}
                    → x ∉ fvStack s
                    → ((x , a , t) ∷ Γ) ∣ s prevalid
                    → Γ ∣ s prevalid
prevalid-strengthen _ (Pv-Nil (Pv-Ctx p _ _ _)) = Pv-Nil p
prevalid-strengthen _ (Pv-Nil (Pv-EqA p _ _ _)) = Pv-Nil p
prevalid-strengthen {Γ} {x} {s = β ∷ s} x∉ (Pv-Sta p lβ fvβ) =
  Pv-Sta (prevalid-strengthen (∉-++ʳ (fv β) x∉) p) lβ shrink
  where
    x∉β : x ∉ fv β
    x∉β = ∉-++ˡ x∉

    shrink : fv β ⊑ dom Γ
    shrink h with fvβ h
    ... | here refl = ⊥-elim (x∉β h)
    ... | there h'  = h'
```

The head annotation of a prevalid context, for either kind.

```agda
head-lc : ∀ {Γ x a t} → ((x , a , t) ∷ Γ) prevalid → LC t
head-lc (Pv-Ctx _ _ lt _) = lt
head-lc (Pv-EqA _ _ lα _) = lα

head-fv : ∀ {Γ x a t} → ((x , a , t) ∷ Γ) prevalid → fv t ⊑ dom Γ
head-fv (Pv-Ctx _ _ _ f) = f
head-fv (Pv-EqA _ _ _ f) = f

tail-prevalid : ∀ {Γ x a t} → ((x , a , t) ∷ Γ) prevalid → Γ prevalid
tail-prevalid (Pv-Ctx p _ _ _) = p
tail-prevalid (Pv-EqA p _ _ _) = p
```

## What this establishes

The context layer of MPSS, and the first three differences from v1: two annotation kinds,
disjoint lookups for them, and prevalidity factored into logical and extended judgements.
