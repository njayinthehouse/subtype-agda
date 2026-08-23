# System λ⊲: contexts, stacks, and the three reductions

Figure 1's operational semantics and prevalidity, and Figure 2's two reduction relations.

λ⊲ has **three** reduction relations, and keeping them apart is most of the work:

| relation | what it is | context |
|---|---|---|
| `↦` | the operational semantics — β plus congruence | none |
| `⟶≡` | *equivalence* reduction: reflexive, simultaneous β, plus `Cr-TopApp` | immaterial |
| `⟶≤` | *promotion*: a variable rises to its bound, anything rises to `Top` | `Γ ∣ s` |

The judgements are indexed by an **extended context** `Γ ∣ s`: a subtyping context `Γ` of
bounds `x ≤ t`, and a **continuation stack** `s` of pending operands. `Srs-App` pushes an
operand and promotes the operator; `Srs-FunOp` pops one and binds the formal parameter to it.
That stack is what λ⊲ adds to Hutchins' algorithmic system, and it is why promotion of an
applied abstraction binds the parameter to the *operand* rather than to its own annotation.

```agda
{-# OPTIONS --safe #-}

module PSS.Reduction where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PSS.Syntax
```

## Extended contexts

A context binds names to bounds; a stack holds pending operands. `dom` forgets the bounds.

```agda
Ctx : Set
Ctx = List (Name × Tm)

Stack : Set
Stack = List Tm

dom : Ctx → List Name
dom = map proj₁
```

Sublist inclusion, used for the scoping conditions. `fv t ⊑ dom Γ` is the paper's
`fv(t) ⊆ dom(Γ)`.

```agda
infix 4 _⊑_
_⊑_ : List Name → List Name → Set
xs ⊑ ys = ∀ {x} → x ∈ xs → x ∈ ys
```

Looking a bound up: `x ≤ t ∈ Γ`.

```agda
infix 4 _≤_∈_
_≤_∈_ : Name → Tm → Ctx → Set
x ≤ t ∈ Γ = (x , t) ∈ Γ
```

## Prevalidity

`Γ ∣ s prevalid` is well-scopedness of the extended context: no name is bound twice, and every
bound and every stacked operand is a genuine term mentioning only names already in scope.

The local-closure premises are an artefact of the encoding, not an addition to the system. In
the paper's named presentation every context entry is a term by construction; locally nameless
admits raw syntax with dangling indices, so "is a term" has to be said. Theorem 4.5 needs it:
promoting a variable under a *reflexive* context reduction requires `t ⟶≡ t` for its bound,
and reflexivity of `⟶≡` holds only on locally closed terms (Lemma 2.2).

The paper stresses that prevalidity — unlike well-formedness — is *preserved by reduction*.
Keeping it a separate judgement rather than a type-level invariant is what makes that
statement expressible (`../PLAN.md` D6).

```agda
data _∣_prevalid : Ctx → Stack → Set where

  P-Ctx1 : [] ∣ [] prevalid

  P-Ctx2 : ∀ {Γ x t}
         → Γ ∣ [] prevalid
         → x ∉ dom Γ
         → LC t
         → fv t ⊑ dom Γ
         → ((x , t) ∷ Γ) ∣ [] prevalid

  P-Ctx3 : ∀ {Γ s α}
         → Γ ∣ s prevalid
         → LC α
         → fv α ⊑ dom Γ
         → Γ ∣ (α ∷ s) prevalid
```

## Normal forms

`NF ::= Top | λx≤tₙ.uₙ | x{tₙ}*` — `Top`, an abstraction with normal annotation and body, or a
variable applied to a spine of normal forms. The spine case is split into a `Neutral` judgement.

```agda
data Neutral : Tm → Set
data NF      : Tm → Set

data Neutral where
  ne-var : ∀ {x} → Neutral (fvar x)
  ne-app : ∀ {u v} → Neutral u → NF v → Neutral (app u v)

data NF where
  nf-Top : NF Top
  nf-lam : ∀ {t u} (L : List Name)
         → NF t
         → (∀ {x} → x ∉ L → NF (u ^ fvar x))
         → NF (lam t u)
  nf-ne  : ∀ {u} → Neutral u → NF u
```

## The operational semantics `↦`

β-reduction (`E-App`) closed under the congruence contexts `C` of Figure 1. Rather than reify
`C`, the congruence closure is given directly by one rule per hole position — the two
presentations generate the same relation.

`E-App` carries local-closure side conditions so that contraction lands in the syntax: this is
`open-lc` from `PSS.Syntax`.

```agda
infix 3 _↦_
data _↦_ : Tm → Tm → Set where

  E-App    : ∀ {t u v} → LC (lam t u) → LC v → app (lam t u) v ↦ (u ^ v)

  E-Lam-l  : ∀ {t t' u} → t ↦ t' → lam t u ↦ lam t' u

  E-Lam-r  : ∀ {t u u'} (L : List Name)
           → (∀ {x} → x ∉ L → (u ^ fvar x) ↦ (u' ^ fvar x))
           → lam t u ↦ lam t u'

  E-App-l  : ∀ {u u' v} → u ↦ u' → app u v ↦ app u' v

  E-App-r  : ∀ {u v v'} → v ↦ v' → app u v ↦ app u v'
```

## Equivalence reduction `⟶≡`

Reflexive, small-step, **simultaneous** β-reduction. Reflexive because `Cr-Var` and `Cr-Top`
have no premises, so every locally closed term reduces to itself (Lemma 2.2); simultaneous
because `Cr-App`, `Cr-Fun` and `Cr-Beta` reduce all subterms at once.

The paper notes the extended context is immaterial here, and writes `u ⟶≡ v`; we do the same.

Two things to flag.

**`Cr-Beta` reduces the body under the binder and then substitutes.** The premise is about the
open body, so it is cofinitely quantified; the conclusion opens `u'` with the reduced operand.

**`Cr-TopApp` is one of the two candidate "bad rules"** (`../PLAN.md`, O3). The paper is candid
that it exists to accommodate ill-formed terms of shape `Top u` thrown up by reduction, because
the system deliberately drops the well-formedness condition. It is what makes `Top` absorbing.

```agda
infix 3 _⟶≡_
data _⟶≡_ : Tm → Tm → Set where

  Cr-Var    : ∀ {x} → fvar x ⟶≡ fvar x

  Cr-Top    : Top ⟶≡ Top

  Cr-App    : ∀ {u u' v v'} → u ⟶≡ u' → v ⟶≡ v' → app u v ⟶≡ app u' v'

  Cr-Fun    : ∀ {t t' u u'} (L : List Name)
            → t ⟶≡ t'
            → (∀ {x} → x ∉ L → (u ^ fvar x) ⟶≡ (u' ^ fvar x))
            → lam t u ⟶≡ lam t' u'

  Cr-Beta   : ∀ {t u u' v v'} (L : List Name)
            → (∀ {x} → x ∉ L → (u ^ fvar x) ⟶≡ (u' ^ fvar x))
            → v ⟶≡ v'
            → app (lam t u) v ⟶≡ (u' ^ v')

  Cr-TopApp : ∀ {u} → app Top u ⟶≡ Top
```

## Promotion `⟶≤`

A variable promotes to its bound (`Srs-Prom`); anything promotes to `Top` (`Srs-Top` — the
other candidate bad rule); promotion subsumes equivalence reduction (`Srs-Eq`).

The stack rules are the distinctive part. `Srs-App` pushes the operand and promotes the
operator in the enlarged extended context. `Srs-FunOp` fires when an operand `α` is waiting:
the formal parameter is bound to **`α`, not to the abstraction's own annotation `t`**, and
promotion continues into the body. `Srs-Fun` is the unapplied case, where the parameter is
bound to `t` as usual.

```agda
infix 3 _∣_⊢_⟶≤_
data _∣_⊢_⟶≤_ : Ctx → Stack → Tm → Tm → Set where

  Srs-Prom  : ∀ {Γ s x t}
            → Γ ∣ s prevalid
            → x ≤ t ∈ Γ
            → Γ ∣ s ⊢ fvar x ⟶≤ t

  Srs-Top   : ∀ {Γ s u}
            → Γ ∣ s prevalid
            → Γ ∣ s ⊢ u ⟶≤ Top

  Srs-Eq    : ∀ {Γ s u v}
            → Γ ∣ s prevalid
            → u ⟶≡ v
            → Γ ∣ s ⊢ u ⟶≤ v

  Srs-App   : ∀ {Γ s u u' v}
            → Γ ∣ (v ∷ s) ⊢ u ⟶≤ u'
            → Γ ∣ s ⊢ app u v ⟶≤ app u' v

  Srs-FunOp : ∀ {Γ s α t u u'} (L : List Name)
            → (∀ {x} → x ∉ L → ((x , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶≤ (u' ^ fvar x))
            → Γ ∣ (α ∷ s) ⊢ lam t u ⟶≤ lam t u'

  Srs-Fun   : ∀ {Γ t u u'} (L : List Name)
            → (∀ {x} → x ∉ L → ((x , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶≤ (u' ^ fvar x))
            → Γ ∣ [] ⊢ lam t u ⟶≤ lam t u'
```

## Local closure inversion

Needed to push local-closure evidence into subterms when proving Lemma 2.2 and Proposition 2.1.

```agda
lc-app₁ : ∀ {f a} → LC (app f a) → LC f
lc-app₁ (lc-app p _) = p

lc-app₂ : ∀ {f a} → LC (app f a) → LC a
lc-app₂ (lc-app _ q) = q

lc-lam₁ : ∀ {t b} → LC (lam t b) → LC t
lc-lam₁ (lc-lam _ p _) = p
```

## Lemma 2.2 — `⟶≡` is reflexive

Every locally closed term equivalence-reduces to itself. Local closure is exactly what is
needed: the `lam` case must open the body with a fresh name, which only makes sense if the
body has no other dangling index.

```agda
⟶≡-refl : ∀ {t} → LC t → t ⟶≡ t
⟶≡-refl lc-fvar             = Cr-Var
⟶≡-refl lc-Top              = Cr-Top
⟶≡-refl (lc-app lf la)      = Cr-App (⟶≡-refl lf) (⟶≡-refl la)
⟶≡-refl (lc-lam L lt F)     = Cr-Fun L (⟶≡-refl lt) (λ x∉ → ⟶≡-refl (F x∉))
```

## Proposition 2.1 — the operational semantics embeds in equivalence reduction

`u ↦ v` implies `u ⟶≡ v`. Each congruence rule of `↦` maps to the corresponding simultaneous
rule of `⟶≡`, with Lemma 2.2 supplying reflexivity in the positions that did not move; `E-App`
maps to `Cr-Beta` with both premises reflexive.

Local closure is required — `⟶≡` is reflexive only on locally closed terms, so the congruence
cases cannot supply their untouched halves without it.

```agda
↦⇒⟶≡ : ∀ {u v} → LC u → u ↦ v → u ⟶≡ v

↦⇒⟶≡ lu (E-App {t} {u} {v} (lc-lam L lt F) lv) =
  Cr-Beta {t} {u} {u} {v} {v} L (λ x∉ → ⟶≡-refl (F x∉)) (⟶≡-refl lv)

↦⇒⟶≡ (lc-lam L lt F) (E-Lam-l st) =
  Cr-Fun L (↦⇒⟶≡ lt st) (λ x∉ → ⟶≡-refl (F x∉))

↦⇒⟶≡ (lc-lam L lt F) (E-Lam-r L' G) =
  Cr-Fun (L ++ L') (⟶≡-refl lt)
         (λ {x} x∉ → ↦⇒⟶≡ (F (∉-++ˡ x∉)) (G (∉-++ʳ L x∉)))

↦⇒⟶≡ (lc-app lf la) (E-App-l st) = Cr-App (↦⇒⟶≡ lf st) (⟶≡-refl la)

↦⇒⟶≡ (lc-app lf la) (E-App-r st) = Cr-App (⟶≡-refl lf) (↦⇒⟶≡ la st)
```

## What this establishes

Figure 1's operational semantics, normal forms and prevalidity; Figure 2's `⟶≡` and `⟶≤`;
Lemma 2.2 and Proposition 2.1.

**Next** (`PSS/Subtyping`): the subtyping/equivalence relation `⊲` and its transitive closure
`⊲*`. Recall from `../PLAN.md` D4 that `⊲` is a **metavariable** ranging over `≤` and `≡`, so
`As-Left` is two rules — one taking a `⟶≤` step, one a `⟶≡` step — and the relation must be
indexed by which of the two is meant.
