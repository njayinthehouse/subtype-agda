# MPSS: the equivalence reduction is not finitely branching

`Me-App` pushes an operand onto the stack, `Me-FOp` pops it and records the parameter as
*equivalent* to it, and `Me-Pro` cashes that in. Run those three against a self-application and the
context grows by a fresh binding on every turn, so nothing ever repeats.

The consequence is that a single term has infinitely many one-step reducts. Write

> `ω = λ⊤. x x`  and  `Ω = ω ω`

then at the empty context and the empty stack

> `Ω ⟶≡ Ω`,  `Ω ⟶≡ (λ⊤. Ω) ω`,  `Ω ⟶≡ (λ⊤. (λ⊤. Ω) ω) ω`,  …

all in **one** step. This module builds that family and proves every member is a reduct.

```agda
{-# OPTIONS --safe #-}

module MPSS.InfiniteBranching where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

open import MPSS.WellFormed
open import PSS.Syntax using (lc-fvar; lc-Top; lc-lam; lc-app; fresh; fresh-∉; open-lc-id)
```

## The family

```agda
ω : Tm
ω = lam Top (app (bvar 0) (bvar 0))

Ω : Tm
Ω = app ω ω

Ω[_] : ℕ → Tm
Ω[ zero ]  = Ω
Ω[ suc n ] = app (lam Top Ω[ n ]) ω

lc-ω : LC ω
lc-ω = lc-lam [] lc-Top (λ _ → lc-app lc-fvar lc-fvar)

fv-ω : fv ω ⊑ []
fv-ω ()
```

Every member is locally closed, so opening it at a fresh name leaves it alone — which is what
`Me-FOp` needs, since its premise talks about the body *opened*.

```agda
lc-Ω : ∀ n → LC Ω[ n ]
lc-Ω zero    = lc-app lc-ω lc-ω
lc-Ω (suc n) = lc-app (lc-lam [] lc-Top body) lc-ω
  where
    body : ∀ {x} → x ∉ [] → LC (Ω[ n ] ^ fvar x)
    body {x} _ = subst LC (open-lc-id (lc-Ω n) 0 (fvar x)) (lc-Ω n)

Ω-open : ∀ n u → Ω[ n ] ≡ Ω[ n ] ^ u
Ω-open n u = open-lc-id (lc-Ω n) 0 u
```

## A chain of handles on ω

`Me-FOp` binds each fresh parameter to whatever sat on the stack, which is the *previous*
parameter, not `ω` itself. So the property that has to travel down the derivation is not "is
annotated by `ω`" but "unfolds to `ω` after finitely many hops".

```agda
data Unfolds : Ctx → Name → Set where
  here!  : ∀ {Γ z}   → z ≐ ω ∈ Γ      → Unfolds Γ z
  chain  : ∀ {Γ y z} → y ≐ fvar z ∈ Γ → Unfolds Γ z → Unfolds Γ y

unf-wk : ∀ {Γ z y c α} → Unfolds Γ z → Unfolds ((y , c , α) ∷ Γ) z
unf-wk (here! m)   = here! (there m)
unf-wk (chain m u) = chain (there m) (unf-wk u)

unf-dom : ∀ {Γ z} → Unfolds Γ z → z ∈ dom Γ
unf-dom (here! m)   = ∈-dom m
unf-dom (chain m _) = ∈-dom m
```

## Prevalidity plumbing

```agda
pv-tail : ∀ {Γ α s} → Γ ∣ (α ∷ s) prevalid → Γ ∣ s prevalid
pv-tail (Pv-Sta pv _ _) = pv

pv-hd-lc : ∀ {Γ α s} → Γ ∣ (α ∷ s) prevalid → LC α
pv-hd-lc (Pv-Sta _ l _) = l

pv-hd-fv : ∀ {Γ α s} → Γ ∣ (α ∷ s) prevalid → fv α ⊑ dom Γ
pv-hd-fv (Pv-Sta _ _ f) = f

pv-wk : ∀ {Γ s y c α} → Γ ∣ s prevalid → ((y , c , α) ∷ Γ) prevalid
      → ((y , c , α) ∷ Γ) ∣ s prevalid
pv-wk (Pv-Nil _)          pc = Pv-Nil pc
pv-wk (Pv-Sta pv lβ fβ)   pc = Pv-Sta (pv-wk pv pc) lβ (λ h → there (fβ h))

pv-var : ∀ {Γ s z} → Γ ∣ s prevalid → z ∈ dom Γ → Γ ∣ (fvar z ∷ s) prevalid
pv-var pv m = Pv-Sta pv lc-fvar (λ { (here refl) → m })

pv-self : ∀ {Γ x c α s} → ((x , c , α) ∷ Γ) ∣ s prevalid
        → ((x , c , α) ∷ Γ) ∣ (fvar x ∷ s) prevalid
pv-self pv = pv-var pv (here refl)
```

## ω reduces to itself, at any prevalid configuration

At the empty stack that is `Me-Fun`, and at a non-empty one `Me-FOp`; the body is the same
`Me-App` of two `Me-Var`s either way.

```agda
ω-refl : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ s ⊢ ω ⟶ᵉ ω
ω-refl {Γ} {[]} pv =
  Me-Fun (dom Γ) (Me-Top pv) λ {x} x∉ →
    let pc = Pv-Ctx (prevalid-ctx pv) x∉ lc-Top (λ ())
        p0 = Pv-Nil pc
    in Me-App (Me-Var (pv-self p0)) (Me-Var p0)
ω-refl {Γ} {α ∷ s} pv =
  Me-FOp (dom Γ) (Me-Top (Pv-Nil (prevalid-ctx pv))) λ {x} x∉ →
    let pc = Pv-EqA (prevalid-ctx pv) x∉ (pv-hd-lc pv) (pv-hd-fv pv)
        ps = pv-wk (pv-tail pv) pc
    in Me-App (Me-Var (pv-self ps)) (Me-Var (Pv-Nil pc))
```

## Following the chain down to ω

```agda
to-ω : ∀ {Γ z s} → Γ ∣ s prevalid → Unfolds Γ z → Γ ∣ s ⊢ fvar z ⟶ᵉ ω
to-ω pv (here! m)   = Me-Pro pv m (ω-refl pv)
to-ω pv (chain m u) = Me-Pro pv m (to-ω pv u)
```

## The construction

`Me-FOp` binds the fresh parameter to whatever is on the stack, so the stack head must itself be
something that unfolds to `ω` — either `ω`, or a variable already in the chain.

```agda
data ToΩ : Ctx → Tm → Set where
  isω   : ∀ {Γ}   → ToΩ Γ ω
  isvar : ∀ {Γ z} → Unfolds Γ z → ToΩ Γ (fvar z)

toΩ-unf : ∀ {Γ y α} → ToΩ Γ α → Unfolds ((y , eqv , α) ∷ Γ) y
toΩ-unf isω       = here! (here refl)
toΩ-unf (isvar u) = chain (here refl) (unf-wk u)
```

Three statements, one induction. `key` builds the nth member from a handle; `ω-to-lam` is the
`Me-FOp` step that consumes the stack entry and hands the fresh parameter to `key` at `n-1`;
`to-lam` walks whatever chain of handles it is given, at a fixed stack.

```agda
mutual
  key : ∀ n {Γ z} → Γ ∣ [] prevalid → Unfolds Γ z
      → Γ ∣ [] ⊢ app (fvar z) (fvar z) ⟶ᵉ Ω[ n ]
  key zero    pv u = Me-App (to-ω (pv-var pv (unf-dom u)) u) (to-ω pv u)
  key (suc n) pv u = Me-App (to-lam n (pv-var pv (unf-dom u)) (isvar u) u) (to-ω pv u)

  to-lam : ∀ n {Γ z α} → Γ ∣ (α ∷ []) prevalid → ToΩ Γ α → Unfolds Γ z
         → Γ ∣ (α ∷ []) ⊢ fvar z ⟶ᵉ lam Top Ω[ n ]
  to-lam n pv tα (here!  m)   = Me-Pro pv m (ω-to-lam n pv tα)
  to-lam n pv tα (chain  m u) = Me-Pro pv m (to-lam n pv tα u)

  ω-to-lam : ∀ n {Γ α} → Γ ∣ (α ∷ []) prevalid → ToΩ Γ α
           → Γ ∣ (α ∷ []) ⊢ ω ⟶ᵉ lam Top Ω[ n ]
  ω-to-lam n {Γ} pv tα =
    Me-FOp (dom Γ) (Me-Top (Pv-Nil (prevalid-ctx pv))) λ {y} y∉ →
      subst (λ w → _ ∣ [] ⊢ app (fvar y) (fvar y) ⟶ᵉ w) (Ω-open n (fvar y))
            (key n (Pv-Nil (Pv-EqA (prevalid-ctx pv) y∉ (pv-hd-lc pv) (pv-hd-fv pv)))
                   (toΩ-unf tα))
```

## Every member is a one-step reduct of Ω

```agda
pv-Ω : [] ∣ (ω ∷ []) prevalid
pv-Ω = Pv-Sta (Pv-Nil Pv-Emp) lc-ω fv-ω

Ω-step : ∀ n → [] ∣ [] ⊢ Ω ⟶ᵉ Ω[ n ]
Ω-step zero    = Me-App (ω-refl pv-Ω)         (ω-refl (Pv-Nil Pv-Emp))
Ω-step (suc n) = Me-App (ω-to-lam n pv-Ω isω) (ω-refl (Pv-Nil Pv-Emp))
```

## The members are pairwise distinct

Every member has the same outer shape — an application whose operator is `λ⊤.−` and whose operand
is `ω` — so they are told apart by what sits under that binder.

```agda
B : ℕ → Tm
B zero    = app (bvar 0) (bvar 0)
B (suc n) = Ω[ n ]

Ω-shape : ∀ n → Ω[ n ] ≡ app (lam Top (B n)) ω
Ω-shape zero    = refl
Ω-shape (suc n) = refl

app-fst : ∀ {a b c d} → app a b ≡ app c d → a ≡ c
app-fst refl = refl

lam-body : ∀ {a b c d} → lam a b ≡ lam c d → b ≡ d
lam-body refl = refl

mutual
  Ω-inj : ∀ m n → Ω[ m ] ≡ Ω[ n ] → m ≡ n
  Ω-inj m n e =
    B-inj m n (lam-body (app-fst (trans (sym (Ω-shape m)) (trans e (Ω-shape n)))))

  B-inj : ∀ m n → B m ≡ B n → m ≡ n
  B-inj zero    zero    _ = refl
  B-inj zero    (suc n) e with app-fst (trans e (Ω-shape n))
  ... | ()
  B-inj (suc m) zero    e with app-fst (trans (sym e) (Ω-shape m))
  ... | ()
  B-inj (suc m) (suc n) e = cong suc (Ω-inj m n e)
```

## The theorem

```agda
Ω-branching : (∀ n → [] ∣ [] ⊢ Ω ⟶ᵉ Ω[ n ])
            × (∀ m n → Ω[ m ] ≡ Ω[ n ] → m ≡ n)
Ω-branching = Ω-step , Ω-inj
```

## What this establishes

`Ω-branching`: the family `Ω[_]` is injective, and every member is a **one-step** reduct of `Ω` at
the empty context and the empty stack. So `⟶≡` is **not finitely branching** — a single term has
infinitely many one-step reducts, of unbounded size.

The mechanism is the same three rules that defeated every attempt on Lemma 2, now caught doing
something visible. `Me-App` pushes the operand; `Me-FOp` pops it and records the fresh parameter as
*equivalent* to it; `Me-Pro` unfolds that parameter straight back to `ω`, whose body is again a
self-application. Each turn extends the context by one binding, so no configuration ever repeats
and the derivation can be continued for as long as one likes. `Unfolds` is exactly the invariant
that survives: a parameter is not annotated by `ω` but reaches it after finitely many hops, because
`Me-FOp` binds each parameter to the *previous* one.

**This settles the complete development.** `MPSS/Develop` reported that Agda rejects `star` on
termination and that the `Me-App` push causing it is forced. That was an obstruction; this is a
refutation. Takahashi's `t*` must be a single term that every reduct of `t` reduces to, and for `Ω`
the reducts form an infinite family of unbounded size. The function `star` is not merely hard to
define — the object it names does not exist for `Ω`.

**It also bounds what any search can do.** Enumerating the one-step reducts of a term is not an
effective procedure in general, so `MPSS/diamond-search.py` cannot be run at bounds that admit
self-application. Its results stand at the bounds already reported — `Ω` needs term size 11, well
outside them — but no exhaustive search can go much further, and the failure would show up as
non-termination rather than as a wrong answer.

What this does **not** do is refute Lemma 2. Infinite branching is compatible with the diamond;
it removes one standard route to proving it and explains why the reduct sets that stalled the
search grow the way they do.
