# System λ⊲: syntax

The term language of System λ⊲ (Pasquale & García-Pérez, *Pure Subtype Systems Are Type-Safe*,
arXiv:2407.13882), in locally nameless form.

There is **one** syntactic category. PSS does not distinguish terms from types: `Nat + 3` is a
term that "type-checks" to `Nat`, and `λ x ≤ 3. x` is a legal abstraction whose parameter is
bounded by the term `3`, read as the singleton type `{3}`. Everything is a subtype, and the
subtyping relation replaces typing. So the grammar below is the whole language — there is no
separate grammar of types to give.

> `t, u, v ::= x | Top | λ x ≤ t. u | t u`

`Top` is the greatest element. The binder `λ x ≤ t. u` binds `x` in the body `u` **but not in
the annotation `t`**, which matters for every substitution lemma below.

## Why locally nameless

Free variables are named, bound variables are de Bruijn indices, and rules with binders are
stated with cofinite quantification (Aydemir et al., *Engineering Formal Metatheory*).

This is forced by the system rather than chosen for taste. λ⊲'s prevalidity condition is
literally `x ∉ dom(Γ)` and `fv(t) ⊆ dom(Γ)`, and the promotion rule `Srs-Prom` looks a variable
up in Γ to find its bound. All three need free variables to be nameable and comparable, which a
pure de Bruijn or PHOAS encoding denies. See `../PLAN.md` D1.

```agda
{-# OPTIONS --safe #-}

module PSS.Syntax where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (_≟_; ≤-trans; m≤m⊔n; m≤n⊔m; 1+n≰n)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
```

## Names and terms

Names are naturals; nothing depends on that beyond decidable equality and an inexhaustible
supply.

```agda
Name : Set
Name = ℕ

data Tm : Set where
  bvar : ℕ    → Tm          -- bound variable, de Bruijn index
  fvar : Name → Tm          -- free variable, named
  Top  : Tm
  lam  : Tm → Tm → Tm       -- λ _ ≤ annotation . body
  app  : Tm → Tm → Tm
```

## Opening and closing

`openRec k u t` replaces the bound variable at index `k` with `u`. Going under the binder of
`lam` increments the index for the **body only** — the annotation is outside the scope of the
binder.

```agda
openRec : ℕ → Tm → Tm → Tm
openRec k u (bvar i)  with k ≟ i
... | yes _ = u
... | no  _ = bvar i
openRec k u (fvar x)  = fvar x
openRec k u Top       = Top
openRec k u (lam t b) = lam (openRec k u t) (openRec (suc k) u b)
openRec k u (app f a) = app (openRec k u f) (openRec k u a)

infixr 8 _^_
_^_ : Tm → Tm → Tm
t ^ u = openRec 0 u t
```

`closeRec k x t` is the inverse: it abstracts the free name `x` into the bound index `k`.

```agda
closeRec : ℕ → Name → Tm → Tm
closeRec k x (bvar i)  = bvar i
closeRec k x (fvar y)  with x ≟ y
... | yes _ = bvar k
... | no  _ = fvar y
closeRec k x Top       = Top
closeRec k x (lam t b) = lam (closeRec k x t) (closeRec (suc k) x b)
closeRec k x (app f a) = app (closeRec k x f) (closeRec k x a)
```

Two computation lemmas, isolated so the proofs below never have to unfold a `with`.

```agda
open-bvar-≡ : ∀ {k} u → openRec k u (bvar k) ≡ u
open-bvar-≡ {k} u with k ≟ k
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

open-bvar-≢ : ∀ {k i} u → k ≢ i → openRec k u (bvar i) ≡ bvar i
open-bvar-≢ {k} {i} u k≢i with k ≟ i
... | yes p = ⊥-elim (k≢i p)
... | no  _ = refl
```

## Free variables and substitution

```agda
fv : Tm → List Name
fv (bvar _)  = []
fv (fvar x)  = x ∷ []
fv Top       = []
fv (lam t b) = fv t ++ fv b
fv (app f a) = fv f ++ fv a

infix 6 _[_:=_]
_[_:=_] : Tm → Name → Tm → Tm
bvar i  [ x := u ] = bvar i
fvar y  [ x := u ] with x ≟ y
... | yes _ = u
... | no  _ = fvar y
Top     [ x := u ] = Top
lam t b [ x := u ] = lam (t [ x := u ]) (b [ x := u ])
app f a [ x := u ] = app (f [ x := u ]) (a [ x := u ])

subst-fvar-≡ : ∀ {x} u → (fvar x) [ x := u ] ≡ u
subst-fvar-≡ {x} u with x ≟ x
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

subst-fvar-≢ : ∀ {x y} u → x ≢ y → (fvar y) [ x := u ] ≡ fvar y
subst-fvar-≢ {x} {y} u x≢y with x ≟ y
... | yes p = ⊥-elim (x≢y p)
... | no  _ = refl
```

## A supply of fresh names

Cofinite quantification is only useful if the avoid-set can always be escaped.

```agda
maxs : List ℕ → ℕ
maxs []       = 0
maxs (x ∷ xs) = x ⊔ maxs xs

∈⇒≤maxs : ∀ {x} (l : List ℕ) → x ∈ l → x ≤ maxs l
∈⇒≤maxs (y ∷ ys) (here refl) = m≤m⊔n y (maxs ys)
∈⇒≤maxs (y ∷ ys) (there p)   = ≤-trans (∈⇒≤maxs ys p) (m≤n⊔m y (maxs ys))

fresh : List Name → Name
fresh l = suc (maxs l)

fresh-∉ : ∀ l → fresh l ∉ l
fresh-∉ l p = 1+n≰n (∈⇒≤maxs l p)
```

Splitting and combining freshness across an append, used wherever `fv` meets `lam` or `app`.

```agda
∉-++ˡ : ∀ {x} {l₁ l₂ : List Name} → x ∉ l₁ ++ l₂ → x ∉ l₁
∉-++ˡ n p = n (∈-++⁺ˡ p)

∉-++ʳ : ∀ {x} (l₁ : List Name) {l₂} → x ∉ l₁ ++ l₂ → x ∉ l₂
∉-++ʳ l₁ n p = n (∈-++⁺ʳ l₁ p)

∉-++ : ∀ {x} {l₁ l₂ : List Name} → x ∉ l₁ → x ∉ l₂ → x ∉ l₁ ++ l₂
∉-++ {l₁ = l₁} n₁ n₂ p with ∈-++⁻ l₁ p
... | inj₁ q = n₁ q
... | inj₂ q = n₂ q
```

## Local closure

A term is *locally closed* when every de Bruijn index is bound. This is the well-formedness
condition on raw syntax, prior to any of λ⊲'s own judgments — it says the term is a term, not
that it is well-subtyped.

The `lam` case is cofinitely quantified: the body must be locally closed after opening with
**any** name outside some finite set `L`. This is what makes the induction principle strong
enough to use without renaming lemmas.

```agda
data LC : Tm → Set where
  lc-fvar : ∀ {x} → LC (fvar x)
  lc-Top  : LC Top
  lc-lam  : ∀ {t b} (L : List Name)
          → LC t
          → (∀ {x} → x ∉ L → LC (b ^ fvar x))
          → LC (lam t b)
  lc-app  : ∀ {f a} → LC f → LC a → LC (app f a)
```

## The substitution calculus

Everything downstream — reduction, promotion, the subtyping relation, and both embeddings —
rests on the five lemmas in this section.

The first is the technical core: if opening at two *different* indices is idempotent at the
outer one, the outer opening was already vacuous. It is what lets the `lc-lam` case of
`open-lc` step under the binder.

```agda
lam-inj₁ : ∀ {t b t' b'} → lam t b ≡ lam t' b' → t ≡ t'
lam-inj₁ refl = refl

lam-inj₂ : ∀ {t b t' b'} → lam t b ≡ lam t' b' → b ≡ b'
lam-inj₂ refl = refl

app-inj₁ : ∀ {f a f' a'} → app f a ≡ app f' a' → f ≡ f'
app-inj₁ refl = refl

app-inj₂ : ∀ {f a f' a'} → app f a ≡ app f' a' → a ≡ a'
app-inj₂ refl = refl

suc-≢ : ∀ {i j} → i ≢ j → suc i ≢ suc j
suc-≢ i≢j refl = i≢j refl

open-core : ∀ i j u v t
          → i ≢ j
          → openRec j v t ≡ openRec i u (openRec j v t)
          → t ≡ openRec i u t
open-core i j u v (bvar n) i≢j h with j ≟ n
... | yes refl = sym (open-bvar-≢ u i≢j)
... | no  _    = h
open-core i j u v (fvar x)  i≢j h = refl
open-core i j u v Top       i≢j h = refl
open-core i j u v (lam t b) i≢j h =
  cong₂ lam (open-core i j u v t i≢j (lam-inj₁ h))
            (open-core (suc i) (suc j) u v b (suc-≢ i≢j) (lam-inj₂ h))
open-core i j u v (app f a) i≢j h =
  cong₂ app (open-core i j u v f i≢j (app-inj₁ h))
            (open-core i j u v a i≢j (app-inj₂ h))
```

**Opening a locally closed term does nothing.** There is no free index left to fill.

```agda
open-lc-id : ∀ {t} → LC t → ∀ k u → t ≡ openRec k u t
open-lc-id lc-fvar         k u = refl
open-lc-id lc-Top          k u = refl
open-lc-id (lc-app lf la)  k u = cong₂ app (open-lc-id lf k u) (open-lc-id la k u)
open-lc-id (lc-lam {t} {b} L lt F) k u =
  cong₂ lam (open-lc-id lt k u)
            (open-core (suc k) 0 u (fvar (fresh L))
                       b (λ ()) (open-lc-id (F (fresh-∉ L)) (suc k) u))
```

**Substituting a name that does not occur does nothing.**

```agda
subst-fresh : ∀ {t} x u → x ∉ fv t → t [ x := u ] ≡ t
subst-fresh {bvar i} x u p = refl
subst-fresh {fvar y} x u p with x ≟ y
... | yes refl = ⊥-elim (p (here refl))
... | no  _    = refl
subst-fresh {Top}     x u p = refl
subst-fresh {lam t b} x u p =
  cong₂ lam (subst-fresh x u (∉-++ˡ p)) (subst-fresh x u (∉-++ʳ (fv t) p))
subst-fresh {app f a} x u p =
  cong₂ app (subst-fresh x u (∉-++ˡ p)) (subst-fresh x u (∉-++ʳ (fv f) p))
```

**Substitution commutes with opening**, provided the substituted term is locally closed — the
side condition is exactly what stops a bound index inside `u` from being captured.

The two variable cases are split off as separate lemmas. Both sides of the equation are stuck
on the *same* decidable comparison, so a `with` at the top of a standalone lemma reduces both
at once; doing the `with` inside the main induction would abstract only one side and leave the
goal unprovable.

```agda
subst-open-bvar : ∀ {u} k v i x
                → (openRec k v (bvar i)) [ x := u ] ≡ openRec k (v [ x := u ]) (bvar i)
subst-open-bvar k v i x with k ≟ i
... | yes refl = refl
... | no  _    = refl

subst-open-fvar : ∀ {u} → LC u → ∀ k v y x
                → (openRec k v (fvar y)) [ x := u ]
                  ≡ openRec k (v [ x := u ]) ((fvar y) [ x := u ])
subst-open-fvar {u} lu k v y x with x ≟ y
... | yes refl = open-lc-id lu k (v [ x := u ])
... | no  _    = refl

subst-open : ∀ {u} → LC u → ∀ k v t x
           → (openRec k v t) [ x := u ] ≡ openRec k (v [ x := u ]) (t [ x := u ])
subst-open lu k v (bvar i)  x = subst-open-bvar k v i x
subst-open lu k v (fvar y)  x = subst-open-fvar lu k v y x
subst-open lu k v Top       x = refl
subst-open lu k v (lam t b) x =
  cong₂ lam (subst-open lu k v t x) (subst-open lu (suc k) v b x)
subst-open lu k v (app f a) x =
  cong₂ app (subst-open lu k v f x) (subst-open lu k v a x)
```

**Opening with a term factors through opening with a fresh name.** This is the lemma that makes
cofinite quantification usable: to prove something about `b ^ u`, prove it about `b ^ fvar x`
for fresh `x` and substitute.

```agda
subst-intro : ∀ {t u} → LC u → ∀ x → x ∉ fv t → t ^ u ≡ (t ^ fvar x) [ x := u ]
subst-intro {t} {u} lu x p =
  sym (trans (subst-open lu 0 (fvar x) t x)
             (cong₂ (openRec 0) (subst-fvar-≡ {x} u) (subst-fresh {t} x u p)))
```

**Substitution preserves local closure.**

```agda
subst-lc : ∀ {t u x} → LC t → LC u → LC (t [ x := u ])
subst-lc {x = x} (lc-fvar {y}) lu with x ≟ y
... | yes _ = lu
... | no  _ = lc-fvar
subst-lc lc-Top         lu = lc-Top
subst-lc (lc-app lf la) lu = lc-app (subst-lc lf lu) (subst-lc la lu)
subst-lc {u = u} {x = x} (lc-lam {t} {b} L lt F) lu =
  lc-lam (x ∷ L) (subst-lc lt lu) body
  where
    body : ∀ {y} → y ∉ x ∷ L → LC ((b [ x := u ]) ^ fvar y)
    body {y} y∉ =
      subst-eq (subst-lc (F (λ q → y∉ (there q))) lu)
      where
        x≢y : x ≢ y
        x≢y refl = y∉ (here refl)

        step : (b ^ fvar y) [ x := u ] ≡ (b [ x := u ]) ^ fvar y
        step = trans (subst-open lu 0 (fvar y) b x)
                     (cong (λ z → openRec 0 z (b [ x := u ])) (subst-fvar-≢ u x≢y))

        subst-eq : LC ((b ^ fvar y) [ x := u ]) → LC ((b [ x := u ]) ^ fvar y)
        subst-eq h rewrite sym step = h
```

**The β workhorse.** Opening the body of a locally closed abstraction with a locally closed
argument yields a locally closed term — i.e. contracting a redex does not break the syntax.
Every reduction rule in the next module needs this.

```agda
open-lc : ∀ {t b u} → LC (lam t b) → LC u → LC (b ^ u)
open-lc {t} {b} {u} (lc-lam L lt F) lu = go
  where
    x : Name
    x = fresh (L ++ fv b)

    x∉L : x ∉ L
    x∉L = ∉-++ˡ (fresh-∉ (L ++ fv b))

    x∉b : x ∉ fv b
    x∉b = ∉-++ʳ L (fresh-∉ (L ++ fv b))

    go : LC (b ^ u)
    go rewrite subst-intro {b} lu x x∉b = subst-lc (F x∉L) lu
```

## What this establishes

The raw syntax of λ⊲ with its substitution calculus: opening, closing, free variables,
substitution, local closure, and the five lemmas relating them. Nothing here is specific to
subtyping — it is the layer every judgment in Figures 1–3 of the paper is stated over.

**Next** (`PSS/Reduction`): the three reduction relations. The operational semantics `↦`
(`E-App`, `E-Cong`), the equivalence reduction `⟶≡` (`Cr-Var`, `Cr-App`, `Cr-Top`, `Cr-Fun`,
`Cr-Beta`, `Cr-TopApp`), and the promotion relation `⟶≤` (`Srs-Prom`, `Srs-Top`, `Srs-Eq`,
`Srs-App`, `Srs-FunOp`, `Srs-Fun`) — the last of which needs contexts and the continuation
stack, so those arrive with it.

Two rules to flag now as the candidate "bad rules" for objective O3, where the question is
whether PSS's sources of unsoundness map onto spartan's `Type : Type`:

- **`Cr-TopApp`** — `Top u ⟶≡ Top`. The paper is explicit that this is a device to accommodate
  ill-formed terms of shape `Top u` that arise during reduction because the system drops the
  well-formedness condition. Generation 0 found it makes `Top` absorbing and breaks consistency
  (`../0/subpat/PSSTop`).
- **`Srs-Top`** — every term promotes to `Top`, unconditionally.
