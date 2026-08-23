# System λ⊲: the closing operation

`closeRec` is defined in `PSS.Syntax` but nothing was proved about it. This module supplies the
package: that closing removes the name, that closing and opening commute at distinct indices,
and that they are mutually inverse.

These are needed because the **complete development** used to prove the diamond property of
`⟶≡` cannot be a structural function on raw locally nameless terms (`../PLAN.md` D7). It has to
be a relation, and proving it total means constructing the development of a body as
`closeRec 0 x w` where `w` develops the body opened at a fresh `x`. Closing is therefore on the
critical path, not an optional convenience.

```agda
{-# OPTIONS --safe #-}

module PSS.Close where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import PSS.Syntax
```

Dropping the head of an avoid-set.

```agda
∉-tail : ∀ {y x} {l : List Name} → y ∉ (x ∷ l) → y ∉ l
∉-tail n p = n (there p)
```

## Computation lemmas for `closeRec`

As with opening, the decidable comparison is isolated so later proofs never unfold a `with`.

```agda
close-fvar-≡ : ∀ {k x} → closeRec k x (fvar x) ≡ bvar k
close-fvar-≡ {k} {x} with x ≟ x
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

close-fvar-≢ : ∀ {k x y} → x ≢ y → closeRec k x (fvar y) ≡ fvar y
close-fvar-≢ {k} {x} {y} x≢y with x ≟ y
... | yes p = ⊥-elim (x≢y p)
... | no  _ = refl
```

## Freshness

Closing removes the name being abstracted, and neither operation invents free variables beyond
the one it introduces.

```agda
fv-close : ∀ k x t → x ∉ fv (closeRec k x t)
fv-close k x (bvar i) ()
fv-close k x (fvar y) with x ≟ y
... | yes _ = λ ()
... | no x≢y = λ { (here p) → x≢y p }
fv-close k x Top      ()
fv-close k x (lam t b) = ∉-++ (fv-close k x t) (fv-close (suc k) x b)
fv-close k x (app f a) = ∉-++ (fv-close k x f) (fv-close k x a)

fv-close-mono : ∀ {y} k x t → y ∉ fv t → y ∉ fv (closeRec k x t)
fv-close-mono k x (bvar i) y∉ = y∉
fv-close-mono k x (fvar z) y∉ with x ≟ z
... | yes _ = λ ()
... | no  _ = y∉
fv-close-mono k x Top      y∉ = y∉
fv-close-mono k x (lam t b) y∉ =
  ∉-++ (fv-close-mono k x t (∉-++ˡ y∉)) (fv-close-mono (suc k) x b (∉-++ʳ (fv t) y∉))
fv-close-mono k x (app f a) y∉ =
  ∉-++ (fv-close-mono k x f (∉-++ˡ y∉)) (fv-close-mono k x a (∉-++ʳ (fv f) y∉))

fv-open-mono : ∀ {y} k x t → y ≢ x → y ∉ fv t → y ∉ fv (openRec k (fvar x) t)
fv-open-mono {y} k x (bvar i) y≢x y∉ with k ≟ i
... | yes _ = λ { (here p) → y≢x p }
... | no  _ = λ ()
fv-open-mono k x (fvar z) y≢x y∉ = y∉
fv-open-mono k x Top      y≢x y∉ = y∉
fv-open-mono k x (lam t b) y≢x y∉ =
  ∉-++ (fv-open-mono k x t y≢x (∉-++ˡ y∉))
       (fv-open-mono (suc k) x b y≢x (∉-++ʳ (fv t) y∉))
fv-open-mono k x (app f a) y≢x y∉ =
  ∉-++ (fv-open-mono k x f y≢x (∉-++ˡ y∉))
       (fv-open-mono k x a y≢x (∉-++ʳ (fv f) y∉))
```

## Closing undoes opening

`closeRec k x (t ^ᵏ fvar x) ≡ t`, provided `x` was not already free in `t`. This is the
direction that does not need local closure.

```agda
close-open : ∀ k x t → x ∉ fv t → closeRec k x (openRec k (fvar x) t) ≡ t
close-open k x (bvar i) x∉ with k ≟ i
... | yes refl = close-fvar-≡
... | no  _    = refl
close-open k x (fvar y) x∉ = close-fvar-≢ (λ { refl → x∉ (here refl) })
close-open k x Top      x∉ = refl
close-open k x (lam t b) x∉ =
  cong₂ lam (close-open k x t (∉-++ˡ x∉)) (close-open (suc k) x b (∉-++ʳ (fv t) x∉))
close-open k x (app f a) x∉ =
  cong₂ app (close-open k x f (∉-++ˡ x∉)) (close-open k x a (∉-++ʳ (fv f) x∉))
```

Opening at a fresh name is therefore injective — the workhorse for reasoning under binders.

```agda
open-inj : ∀ k x t u → x ∉ fv t → x ∉ fv u
         → openRec k (fvar x) t ≡ openRec k (fvar x) u
         → t ≡ u
open-inj k x t u x∉t x∉u eq =
  trans (sym (close-open k x t x∉t))
        (trans (cong (closeRec k x) eq) (close-open k x u x∉u))
```

## Commutation at distinct indices

Two openings at different indices commute; so do a closing and an opening, provided the names
differ too.

```agda
open-open-comm : ∀ i j x y t → i ≢ j
               → openRec i (fvar x) (openRec j (fvar y) t)
                 ≡ openRec j (fvar y) (openRec i (fvar x) t)
open-open-comm i j x y (bvar n) i≢j = go (i ≟ n) (j ≟ n)
  where
    go : Dec (i ≡ n) → Dec (j ≡ n)
       → openRec i (fvar x) (openRec j (fvar y) (bvar n))
         ≡ openRec j (fvar y) (openRec i (fvar x) (bvar n))
    go (yes refl) (yes refl) = ⊥-elim (i≢j refl)
    go (yes refl) (no q) =
      trans (trans (cong (openRec i (fvar x)) (open-bvar-≢ (fvar y) q))
                   (open-bvar-≡ {i} (fvar x)))
            (sym (cong (openRec j (fvar y)) (open-bvar-≡ {i} (fvar x))))
    go (no p) (yes refl) =
      trans (cong (openRec i (fvar x)) (open-bvar-≡ {j} (fvar y)))
            (sym (trans (cong (openRec j (fvar y)) (open-bvar-≢ (fvar x) p))
                        (open-bvar-≡ {j} (fvar y))))
    go (no p) (no q) =
      trans (trans (cong (openRec i (fvar x)) (open-bvar-≢ (fvar y) q))
                   (open-bvar-≢ (fvar x) p))
            (sym (trans (cong (openRec j (fvar y)) (open-bvar-≢ (fvar x) p))
                        (open-bvar-≢ (fvar y) q)))
open-open-comm i j x y (fvar z)  i≢j = refl
open-open-comm i j x y Top       i≢j = refl
open-open-comm i j x y (lam t b) i≢j =
  cong₂ lam (open-open-comm i j x y t i≢j)
            (open-open-comm (suc i) (suc j) x y b (suc-≢ i≢j))
open-open-comm i j x y (app f a) i≢j =
  cong₂ app (open-open-comm i j x y f i≢j) (open-open-comm i j x y a i≢j)

close-open-comm : ∀ i j x y t → i ≢ j → x ≢ y
                → closeRec i x (openRec j (fvar y) t)
                  ≡ openRec j (fvar y) (closeRec i x t)
close-open-comm i j x y (bvar n) i≢j x≢y = go (j ≟ n)
  where
    go : Dec (j ≡ n)
       → closeRec i x (openRec j (fvar y) (bvar n))
         ≡ openRec j (fvar y) (closeRec i x (bvar n))
    go (yes refl) =
      trans (trans (cong (closeRec i x) (open-bvar-≡ {j} (fvar y))) (close-fvar-≢ x≢y))
            (sym (open-bvar-≡ {j} (fvar y)))
    go (no q) =
      trans (cong (closeRec i x) (open-bvar-≢ (fvar y) q))
            (sym (open-bvar-≢ (fvar y) q))
close-open-comm i j x y (fvar z) i≢j x≢y = go (x ≟ z)
  where
    j≢i : j ≢ i
    j≢i p = i≢j (sym p)

    go : Dec (x ≡ z)
       → closeRec i x (openRec j (fvar y) (fvar z))
         ≡ openRec j (fvar y) (closeRec i x (fvar z))
    go (yes refl) =
      trans (close-fvar-≡ {i} {x})
            (sym (trans (cong (openRec j (fvar y)) (close-fvar-≡ {i} {x}))
                        (open-bvar-≢ (fvar y) j≢i)))
    go (no q) =
      trans (close-fvar-≢ q) (sym (cong (openRec j (fvar y)) (close-fvar-≢ q)))
close-open-comm i j x y Top       i≢j x≢y = refl
close-open-comm i j x y (lam t b) i≢j x≢y =
  cong₂ lam (close-open-comm i j x y t i≢j x≢y)
            (close-open-comm (suc i) (suc j) x y b (suc-≢ i≢j) x≢y)
close-open-comm i j x y (app f a) i≢j x≢y =
  cong₂ app (close-open-comm i j x y f i≢j x≢y) (close-open-comm i j x y a i≢j x≢y)
```

## Opening undoes closing

The converse direction, and the one that needs local closure: a term with a dangling index
would not be restored. The `lam` case is where the whole package is used — the induction
hypothesis speaks about the body *opened at a fresh name*, so the goal must be transported
there by the commutation lemmas and brought back by injectivity.

```agda
open-close-fvar : ∀ k x y → openRec k (fvar x) (closeRec k x (fvar y)) ≡ fvar y
open-close-fvar k x y = go (x ≟ y)
  where
    go : Dec (x ≡ y) → openRec k (fvar x) (closeRec k x (fvar y)) ≡ fvar y
    go (yes refl) = trans (cong (openRec k (fvar x)) (close-fvar-≡ {k} {x}))
                          (open-bvar-≡ {k} (fvar x))
    go (no  q)    = cong (openRec k (fvar x)) (close-fvar-≢ q)

open-close : ∀ {t} → LC t → ∀ k x → openRec k (fvar x) (closeRec k x t) ≡ t
open-close (lc-fvar {y}) k x = open-close-fvar k x y
open-close lc-Top k x = refl
open-close (lc-app lf la) k x = cong₂ app (open-close lf k x) (open-close la k x)
open-close (lc-lam {t} {b} L lt F) k x =
  cong₂ lam (open-close lt k x) body
  where
    y : Name
    y = fresh (x ∷ L ++ fv b)

    y∉ : y ∉ (x ∷ L ++ fv b)
    y∉ = fresh-∉ (x ∷ L ++ fv b)

    y≢x : y ≢ x
    y≢x p = y∉ (here p)

    x≢y : x ≢ y
    x≢y p = y∉ (here (sym p))

    y∉L : y ∉ L
    y∉L = ∉-++ˡ (∉-tail y∉)

    y∉b : y ∉ fv b
    y∉b = ∉-++ʳ L (∉-tail y∉)

    P : Tm
    P = openRec (suc k) (fvar x) (closeRec (suc k) x b)

    y∉P : y ∉ fv P
    y∉P = fv-open-mono (suc k) x (closeRec (suc k) x b) y≢x
                       (fv-close-mono (suc k) x b y∉b)

    -- the induction hypothesis, at the body opened with y
    ih : openRec (suc k) (fvar x) (closeRec (suc k) x (openRec 0 (fvar y) b))
           ≡ openRec 0 (fvar y) b
    ih = open-close (F y∉L) (suc k) x

    -- transport it to speak about P
    step : openRec 0 (fvar y) P ≡ openRec 0 (fvar y) b
    step = trans (sym (trans (cong (openRec (suc k) (fvar x))
                                   (close-open-comm (suc k) 0 x y b (λ ()) x≢y))
                             (open-open-comm (suc k) 0 x y (closeRec (suc k) x b) (λ ()))))
                 ih

    body : P ≡ b
    body = open-inj 0 y P b y∉P y∉b step
```

## What this establishes

The `closeRec` package: freshness, mutual inversion with opening, injectivity of opening at a
fresh name, and commutation at distinct indices. This discharges the items `../PLAN.md` D5
listed as owed, and unblocks D7.

**Next:** the complete development as a relation, its totality (which is where `closeRec` is
used to build the development of a body), the triangle, and the diamond.
