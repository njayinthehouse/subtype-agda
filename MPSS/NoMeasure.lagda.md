# MPSS: no configuration measure exists for the diamond

`MPSS/Height` writes down what a well-founded measure on configurations would have to satisfy
for the diamond's induction to go through:

> `dec-pro`: `Me-Pro` strictly decreases it — `f Γ s α < f Γ s (fvar x)` for `x ≡ α ∈ Γ`;
> `mono-app`: `Me-App` does not increase it — `f Γ (b ∷ s) a ≤ f Γ s (app a b)`;
> `mono-fop`: `Me-FOp` does not increase it — `f ((z ≡ α) ∷ Γ) s (b ^ z) ≤ f Γ (α ∷ s) (λw.b)`.

Every candidate so far has been refuted one at a time (`DEAD-ENDS.md`, rows 4–11), and the
catalogue leaves open "a measure that reads the context's own unfolding depth". This module
closes that: **the record `Measure` is uninhabited**. The walk from `Ω` that `MPSS/Unroll` traces
is a sequence of configurations in which the three transitions alternate forever, and `dec-pro` is
strict at every round — so any `f` would have to descend through `ℕ` without end.

The round is the one `Unroll` tabulates. With `Γ` prevalid and `z` a handle on `ω`:

| configuration | transition | constraint |
| --- | --- | --- |
| `Γ ; nil ⊢ z z` | `Me-App` pushes `z` | `mono-app` |
| `Γ ; z ⊢ z` | `Me-Pro` unfolds `z` down to `ω` | `dec-pro`, strictly |
| `Γ ; z ⊢ ω` | `Me-FOp` binds `w ≡ z` | `mono-fop` |
| `Γ, w ≡ z ; nil ⊢ w w` | | |

The last line is the first again, one binding deeper, with `w` a handle on `ω`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.NoMeasure where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-trans; <-trans; <-≤-trans; ≤-<-trans; +-mono-≤; ≤-refl; ≤-reflexive; m+n≤o⇒n≤o; 1+n≰n; +-suc; +-identityʳ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Height using (Measure)
open import MPSS.InfiniteBranching using (ω; Unfolds; here!; chain; unf-wk; unf-dom; lc-ω)
open import PSS.Syntax using (fresh; fresh-∉)
```

## One round of the walk

```agda
module _ (μ : Measure) where
  open Measure μ

  -- the subject at the top of a round: a self-application of a handle, at the empty stack
  W : Ctx → Name → ℕ
  W Γ z = f Γ [] (app (fvar z) (fvar z))

  -- unfolding a handle all the way down to ω is a chain of strict decreases
  chain-dec : ∀ {Γ y} s → Γ prevalid → Unfolds Γ y → f Γ s ω < f Γ s (fvar y)
  chain-dec s pv (here! m)   = dec-pro pv m
  chain-dec s pv (chain m u) = <-trans (chain-dec s pv u) (dec-pro pv m)

  round : ∀ {Γ z} → Γ prevalid → Unfolds Γ z
        → W ((fresh (dom Γ) , eqv , fvar z) ∷ Γ) (fresh (dom Γ)) < W Γ z
  round {Γ} {z} pv u =
    <-≤-trans (≤-<-trans fop (chain-dec (fvar z ∷ []) pv u))
             (mono-app Γ [] (fvar z) (fvar z))
    where
      w = fresh (dom Γ)
      fop : f ((w , eqv , fvar z) ∷ Γ) [] (app (fvar w) (fvar w)) ≤ f Γ (fvar z ∷ []) ω
      fop = mono-fop Γ {w} {Top} {fvar z} [] (app (bvar 0) (bvar 0)) (fresh-∉ (dom Γ)) (λ ()) (λ ())
```

## The walk, and the descent

```agda
  mutual
    Γ[_] : ℕ → Ctx
    Γ[ zero ]  = (0 , eqv , ω) ∷ []
    Γ[ suc n ] = (fresh (dom Γ[ n ]) , eqv , fvar z[ n ]) ∷ Γ[ n ]

    z[_] : ℕ → Name
    z[ zero ]  = 0
    z[ suc n ] = fresh (dom Γ[ n ])

  mutual
    pv[_] : ∀ n → Γ[ n ] prevalid
    pv[ zero ]  = Pv-EqA Pv-Emp (λ ()) lc-ω (λ ())
    pv[ suc n ] = Pv-EqA pv[ n ] (fresh-∉ (dom Γ[ n ])) lc-fvar
                         (λ { (here refl) → unf-dom unf[ n ] })

    unf[_] : ∀ n → Unfolds Γ[ n ] z[ n ]
    unf[ zero ]  = here! (here refl)
    unf[ suc n ] = chain (here refl) (unf-wk unf[ n ])

  descent : ∀ n → W Γ[ n ] z[ n ] + n ≤ W Γ[ 0 ] z[ 0 ]
  descent zero    = ≤-reflexive (+-identityʳ _)
  descent (suc n) =
    ≤-trans (subst (_≤ W Γ[ n ] z[ n ] + n) (sym (+-suc _ n))
                   (+-mono-≤ (round pv[ n ] unf[ n ]) ≤-refl))
            (descent n)
```

The measure at the top of the walk would have to be at least `n` for every `n`.

```agda
  absurd : ⊥
  absurd = 1+n≰n (m+n≤o⇒n≤o (W Γ[ N ] z[ N ]) (descent N))
    where N = suc (W Γ[ 0 ] z[ 0 ])
```

```agda
no-measure : ¬ Measure
no-measure μ = absurd μ
```

## What this establishes

`no-measure`: there is no function of the configuration that `Me-Pro` strictly decreases and
`Me-App` and `Me-FOp` do not increase. Every measure in `DEAD-ENDS.md` rows 4–11 was refuted by
a specific configuration; this is the general statement, and its witness is the walk from `Ω`
that `MPSS/Unroll` already traces: the three transitions cycle, and the strict one recurs.

What it does **not** rule out is an induction that reads the *derivations*. Along the walk the
derivations are finite, and the `Me-Var`/`Me-Pro` case consumes a `Me-Pro` node of one of them
each time round. The catalogue's remaining possibility is therefore narrowed to exactly that: a
measure on the pair of derivations, together with the two context reductions, in which the
derivation the context reduction hands back at `Me-Var`/`Me-Pro` is accounted for.
