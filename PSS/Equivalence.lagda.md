# System λ⊲: the substitution theory of `⟶≡`

Everything Theorem 4.5 needs about equivalence reduction on its own: that it preserves local
closure, that it commutes with substitution, and — the payoff — that it has the **diamond
property**.

`⟶≡` is a *simultaneous* (Takahashi-style) reduction, which is exactly why the diamond holds
in one step rather than by a strip lemma: `Cr-App`, `Cr-Fun` and `Cr-Beta` each reduce all
their subterms at once, so two reductions from a common source can always be joined by
reducing "everything both of them touched."

```agda
{-# OPTIONS --safe #-}

module PSS.Equivalence where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import PSS.Syntax
open import PSS.Reduction
```

## `⟶≡` preserves local closure

```agda
⟶≡-lc : ∀ {t t'} → LC t → t ⟶≡ t' → LC t'
⟶≡-lc lt Cr-Var  = lc-fvar
⟶≡-lc lt Cr-Top  = lc-Top

⟶≡-lc (lc-app lu lv) (Cr-App su sv) = lc-app (⟶≡-lc lu su) (⟶≡-lc lv sv)

⟶≡-lc (lc-lam L₀ lt F₀) (Cr-Fun L st F) =
  lc-lam (L ++ L₀) (⟶≡-lc lt st)
         (λ {x} x∉ → ⟶≡-lc (F₀ (∉-++ʳ L x∉)) (F (∉-++ˡ x∉)))

⟶≡-lc (lc-app (lc-lam L₀ lt F₀) lv) (Cr-Beta {t} {u} {u'} L F sv) =
  open-lc {t} {u'} lam-u' (⟶≡-lc lv sv)
  where
    lam-u' : LC (lam t u')
    lam-u' = lc-lam (L ++ L₀) lt
                    (λ {x} x∉ → ⟶≡-lc (F₀ (∉-++ʳ L x∉)) (F (∉-++ˡ x∉)))

⟶≡-lc lt Cr-TopApp = lc-Top
```

## Substitution commutes with `⟶≡`

If `t ⟶≡ t'` and `v ⟶≡ v'`, then `t [x := v] ⟶≡ t' [x := v']`. Local closure of the
substituted terms is needed to push substitution under the binders, via `subst-open`.

```agda
⟶≡-subst : ∀ {t t' v v'} x
         → LC v → LC v'
         → t ⟶≡ t'
         → v ⟶≡ v'
         → (t [ x := v ]) ⟶≡ (t' [ x := v' ])

⟶≡-subst {v = v} {v'} x lv lv' (Cr-Var {y}) sv = go
  where
    go : (fvar y [ x := v ]) ⟶≡ (fvar y [ x := v' ])
    go with x ≟ y
    ... | yes _ = sv
    ... | no  _ = Cr-Var

⟶≡-subst x lv lv' Cr-Top sv = Cr-Top

⟶≡-subst x lv lv' (Cr-App s₁ s₂) sv =
  Cr-App (⟶≡-subst x lv lv' s₁ sv) (⟶≡-subst x lv lv' s₂ sv)

⟶≡-subst {v = v} {v'} x lv lv' (Cr-Fun {t} {t'} {u} {u'} L st F) sv =
  Cr-Fun (x ∷ L ++ fv v ++ fv v')
         (⟶≡-subst x lv lv' st sv)
         body
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v ++ fv v')
         → ((u [ x := v ]) ^ fvar y) ⟶≡ ((u' [ x := v' ]) ^ fvar y)
    body {y} y∉ = transport (⟶≡-subst x lv lv' (F (∉-++ˡ (∉-tail y∉))) sv)
      where
        x≢y : x ≢ y
        x≢y refl = y∉ (here refl)

        eq  : ((u ^ fvar y) [ x := v ]) ≡ ((u [ x := v ]) ^ fvar y)
        eq  = trans (subst-open lv 0 (fvar y) u x)
                    (cong (λ z → openRec 0 z (u [ x := v ])) (subst-fvar-≢ v x≢y))

        eq' : ((u' ^ fvar y) [ x := v' ]) ≡ ((u' [ x := v' ]) ^ fvar y)
        eq' = trans (subst-open lv' 0 (fvar y) u' x)
                    (cong (λ z → openRec 0 z (u' [ x := v' ])) (subst-fvar-≢ v' x≢y))

        transport : ((u ^ fvar y) [ x := v ]) ⟶≡ ((u' ^ fvar y) [ x := v' ])
                  → ((u [ x := v ]) ^ fvar y) ⟶≡ ((u' [ x := v' ]) ^ fvar y)
        transport h rewrite sym eq | sym eq' = h

⟶≡-subst {v = v} {v'} x lv lv' (Cr-Beta {t} {u} {u'} {w} {w'} L F sw) sv =
  transport (Cr-Beta {t [ x := v ]} {u [ x := v ]} {u' [ x := v' ]}
                     {w [ x := v ]} {w' [ x := v' ]}
                     (x ∷ L ++ fv v ++ fv v') body (⟶≡-subst x lv lv' sw sv))
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v ++ fv v')
         → ((u [ x := v ]) ^ fvar y) ⟶≡ ((u' [ x := v' ]) ^ fvar y)
    body {y} y∉ = go (⟶≡-subst x lv lv' (F (∉-++ˡ (∉-tail y∉))) sv)
      where
        x≢y : x ≢ y
        x≢y refl = y∉ (here refl)

        eq  : ((u ^ fvar y) [ x := v ]) ≡ ((u [ x := v ]) ^ fvar y)
        eq  = trans (subst-open lv 0 (fvar y) u x)
                    (cong (λ z → openRec 0 z (u [ x := v ])) (subst-fvar-≢ v x≢y))

        eq' : ((u' ^ fvar y) [ x := v' ]) ≡ ((u' [ x := v' ]) ^ fvar y)
        eq' = trans (subst-open lv' 0 (fvar y) u' x)
                    (cong (λ z → openRec 0 z (u' [ x := v' ])) (subst-fvar-≢ v' x≢y))

        go : ((u ^ fvar y) [ x := v ]) ⟶≡ ((u' ^ fvar y) [ x := v' ])
           → ((u [ x := v ]) ^ fvar y) ⟶≡ ((u' [ x := v' ]) ^ fvar y)
        go h rewrite sym eq | sym eq' = h

    -- the conclusion of Cr-Beta substitutes; push the outer substitution inside
    eqβ : ((u' ^ w') [ x := v' ]) ≡ ((u' [ x := v' ]) ^ (w' [ x := v' ]))
    eqβ = subst-open lv' 0 w' u' x

    transport : (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶≡ ((u' [ x := v' ]) ^ (w' [ x := v' ]))
              → (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶≡ ((u' ^ w') [ x := v' ])
    transport h rewrite eqβ = h

⟶≡-subst x lv lv' Cr-TopApp sv = Cr-TopApp
```

## The cofinite corollary

Opening with a *term* rather than a name, which is the form `Cr-Beta` and Theorem 4.5 need.

```agda
⟶≡-open : ∀ {u u' v v'} (L : List Name)
        → LC v → LC v'
        → (∀ {x} → x ∉ L → (u ^ fvar x) ⟶≡ (u' ^ fvar x))
        → v ⟶≡ v'
        → (u ^ v) ⟶≡ (u' ^ v')
⟶≡-open {u} {u'} {v} {v'} L lv lv' F sv = go
  where
    x : Name
    x = fresh (L ++ fv u ++ fv u')

    x∉L : x ∉ L
    x∉L = ∉-++ˡ (fresh-∉ (L ++ fv u ++ fv u'))

    x∉u : x ∉ fv u
    x∉u = ∉-++ˡ (∉-++ʳ L (fresh-∉ (L ++ fv u ++ fv u')))

    x∉u' : x ∉ fv u'
    x∉u' = ∉-++ʳ (fv u) (∉-++ʳ L (fresh-∉ (L ++ fv u ++ fv u')))

    go : (u ^ v) ⟶≡ (u' ^ v')
    go rewrite subst-intro {u} lv x x∉u | subst-intro {u'} lv' x x∉u' =
      ⟶≡-subst x lv lv' (F x∉L) sv
```

## What this establishes

The substitution theory of `⟶≡`: preservation of local closure, the substitution lemma, and
its cofinite corollary.

**Next:** the diamond property of `⟶≡`, then Theorem 4.5. The diamond's `Cr-Beta` versus
`Cr-App` critical pair is joined precisely by `⟶≡-open` above.
