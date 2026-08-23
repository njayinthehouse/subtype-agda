# System λ⊲: the diamond property of `⟶≡`

`⟶≡` is a simultaneous reduction, so it satisfies the **diamond property** outright: any two
reductions from a common source are joined by a single further step on each side. This is what
Theorem 4.5's `Srs-Eq` case needs.

The obstacle in locally nameless (recorded as `../PLAN.md` D7) is the binder. Joining
`lam t u₁` and `lam t u₂` means joining the bodies, but the induction hypothesis only speaks
about bodies *opened at a name*, and hands back a join `w` for each choice of name, with no
evident way to produce a single body `u₃`.

Two ingredients resolve it, both now available:

- **`closeRec`** turns the join at one fresh name back into a body: `u₃ := closeRec 0 x w`, with
  `open-close` recovering `w ≡ u₃ ^ fvar x` and `fv-close` giving `x ∉ fv u₃`.
- **Renaming** moves that from the chosen `x` to an arbitrary `y` — and needs no new machinery.
  It is `⟶≡-subst` at `v = v' = fvar y`, because both sides get renamed *symmetrically*.

```agda
{-# OPTIONS --safe #-}

module PSS.Diamond where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Close
open import PSS.Equivalence
```

## Renaming

```agda
⟶≡-rename : ∀ {u u'} x y → x ∉ fv u → x ∉ fv u'
          → (u ^ fvar x) ⟶≡ (u' ^ fvar x)
          → (u ^ fvar y) ⟶≡ (u' ^ fvar y)
⟶≡-rename {u} {u'} x y x∉u x∉u' s
  rewrite subst-intro {u}  (lc-fvar {y}) x x∉u
        | subst-intro {u'} (lc-fvar {y}) x x∉u'
  = ⟶≡-subst x lc-fvar lc-fvar s Cr-Var
```

## Closing a join back into a body

The plumbing all four binder cases share: given a reduction from a body opened at `x` to an
arbitrary locally closed `w`, close `w` at `x` and rename to any `y`.

```agda
close-rename : ∀ {b w} x y → LC w → x ∉ fv b
             → (b ^ fvar x) ⟶≡ w
             → (b ^ fvar y) ⟶≡ ((closeRec 0 x w) ^ fvar y)
close-rename {b} {w} x y lw x∉b s =
  ⟶≡-rename {b} {closeRec 0 x w} x y x∉b (fv-close 0 x w) s'
  where
    s' : (b ^ fvar x) ⟶≡ ((closeRec 0 x w) ^ fvar x)
    s' rewrite open-close lw 0 x = s
```

## The diamond

By induction on the local-closure derivation, casing on the pair of reduction rules. The source
constrains which pairs occur: only `Cr-Fun` applies to a `lam`, and `Cr-Beta` needs the operator
to be a `lam` while `Cr-TopApp` needs it to be `Top`, so those two never collide.

The critical pair is `Cr-App` against `Cr-Beta` — an application whose operator is an
abstraction, contracted on one side and merely reduced on the other. It is joined by
`⟶≡-open`, which is what that lemma was for.

```agda
⟶≡-diamond : ∀ {t u v} → LC t → t ⟶≡ u → t ⟶≡ v
           → ∃[ w ] ((u ⟶≡ w) × (v ⟶≡ w))

⟶≡-diamond lt Cr-Var Cr-Var = _ , Cr-Var , Cr-Var
⟶≡-diamond lt Cr-Top Cr-Top = _ , Cr-Top , Cr-Top

⟶≡-diamond lt Cr-TopApp Cr-TopApp         = Top , Cr-Top    , Cr-Top
⟶≡-diamond lt Cr-TopApp (Cr-App Cr-Top _) = Top , Cr-Top    , Cr-TopApp
⟶≡-diamond lt (Cr-App Cr-Top _) Cr-TopApp = Top , Cr-TopApp , Cr-Top

⟶≡-diamond (lc-app lf la) (Cr-App s₁ s₂) (Cr-App s₁' s₂')
  with ⟶≡-diamond lf s₁ s₁' | ⟶≡-diamond la s₂ s₂'
... | w₁ , p₁ , q₁ | w₂ , p₂ , q₂ = app w₁ w₂ , Cr-App p₁ p₂ , Cr-App q₁ q₂
```

### Abstraction against abstraction

```agda
⟶≡-diamond (lc-lam {t} {b} L₀ lt F₀)
           (Cr-Fun {_} {t₁} {_} {b₁} L₁ st₁ F₁)
           (Cr-Fun {_} {t₂} {_} {b₂} L₂ st₂ F₂) =
  lam (proj₁ jt) b₃ , Cr-Fun [] (proj₁ (proj₂ jt)) (λ _ → r₁)
                    , Cr-Fun [] (proj₂ (proj₂ jt)) (λ _ → r₂)
  where
    A = L₀ ++ L₁ ++ L₂ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₃
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₃

    jt = ⟶≡-diamond lt st₁ st₂
    jb = ⟶≡-diamond (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lw : LC (proj₁ jb)
    lw = ⟶≡-lc (⟶≡-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → (b₁ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₁ {y} = close-rename {b₁} {proj₁ jb} x y lw x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → (b₂ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₂ {y} = close-rename {b₂} {proj₁ jb} x y lw x∉b₂ (proj₂ (proj₂ jb))
```

### Congruence against contraction — the critical pair

```agda
⟶≡-diamond (lc-app (lc-lam {a} {b} L₀ la F₀) lc)
           (Cr-App {_} {_} {_} {c₁} (Cr-Fun {_} {a₁} {_} {b₁} L₁ sa₁ F₁) sc₁)
           (Cr-Beta {_} {_} {b₂} {_} {c₂} L₂ F₂ sc₂) =
  (b₃ ^ proj₁ jc)
  , Cr-Beta {a₁} {b₁} {b₃} {c₁} {proj₁ jc} [] (λ _ → r₁) (proj₁ (proj₂ jc))
  , ⟶≡-open {b₂} {b₃} {c₂} {proj₁ jc} [] lc₂ lc₃ (λ _ → r₂) (proj₂ (proj₂ jc))
  where
    A = L₀ ++ L₁ ++ L₂ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₃
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₃

    jc = ⟶≡-diamond lc sc₁ sc₂
    jb = ⟶≡-diamond (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lc₂ : LC c₂
    lc₂ = ⟶≡-lc lc sc₂
    lc₃ : LC (proj₁ jc)
    lc₃ = ⟶≡-lc lc₂ (proj₂ (proj₂ jc))

    lw : LC (proj₁ jb)
    lw = ⟶≡-lc (⟶≡-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → (b₁ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₁ {y} = close-rename {b₁} {proj₁ jb} x y lw x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → (b₂ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₂ {y} = close-rename {b₂} {proj₁ jb} x y lw x∉b₂ (proj₂ (proj₂ jb))

⟶≡-diamond (lc-app (lc-lam {a} {b} L₀ la F₀) lc)
           (Cr-Beta {_} {_} {b₁} {_} {c₁} L₁ F₁ sc₁)
           (Cr-App {_} {_} {_} {d₂} (Cr-Fun {_} {a₂} {_} {b₂} L₂ sa₂ F₂) sc₂) =
  (b₃ ^ proj₁ jc)
  , ⟶≡-open {b₁} {b₃} {c₁} {proj₁ jc} [] lc₁ lc₃ (λ _ → r₁) (proj₁ (proj₂ jc))
  , Cr-Beta {a₂} {b₂} {b₃} {d₂} {proj₁ jc} [] (λ _ → r₂) (proj₂ (proj₂ jc))
  where
    A = L₀ ++ L₁ ++ L₂ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₃
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₃

    jc = ⟶≡-diamond lc sc₁ sc₂
    jb = ⟶≡-diamond (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lc₁ : LC c₁
    lc₁ = ⟶≡-lc lc sc₁
    lc₃ : LC (proj₁ jc)
    lc₃ = ⟶≡-lc lc₁ (proj₁ (proj₂ jc))

    lw : LC (proj₁ jb)
    lw = ⟶≡-lc (⟶≡-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → (b₁ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₁ {y} = close-rename {b₁} {proj₁ jb} x y lw x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → (b₂ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₂ {y} = close-rename {b₂} {proj₁ jb} x y lw x∉b₂ (proj₂ (proj₂ jb))
```

### Contraction against contraction

```agda
⟶≡-diamond (lc-app (lc-lam {a} {b} L₀ la F₀) lc)
           (Cr-Beta {_} {_} {b₁} {_} {c₁} L₁ F₁ sc₁)
           (Cr-Beta {_} {_} {b₂} {_} {c₂} L₂ F₂ sc₂) =
  (b₃ ^ proj₁ jc)
  , ⟶≡-open {b₁} {b₃} {c₁} {proj₁ jc} [] lc₁ lc₃ (λ _ → r₁) (proj₁ (proj₂ jc))
  , ⟶≡-open {b₂} {b₃} {c₂} {proj₁ jc} [] lc₂ lc₃ (λ _ → r₂) (proj₂ (proj₂ jc))
  where
    A = L₀ ++ L₁ ++ L₂ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₃
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₃

    jc = ⟶≡-diamond lc sc₁ sc₂
    jb = ⟶≡-diamond (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lc₁ : LC c₁
    lc₁ = ⟶≡-lc lc sc₁
    lc₂ : LC c₂
    lc₂ = ⟶≡-lc lc sc₂
    lc₃ : LC (proj₁ jc)
    lc₃ = ⟶≡-lc lc₁ (proj₁ (proj₂ jc))

    lw : LC (proj₁ jb)
    lw = ⟶≡-lc (⟶≡-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → (b₁ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₁ {y} = close-rename {b₁} {proj₁ jb} x y lw x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → (b₂ ^ fvar y) ⟶≡ (b₃ ^ fvar y)
    r₂ {y} = close-rename {b₂} {proj₁ jb} x y lw x∉b₂ (proj₂ (proj₂ jb))
```

## What this establishes

`⟶≡` is diamond, hence confluent. D7 is closed, and Theorem 4.5's `Srs-Eq` case is unblocked.

**Next:** Lemma B.9 (promotion commutes with substitution), then Theorem 4.5 itself.
