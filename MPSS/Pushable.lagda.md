# MPSS: terms whose operands are scoped

Reflexivity `Γ ∣ s ⊢ t ⟶ᵉ′ t` needs more than local closure: `Me-App′` pushes the operand and
`Pv-Sta` wants it scoped in `dom Γ`, and `Me-Fun′` puts the annotation in the context and
`Pv-Ctx` wants that scoped too. `MPSS/StackPush` asks for `fv t ⊑ dom Γ` outright. That is too
much for the chains `MPSS/Peel` builds, whose terms sit inside `Me-Bet` bodies and mention the
unbound parameter. What is exactly needed is the predicate below: every operand, and every
annotation of an abstraction that is not in operator position, is scoped. It is indexed by the
depth of the stack, since an abstraction at a non-empty stack binds its parameter to the stack
head and its annotation never enters the context.

The point of the predicate is the last lemma: **the target of any variant step satisfies it**,
with no hypothesis on the source beyond local closure. Every application node of a target was
either kept by `Me-App′`, whose operand was pushed and hence scoped, or produced by substituting
an operand for the parameter of a `Me-Bet′` body — and the parameter, being unbound, occurs in no
operand of that body.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Pushable where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-prevalid; ⟶ᵉ′-lc; fv-⟶ᵉ′)
open import MPSS.StackPush using (prevalid-cons)
```

## The predicate

```agda
data Pushable : ℕ → List Name → Tm → Set where
  P-fvar : ∀ {k N x} → Pushable k N (fvar x)
  P-Top  : ∀ {k N}   → Pushable k N Top
  P-app  : ∀ {k N u v}
         → Pushable (suc k) N u → Pushable 0 N v → fv v ⊑ N
         → Pushable k N (app u v)
  P-lam₀ : ∀ {N t u} (L : List Name)
         → fv t ⊑ N → Pushable 0 N t
         → (∀ {y} → y ∉ L → Pushable 0 (y ∷ N) (u ^ fvar y))
         → Pushable 0 N (lam t u)
  P-lamₛ : ∀ {k N t u} (L : List Name)
         → Pushable 0 N t
         → (∀ {y} → y ∉ L → Pushable k (y ∷ N) (u ^ fvar y))
         → Pushable (suc k) N (lam t u)
```

## Monotonicity in the set of names, and in the depth

```agda
⊑-cons : ∀ {N N′ : List Name} y → N ⊑ N′ → (y ∷ N) ⊑ (y ∷ N′)
⊑-cons y inc (here p)  = here p
⊑-cons y inc (there h) = there (inc h)

pushable-mono : ∀ {k N N′ t} → N ⊑ N′ → Pushable k N t → Pushable k N′ t
pushable-mono inc P-fvar = P-fvar
pushable-mono inc P-Top  = P-Top
pushable-mono inc (P-app pu pv f) =
  P-app (pushable-mono inc pu) (pushable-mono inc pv) (λ h → inc (f h))
pushable-mono inc (P-lam₀ L f pt F) =
  P-lam₀ L (λ h → inc (f h)) (pushable-mono inc pt) (λ {y} y∉ → pushable-mono (⊑-cons y inc) (F y∉))
pushable-mono inc (P-lamₛ L pt F) =
  P-lamₛ L (pushable-mono inc pt) (λ {y} y∉ → pushable-mono (⊑-cons y inc) (F y∉))
```

Depth `0` is the strongest: an abstraction at the empty stack has its annotation scoped, which a
deeper position does not ask for.

```agda
pushable-lift : ∀ {j N t} k → Pushable j N t → Pushable (j + k) N t
pushable-lift k P-fvar = P-fvar
pushable-lift k P-Top  = P-Top
pushable-lift k (P-app pu pv f) = P-app (pushable-lift k pu) pv f
pushable-lift zero    (P-lam₀ L f pt F) = P-lam₀ L f pt F
pushable-lift (suc k) (P-lam₀ L f pt F) = P-lamₛ L pt (λ y∉ → pushable-lift k (F y∉))
pushable-lift k (P-lamₛ L pt F) = P-lamₛ L pt (λ y∉ → pushable-lift k (F y∉))
```

## Substitution for a name outside the set

Such a name occurs in no operand and in no annotation the predicate scopes, so those are left
alone; the substituend only has to be pushable itself.

```agda
pushable-subst : ∀ {k N t v} y → y ∉ N → LC v → Pushable 0 N v
               → Pushable k N t → Pushable k N (t [ y := v ])
pushable-subst {N = N} {v = v} y y∉ lv pv (P-fvar {x = x}) = go
  where
    go : Pushable _ N ((fvar x) [ y := v ])
    go with y ≟ x
    ... | yes _ = pushable-lift _ pv
    ... | no  _ = P-fvar
pushable-subst y y∉ lv pv P-Top = P-Top
pushable-subst {N = N} {v = v} y y∉ lv pv (P-app {u = u} {v = w} pu pw f) = go
  where
    y∉w : y ∉ fv w
    y∉w h = y∉ (f h)
    go : Pushable _ N (app (u [ y := v ]) (w [ y := v ]))
    go rewrite subst-fresh {w} y v y∉w = P-app (pushable-subst y y∉ lv pv pu) pw f
pushable-subst {N = N} {v = v} y y∉ lv pv (P-lam₀ {t = t} {u = u} L f pt F) = go
  where
    y∉t : y ∉ fv t
    y∉t h = y∉ (f h)
    body : ∀ {z} → z ∉ (y ∷ L) → Pushable 0 (z ∷ N) ((u [ y := v ]) ^ fvar z)
    body {z} z∉ = transport (pushable-subst y y∉′ lv (pushable-mono there pv) (F (∉-tail z∉)))
      where
        y≢z : y ≢ z
        y≢z p = z∉ (here (sym p))
        y∉′ : y ∉ (z ∷ N)
        y∉′ (here p)  = y≢z p
        y∉′ (there h) = y∉ h
        eq : ((u ^ fvar z) [ y := v ]) ≡ ((u [ y := v ]) ^ fvar z)
        eq = trans (subst-open lv 0 (fvar z) u y)
                   (cong (λ q → openRec 0 q (u [ y := v ])) (subst-fvar-≢ v y≢z))
        transport : Pushable 0 (z ∷ N) ((u ^ fvar z) [ y := v ])
                  → Pushable 0 (z ∷ N) ((u [ y := v ]) ^ fvar z)
        transport h rewrite sym eq = h
    go : Pushable 0 N (lam (t [ y := v ]) (u [ y := v ]))
    go rewrite subst-fresh {t} y v y∉t = P-lam₀ (y ∷ L) f pt body
pushable-subst {N = N} {v = v} y y∉ lv pv (P-lamₛ {k = k} {t = t} {u = u} L pt F) =
  P-lamₛ (y ∷ L) (pushable-subst y y∉ lv pv pt) body
  where
    body : ∀ {z} → z ∉ (y ∷ L) → Pushable k (z ∷ N) ((u [ y := v ]) ^ fvar z)
    body {z} z∉ = transport (pushable-subst y y∉′ lv (pushable-mono there pv) (F (∉-tail z∉)))
      where
        y≢z : y ≢ z
        y≢z p = z∉ (here (sym p))
        y∉′ : y ∉ (z ∷ N)
        y∉′ (here p)  = y≢z p
        y∉′ (there h) = y∉ h
        eq : ((u ^ fvar z) [ y := v ]) ≡ ((u [ y := v ]) ^ fvar z)
        eq = trans (subst-open lv 0 (fvar z) u y)
                   (cong (λ q → openRec 0 q (u [ y := v ])) (subst-fvar-≢ v y≢z))
        transport : Pushable k (z ∷ N) ((u ^ fvar z) [ y := v ])
                  → Pushable k (z ∷ N) ((u [ y := v ]) ^ fvar z)
        transport h rewrite sym eq = h
```

## Reflexivity for pushable terms

```agda
⟶ᵉ′-refl-push : ∀ {Γ s t} → Γ ∣ s prevalid → LC t → Pushable (length s) (dom Γ) t
              → Γ ∣ s ⊢ t ⟶ᵉ′ t
⟶ᵉ′-refl-push pv lc-fvar P-fvar = Me-Var′ pv
⟶ᵉ′-refl-push pv lc-Top  P-Top  = Me-Top′ pv
⟶ᵉ′-refl-push pv (lc-app lu lv) (P-app pu pw f) =
  Me-App′ (⟶ᵉ′-refl-push (Pv-Sta pv lv f) lu pu) (⟶ᵉ′-refl-push (prevalid-nil pv) lv pw)
⟶ᵉ′-refl-push {Γ} {[]} pv (lc-lam {t} {b} L₁ lt F₁) (P-lam₀ L f pt F) =
  Me-Fun′ (L ++ L₁ ++ dom Γ) (⟶ᵉ′-refl-push pv lt pt) body
  where
    body : ∀ {y} → y ∉ (L ++ L₁ ++ dom Γ) → ((y , sub , t) ∷ Γ) ∣ [] ⊢ (b ^ fvar y) ⟶ᵉ′ (b ^ fvar y)
    body {y} y∉ = ⟶ᵉ′-refl-push (prevalid-cons pv (∉-++ʳ L₁ (∉-++ʳ L y∉)) lt f)
                                (F₁ (∉-++ˡ (∉-++ʳ L y∉))) (F (∉-++ˡ y∉))
⟶ᵉ′-refl-push {Γ} {α ∷ s} pv (lc-lam {t} {b} L₁ lt F₁) (P-lamₛ L pt F) =
  Me-FOp′ (L ++ L₁ ++ dom Γ) (⟶ᵉ′-refl-push (prevalid-nil pv) lt pt) body
  where
    body : ∀ {y} → y ∉ (L ++ L₁ ++ dom Γ) → ((y , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ᵉ′ (b ^ fvar y)
    body {y} y∉ = ⟶ᵉ′-refl-push (prevalid-cons (prevalid-pop pv) (∉-++ʳ L₁ (∉-++ʳ L y∉))
                                               (prevalid-head-lc pv) (prevalid-head-fv pv))
                                (F₁ (∉-++ˡ (∉-++ʳ L y∉))) (F (∉-++ˡ y∉))
```

## The target of a step is pushable

```agda
⊑-refl : ∀ {N : List Name} → N ⊑ N
⊑-refl h = h

pushable-target : ∀ {Γ s t t′} → LC t → Γ ∣ s ⊢ t ⟶ᵉ′ t′ → Pushable (length s) (dom Γ) t′
pushable-target lt (Me-Var′ _) = P-fvar
pushable-target lt (Me-Top′ _) = P-Top
pushable-target lt (Me-TAp′ _) = P-Top
pushable-target {s = s} lt (Me-Pro′ pv m d) =
  pushable-lift (length s) (pushable-target (prevalid-bound-lc (prevalid-ctx pv) m) d)
pushable-target (lc-app lu lv) (Me-App′ d e) =
  P-app (pushable-target lu d) (pushable-target lv e)
        (fv-⟶ᵉ′ ⊑-refl e (prevalid-head-fv (⟶ᵉ′-prevalid d)))
pushable-target {Γ} {s} (lc-app (lc-lam {t} {u} L₁ lt F₁) lv)
                (Me-Bet′ {u' = u′} {v = v} {v' = v′} L F e) = result
  where
    A   = L ++ L₁ ++ dom Γ ++ fv u′
    y   = fresh A
    y∉L : y ∉ L
    y∉L = ∉-++ˡ (fresh-∉ A)
    y∉L₁ : y ∉ L₁
    y∉L₁ = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    y∉Γ : y ∉ dom Γ
    y∉Γ = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))
    y∉u′ : y ∉ fv u′
    y∉u′ = ∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))

    lv′ : LC v′
    lv′ = ⟶ᵉ′-lc lv e

    body : Pushable (length s) (dom Γ) (u′ ^ fvar y)
    body = pushable-target (F₁ y∉L₁) (F y∉L)

    result : Pushable (length s) (dom Γ) (u′ ^ v′)
    result rewrite subst-intro {u′} {v′} lv′ y y∉u′ =
      pushable-subst y y∉Γ lv′ (pushable-target lv e) body
pushable-target {Γ} (lc-lam {t} {u} L₁ lt F₁) (Me-Fun′ {u' = u′} L d F) =
  P-lam₀ (L ++ L₁) (fv-⟶ᵉ′ ⊑-refl d ft) (pushable-target lt d)
         (λ {y} y∉ → pushable-target (F₁ (∉-++ʳ L y∉)) (F (∉-++ˡ y∉)))
  where
    ft : fv t ⊑ dom Γ
    ft = head-fv (prevalid-ctx (⟶ᵉ′-prevalid (F (fresh-∉ L))))
pushable-target (lc-lam L₁ lt F₁) (Me-FOp′ L d F) =
  P-lamₛ (L ++ L₁) (pushable-target lt d)
         (λ {y} y∉ → pushable-target (F₁ (∉-++ʳ L y∉)) (F (∉-++ˡ y∉)))
```

## The same for the original relation

The chains of `MPSS/Peel` hold a side still that is the target of an *original* step, so the
lemma is needed for `⟶ᵉ` as well. The proof is the same; `Me-Pro`'s premise is at the current
stack, so no lifting is needed there.

```agda
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ)

pushable-targetᵒ : ∀ {Γ s t t′} → LC t → Γ ∣ s ⊢ t ⟶ᵉ t′ → Pushable (length s) (dom Γ) t′
pushable-targetᵒ lt (Me-Var _) = P-fvar
pushable-targetᵒ lt (Me-Top _) = P-Top
pushable-targetᵒ lt (Me-TAp _) = P-Top
pushable-targetᵒ lt (Me-Pro pv m d) = pushable-targetᵒ (prevalid-bound-lc (prevalid-ctx pv) m) d
pushable-targetᵒ (lc-app lu lv) (Me-App d e) =
  P-app (pushable-targetᵒ lu d) (pushable-targetᵒ lv e)
        (fv-⟶ᵉ ⊑-refl e (prevalid-head-fv (⟶ᵉ-prevalid d)))
pushable-targetᵒ {Γ} {s} (lc-app (lc-lam {t} {u} L₁ lt F₁) lv)
                 (Me-Bet {u' = u′} {v = v} {v' = v′} L F e) = result
  where
    A   = L ++ L₁ ++ dom Γ ++ fv u′
    y   = fresh A
    y∉L : y ∉ L
    y∉L = ∉-++ˡ (fresh-∉ A)
    y∉L₁ : y ∉ L₁
    y∉L₁ = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    y∉Γ : y ∉ dom Γ
    y∉Γ = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))
    y∉u′ : y ∉ fv u′
    y∉u′ = ∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))

    lv′ : LC v′
    lv′ = ⟶ᵉ-lc lv e

    body : Pushable (length s) (dom Γ) (u′ ^ fvar y)
    body = pushable-targetᵒ (F₁ y∉L₁) (F y∉L)

    result : Pushable (length s) (dom Γ) (u′ ^ v′)
    result rewrite subst-intro {u′} {v′} lv′ y y∉u′ =
      pushable-subst y y∉Γ lv′ (pushable-targetᵒ lv e) body
pushable-targetᵒ {Γ} (lc-lam {t} {u} L₁ lt F₁) (Me-Fun {u' = u′} L d F) =
  P-lam₀ (L ++ L₁) (fv-⟶ᵉ ⊑-refl d ft) (pushable-targetᵒ lt d)
         (λ {y} y∉ → pushable-targetᵒ (F₁ (∉-++ʳ L y∉)) (F (∉-++ˡ y∉)))
  where
    ft : fv t ⊑ dom Γ
    ft = head-fv (prevalid-ctx (⟶ᵉ-prevalid (F (fresh-∉ L))))
pushable-targetᵒ (lc-lam L₁ lt F₁) (Me-FOp L d F) =
  P-lamₛ (L ++ L₁) (pushable-targetᵒ lt d)
         (λ {y} y∉ → pushable-targetᵒ (F₁ (∉-++ʳ L y∉)) (F (∉-++ˡ y∉)))
```

## What this establishes

`Pushable`, closed under enlarging the set of names, under moving to a deeper stack position, and
under substituting a pushable term for a name outside the set. `⟶ᵉ′-refl-push`: reflexivity of
the variant relation for pushable terms. `pushable-target`: every target of a variant step is
pushable, so in particular reflexive — which is what lets the chains of `MPSS/Peel` hold one side
still while the other reduces.
