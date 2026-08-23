# System λ⊲: confluence of `⟶≡`, and uniqueness of normal forms

The diamond property of `⟶≡` tiles up to full confluence (Church–Rosser). Together with the
fact that a normal form reduces only to itself, that gives uniqueness of normal forms — which
is what Lemma 5.1 needs to know that minimal promotion is deterministic.

```agda
{-# OPTIONS --safe #-}

module PSS.Confluence where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Close
open import PSS.Equivalence
open import PSS.Diamond
open import PSS.Narrowing using (_⟶≡*_; εₑ; _◅ₑ_; _++ₑ_)
```

## Church–Rosser

```agda
⟶≡-strip : ∀ {t u v} → LC t → t ⟶≡ u → t ⟶≡* v
         → ∃[ w ] ((u ⟶≡* w) × (v ⟶≡* w))
⟶≡-strip lt e εₑ = _ , εₑ , (e ◅ₑ εₑ)
⟶≡-strip lt e (e₁ ◅ₑ c) with ⟶≡-diamond lt e e₁
... | w₁ , p , q with ⟶≡-strip (⟶≡-lc lt e₁) q c
...   | w , c₁ , c₂ = w , (p ◅ₑ c₁) , c₂

⟶≡-confluent : ∀ {t u v} → LC t → t ⟶≡* u → t ⟶≡* v
             → ∃[ w ] ((u ⟶≡* w) × (v ⟶≡* w))
⟶≡-confluent lt εₑ c = _ , c , εₑ
⟶≡-confluent lt (e ◅ₑ c₁) c with ⟶≡-strip lt e c
... | w₁ , d₁ , d₂ with ⟶≡-confluent (⟶≡-lc lt e) c₁ d₁
...   | w , f₁ , f₂ = w , f₁ , (d₂ ++ₑ f₂)
```

## Normal forms reduce only to themselves

`⟶≡` is reflexive, so a normal form does reduce — but only to itself. The `lam` case needs
injectivity of opening to pull the equality of the opened bodies back to the bodies.

```agda
nf-⟶≡-id      : ∀ {u v} → NF u → u ⟶≡ v → u ≡ v
neutral-⟶≡-id : ∀ {u v} → Neutral u → u ⟶≡ v → u ≡ v

neutral-⟶≡-id ne-var Cr-Var = refl
neutral-⟶≡-id (ne-app ne nf) (Cr-App e₁ e₂) =
  cong₂ app (neutral-⟶≡-id ne e₁) (nf-⟶≡-id nf e₂)

nf-⟶≡-id nf-Top Cr-Top = refl
nf-⟶≡-id (nf-ne ne) e  = neutral-⟶≡-id ne e
nf-⟶≡-id (nf-lam {t} {u} L nt F) (Cr-Fun {u' = u'} L' st F') =
  cong₂ lam (nf-⟶≡-id nt st) body
  where
    A  = L ++ L' ++ fv u ++ fv u'
    x  = fresh A
    a∉ = fresh-∉ A

    r₁ = ∉-++ʳ L a∉
    r₂ = ∉-++ʳ L' r₁

    x∉L  = ∉-++ˡ a∉
    x∉L' = ∉-++ˡ r₁
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₂
    x∉u' : x ∉ fv u'
    x∉u' = ∉-++ʳ (fv u) r₂

    body : u ≡ u'
    body = open-inj 0 x u u' x∉u x∉u' (nf-⟶≡-id (F x∉L) (F' x∉L'))

nf-⟶≡*-id : ∀ {u v} → NF u → u ⟶≡* v → u ≡ v
nf-⟶≡*-id nf εₑ       = refl
nf-⟶≡*-id nf (e ◅ₑ c) with nf-⟶≡-id nf e
... | refl = nf-⟶≡*-id nf c
```

## Uniqueness of normal forms

```agda
nf-unique : ∀ {t a b} → LC t → t ⟶≡* a → t ⟶≡* b → NF a → NF b → a ≡ b
nf-unique lt c₁ c₂ na nb with ⟶≡-confluent lt c₁ c₂
... | w , d₁ , d₂ = trans (nf-⟶≡*-id na d₁) (sym (nf-⟶≡*-id nb d₂))
```

## What this establishes

`⟶≡` is confluent, and a term has at most one normal form. Together with the diamond property
this is the Church–Rosser theorem for λ⊲'s equivalence reduction.
