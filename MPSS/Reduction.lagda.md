# MPSS: equivalence and subtyping reduction

Figure 2 of v2. This is where MPSS departs from v1 most sharply.

In v1, **equivalence reduction was context-free**: `u ⟶≡ v`, with the `Γ ∣ s` index printed but
never read by any rule (`../PSS/Faithfulness` proves exactly that). In MPSS the index is real.
Four rules now consult it:

| MPSS | v1 counterpart | difference |
| --- | --- | --- |
| `Me-Pro` | **none** | a variable equivalence-reduces to its `≡` annotation |
| `Me-App` | `Cr-App` | **pushes the operand** onto the stack |
| `Me-Fun` | `Cr-Fun` | extends the context with `x ≤ t` |
| `Me-FOp` | **none** | the stack-consuming abstraction rule, binding `x ≡ α` |
| `Ms-FOp` | `Srs-FunOp` | binds `x ≡ α`, where v1 bound `x ≤ α` |

The last two lines are the substantive change. Popping an operand now records that the parameter
**is** that operand, not merely that it is below it — and `Me-Pro` is what cashes that in.

```agda
{-# OPTIONS --safe #-}

module MPSS.Reduction where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.Context public
```

## Equivalence reduction

Simultaneous reduction, as in v1 — every rule reduces all subterms at once — but now indexed by
the extended context.

```agda
infix 3 _∣_⊢_⟶ᵉ_
data _∣_⊢_⟶ᵉ_ : Ctx → Stack → Tm → Tm → Set where

  Me-Var : ∀ {Γ s x}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢ fvar x ⟶ᵉ fvar x

  Me-Top : ∀ {Γ s}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢ Top ⟶ᵉ Top

  Me-Pro : ∀ {Γ s x α α'}
         → Γ ∣ s prevalid
         → x ≐ α ∈ Γ
         → Γ ∣ s ⊢ α ⟶ᵉ α'
         → Γ ∣ s ⊢ fvar x ⟶ᵉ α'

  Me-App : ∀ {Γ s u u' v v'}
         → Γ ∣ (v ∷ s) ⊢ u ⟶ᵉ u'
         → Γ ∣ [] ⊢ v ⟶ᵉ v'
         → Γ ∣ s ⊢ app u v ⟶ᵉ app u' v'

  Me-TAp : ∀ {Γ s u}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢ app Top u ⟶ᵉ Top

  Me-Bet : ∀ {Γ s t u u' v v'} (L : List Name)
         → (∀ {x} → x ∉ L → Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ (u' ^ fvar x))
         → Γ ∣ [] ⊢ v ⟶ᵉ v'
         → Γ ∣ s ⊢ app (lam t u) v ⟶ᵉ (u' ^ v')

  Me-Fun : ∀ {Γ t t' u u'} (L : List Name)
         → Γ ∣ [] ⊢ t ⟶ᵉ t'
         → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶ᵉ (u' ^ fvar x))
         → Γ ∣ [] ⊢ lam t u ⟶ᵉ lam t' u'

  Me-FOp : ∀ {Γ s α t t' u u'} (L : List Name)
         → Γ ∣ [] ⊢ t ⟶ᵉ t'
         → (∀ {x} → x ∉ L → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ᵉ (u' ^ fvar x))
         → Γ ∣ (α ∷ s) ⊢ lam t u ⟶ᵉ lam t' u'
```

## Subtyping reduction

```agda
infix 3 _∣_⊢_⟶ˢ_
data _∣_⊢_⟶ˢ_ : Ctx → Stack → Tm → Tm → Set where

  Ms-Pro : ∀ {Γ s x t}
         → Γ ∣ s prevalid
         → x ≤ t ∈ Γ
         → Γ ∣ s ⊢ fvar x ⟶ˢ t

  Ms-Top : ∀ {Γ s u}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢ u ⟶ˢ Top

  Ms-Equ : ∀ {Γ s u v}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢ u ⟶ᵉ v
         → Γ ∣ s ⊢ u ⟶ˢ v

  Ms-App : ∀ {Γ s u u' v}
         → Γ ∣ (v ∷ s) ⊢ u ⟶ˢ u'
         → Γ ∣ s ⊢ app u v ⟶ˢ app u' v

  Ms-Fun : ∀ {Γ t u u'} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶ˢ (u' ^ fvar x))
         → Γ ∣ [] ⊢ lam t u ⟶ˢ lam t u'

  Ms-FOp : ∀ {Γ s α t u u'} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ˢ (u' ^ fvar x))
         → Γ ∣ (α ∷ s) ⊢ lam t u ⟶ˢ lam t u'
```

## Prevalidity is recoverable from either reduction

Both relations carry their extended context, so a derivation witnesses that the context is
prevalid. `Me-Pro` and `Me-App` need care: the former recurses at the same extended context, the
latter at a pushed one.

```agda
⟶ᵉ-prevalid : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ v → Γ ∣ s prevalid
⟶ᵉ-prevalid (Me-Var pv)      = pv
⟶ᵉ-prevalid (Me-Top pv)      = pv
⟶ᵉ-prevalid (Me-Pro pv _ _)  = pv
⟶ᵉ-prevalid (Me-TAp pv)      = pv
⟶ᵉ-prevalid (Me-App d _)     = prevalid-pop (⟶ᵉ-prevalid d)
⟶ᵉ-prevalid (Me-Bet L F _)   = ⟶ᵉ-prevalid (F (fresh-∉ L))
⟶ᵉ-prevalid (Me-Fun L d F)   = ⟶ᵉ-prevalid d
⟶ᵉ-prevalid {Γ} {α ∷ s} (Me-FOp {s = s} {α = α} L d F) =
  Pv-Sta (prevalid-strengthen x∉stk inner) (head-lc ctx) (head-fv ctx)
  where
    A     = L ++ fvStack s
    x     = fresh A
    x∉L   = ∉-++ˡ (fresh-∉ A)
    x∉stk = ∉-++ʳ L (fresh-∉ A)

    inner : ((x , eqv , α) ∷ Γ) ∣ s prevalid
    inner = ⟶ᵉ-prevalid (F x∉L)

    ctx : ((x , eqv , α) ∷ Γ) prevalid
    ctx = prevalid-ctx inner

⟶ˢ-prevalid : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ˢ v → Γ ∣ s prevalid
⟶ˢ-prevalid (Ms-Pro pv _)  = pv
⟶ˢ-prevalid (Ms-Top pv)    = pv
⟶ˢ-prevalid (Ms-Equ pv _)  = pv
⟶ˢ-prevalid (Ms-App d)     = prevalid-pop (⟶ˢ-prevalid d)
⟶ˢ-prevalid (Ms-Fun L F)   =
  Pv-Nil (tail-prevalid (prevalid-ctx (⟶ˢ-prevalid (F (fresh-∉ L)))))
⟶ˢ-prevalid {Γ} {α ∷ s} (Ms-FOp {s = s} {α = α} L F) =
  Pv-Sta (prevalid-strengthen x∉stk inner) (head-lc ctx) (head-fv ctx)
  where
    A     = L ++ fvStack s
    x     = fresh A
    x∉L   = ∉-++ˡ (fresh-∉ A)
    x∉stk = ∉-++ʳ L (fresh-∉ A)

    inner : ((x , eqv , α) ∷ Γ) ∣ s prevalid
    inner = ⟶ˢ-prevalid (F x∉L)

    ctx : ((x , eqv , α) ∷ Γ) prevalid
    ctx = prevalid-ctx inner
```

## What this establishes

Figure 2 of v2, both reductions, with prevalidity recoverable from either. The five differences
from v1's Figure 2 are tabulated at the head of this module; the load-bearing one is that
`Ms-FOp` and `Me-FOp` bind the popped operand as an **equivalence** annotation.
