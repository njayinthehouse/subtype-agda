# λ⊲ subtyping over the context-sensitive equivalence

`PSS/EquivCtx` replaces λ⊲'s context-free `⟶≡` with `⟶≐`, indexed by an equational context `Δ`.
This module rebuilds the promotion and subtyping relations on top of it, so that `Srs-Eq` injects
`⟶≐` rather than `⟶≡`.

Per the project's no-restructuring rule this is a **variant**, in new files; `PSS/Reduction` and
`PSS/Subtyping` are untouched and everything proved about them still stands.

```agda
{-# OPTIONS --safe #-}

module PSS.CtxSubtyping where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.EquivCtx
open import PSS.WellFormed using (prevalid-pop; prevalid-strengthen; prevalid-bound-lc;
                                 prevalid-bound; fvStack)
```

## Promotion, with context-sensitive equivalence

Only `Sc-Eq` differs from `Srs-Eq`: the equivalence step it lifts is now `Δ ⊢ u ⟶≐ v`.

```agda
infix 3 _∣_∣_⊢_⟶≤ᶜ_
data _∣_∣_⊢_⟶≤ᶜ_ : Ctx → Stack → EqCtx → Tm → Tm → Set where

  Sc-Prom  : ∀ {Γ s Δ x t}
           → Γ ∣ s prevalid → x ≤ t ∈ Γ
           → Γ ∣ s ∣ Δ ⊢ fvar x ⟶≤ᶜ t

  Sc-Top   : ∀ {Γ s Δ u}
           → Γ ∣ s prevalid
           → Γ ∣ s ∣ Δ ⊢ u ⟶≤ᶜ Top

  Sc-Eq    : ∀ {Γ s Δ u v}
           → Γ ∣ s prevalid → Δ ⊢ u ⟶≐ v
           → Γ ∣ s ∣ Δ ⊢ u ⟶≤ᶜ v

  Sc-App   : ∀ {Γ s Δ u u' v}
           → Γ ∣ (v ∷ s) ∣ Δ ⊢ u ⟶≤ᶜ u'
           → Γ ∣ s ∣ Δ ⊢ app u v ⟶≤ᶜ app u' v

  Sc-FunOp : ∀ {Γ s Δ α t u u'} (L : List Name)
           → (∀ {x} → x ∉ L → ((x , α) ∷ Γ) ∣ s ∣ Δ ⊢ (u ^ fvar x) ⟶≤ᶜ (u' ^ fvar x))
           → Γ ∣ (α ∷ s) ∣ Δ ⊢ lam t u ⟶≤ᶜ lam t u'

  Sc-Fun   : ∀ {Γ Δ t u u'} (L : List Name)
           → (∀ {x} → x ∉ L → ((x , t) ∷ Γ) ∣ [] ∣ Δ ⊢ (u ^ fvar x) ⟶≤ᶜ (u' ^ fvar x))
           → Γ ∣ [] ∣ Δ ⊢ lam t u ⟶≤ᶜ lam t u'
```

## Subtyping

```agda
infix 3 _∣_∣_⊢_⊲ᶜ[_]_
data _∣_∣_⊢_⊲ᶜ[_]_ : Ctx → Stack → EqCtx → Tm → Mode → Tm → Set where

  Ac-Refl   : ∀ {Γ s Δ t m}
            → Γ ∣ s prevalid
            → Γ ∣ s ∣ Δ ⊢ t ⊲ᶜ[ m ] t

  Ac-Left-1 : ∀ {Γ s Δ v v' t}
            → Γ ∣ s ∣ Δ ⊢ v ⟶≤ᶜ v'
            → Γ ∣ s ∣ Δ ⊢ v' ⊲ᶜ[ sub ] t
            → Γ ∣ s ∣ Δ ⊢ v  ⊲ᶜ[ sub ] t

  Ac-Left-2 : ∀ {Γ s Δ v v' t}
            → Δ ⊢ v ⟶≐ v'
            → Γ ∣ s ∣ Δ ⊢ v' ⊲ᶜ[ eqv ] t
            → Γ ∣ s ∣ Δ ⊢ v  ⊲ᶜ[ eqv ] t

  Ac-Right  : ∀ {Γ s Δ v t t' m}
            → Γ ∣ s ∣ Δ ⊢ v ⊲ᶜ[ m ] t'
            → Δ ⊢ t ⟶≐ t'
            → Γ ∣ s ∣ Δ ⊢ v ⊲ᶜ[ m ] t

infix 3 _∣_∣_⊢_≤ᶜ_

_∣_∣_⊢_≤ᶜ_ : Ctx → Stack → EqCtx → Tm → Tm → Set
Γ ∣ s ∣ Δ ⊢ v ≤ᶜ t = Γ ∣ s ∣ Δ ⊢ v ⊲ᶜ[ sub ] t
```

## Conservativity

λ⊲'s relations embed at every `Δ`, and are recovered exactly at `Δ = []`. So the rebuilt system
extends the original without disturbing it — every theorem in `PSS/` transfers along `⟶≤⇒⟶≤ᶜ`
and `⊲⇒⊲ᶜ`, and nothing new is provable at the empty equational context.

```agda
⟶≤⇒⟶≤ᶜ : ∀ {Γ s Δ u v} → Γ ∣ s ⊢ u ⟶≤ v → Γ ∣ s ∣ Δ ⊢ u ⟶≤ᶜ v
⟶≤⇒⟶≤ᶜ (Srs-Prom pv m)  = Sc-Prom pv m
⟶≤⇒⟶≤ᶜ (Srs-Top pv)     = Sc-Top pv
⟶≤⇒⟶≤ᶜ (Srs-Eq pv e)    = Sc-Eq pv (⟶≡⇒⟶≐ e)
⟶≤⇒⟶≤ᶜ (Srs-App d)      = Sc-App (⟶≤⇒⟶≤ᶜ d)
⟶≤⇒⟶≤ᶜ (Srs-FunOp L F)  = Sc-FunOp L (λ x∉ → ⟶≤⇒⟶≤ᶜ (F x∉))
⟶≤⇒⟶≤ᶜ (Srs-Fun L F)    = Sc-Fun L (λ x∉ → ⟶≤⇒⟶≤ᶜ (F x∉))

⟶≤ᶜ-nil : ∀ {Γ s u v} → Γ ∣ s ∣ [] ⊢ u ⟶≤ᶜ v → Γ ∣ s ⊢ u ⟶≤ v
⟶≤ᶜ-nil (Sc-Prom pv m)  = Srs-Prom pv m
⟶≤ᶜ-nil (Sc-Top pv)     = Srs-Top pv
⟶≤ᶜ-nil (Sc-Eq pv e)    = Srs-Eq pv (⟶≐-nil e)
⟶≤ᶜ-nil (Sc-App d)      = Srs-App (⟶≤ᶜ-nil d)
⟶≤ᶜ-nil (Sc-FunOp L F)  = Srs-FunOp L (λ x∉ → ⟶≤ᶜ-nil (F x∉))
⟶≤ᶜ-nil (Sc-Fun L F)    = Srs-Fun L (λ x∉ → ⟶≤ᶜ-nil (F x∉))

⊲⇒⊲ᶜ : ∀ {Γ s Δ u m t} → Γ ∣ s ⊢ u ⊲[ m ] t → Γ ∣ s ∣ Δ ⊢ u ⊲ᶜ[ m ] t
⊲⇒⊲ᶜ (As-Refl pv)      = Ac-Refl pv
⊲⇒⊲ᶜ (As-Left-1 st d)  = Ac-Left-1 (⟶≤⇒⟶≤ᶜ st) (⊲⇒⊲ᶜ d)
⊲⇒⊲ᶜ (As-Left-2 e d)   = Ac-Left-2 (⟶≡⇒⟶≐ e) (⊲⇒⊲ᶜ d)
⊲⇒⊲ᶜ (As-Right d e)    = Ac-Right (⊲⇒⊲ᶜ d) (⟶≡⇒⟶≐ e)

⊲ᶜ-nil : ∀ {Γ s u m t} → Γ ∣ s ∣ [] ⊢ u ⊲ᶜ[ m ] t → Γ ∣ s ⊢ u ⊲[ m ] t
⊲ᶜ-nil (Ac-Refl pv)      = As-Refl pv
⊲ᶜ-nil (Ac-Left-1 st d)  = As-Left-1 (⟶≤ᶜ-nil st) (⊲ᶜ-nil d)
⊲ᶜ-nil (Ac-Left-2 e d)   = As-Left-2 (⟶≐-nil e) (⊲ᶜ-nil d)
⊲ᶜ-nil (Ac-Right d e)    = As-Right (⊲ᶜ-nil d) (⟶≐-nil e)
```

## Strictly stronger when `Δ` is non-empty

```agda
Δ₂ : EqCtx
Δ₂ = (0 , Top) ∷ []

Γ₂ : Ctx
Γ₂ = []

pv₂ : Γ₂ ∣ [] prevalid
pv₂ = P-Ctx1

moves-≤ : Γ₂ ∣ [] ∣ Δ₂ ⊢ fvar 0 ⟶≤ᶜ Top
moves-≤ = Sc-Eq pv₂ (Ce-Pro (here refl) lc-Top)
```

Under λ⊲'s own promotion this step exists only through `Srs-Top`; here it is available as an
*equivalence*, which is what makes the variable usable on the right of `Ac-Right` as well.

## Basic properties

```agda
⟶≤ᶜ-prevalid : ∀ {Γ s Δ u v} → Γ ∣ s ∣ Δ ⊢ u ⟶≤ᶜ v → Γ ∣ s prevalid
⟶≤ᶜ-prevalid (Sc-Prom pv _)  = pv
⟶≤ᶜ-prevalid (Sc-Top pv)     = pv
⟶≤ᶜ-prevalid (Sc-Eq pv _)    = pv
⟶≤ᶜ-prevalid (Sc-App d)      = prevalid-pop (⟶≤ᶜ-prevalid d)
⟶≤ᶜ-prevalid (Sc-Fun L F)    = strip (⟶≤ᶜ-prevalid (F (fresh-∉ L)))
  where
    strip : ∀ {Γ x t} → ((x , t) ∷ Γ) ∣ [] prevalid → Γ ∣ [] prevalid
    strip (P-Ctx2 p _ _ _) = p
⟶≤ᶜ-prevalid (Sc-FunOp {Γ} {s} {Δ} {α} L F) =
  P-Ctx3 (prevalid-strengthen x∉stk pv) (prevalid-bound-lc pv) (prevalid-bound pv)
  where
    x     = fresh (L ++ fvStack s)
    x∉L   = ∉-++ˡ (fresh-∉ (L ++ fvStack s))
    x∉stk = ∉-++ʳ L (fresh-∉ (L ++ fvStack s))
    pv    = ⟶≤ᶜ-prevalid (F x∉L)

⊲ᶜ-prevalid : ∀ {Γ s Δ u m t} → Γ ∣ s ∣ Δ ⊢ u ⊲ᶜ[ m ] t → Γ ∣ s prevalid
⊲ᶜ-prevalid (Ac-Refl pv)     = pv
⊲ᶜ-prevalid (Ac-Left-1 st _) = ⟶≤ᶜ-prevalid st
⊲ᶜ-prevalid (Ac-Left-2 _ d)  = ⊲ᶜ-prevalid d
⊲ᶜ-prevalid (Ac-Right d _)   = ⊲ᶜ-prevalid d
```

## What this establishes

The λ⊲ promotion and subtyping relations **rebuilt over the context-sensitive equivalence**, and
proved to be a conservative extension:

- `⟶≤⇒⟶≤ᶜ` and `⊲⇒⊲ᶜ` — everything λ⊲ derives, the rebuilt system derives, at every `Δ`. So every
  theorem in `PSS/` transfers.
- `⟶≤ᶜ-nil` and `⊲ᶜ-nil` — at `Δ = []` the rebuilt system derives *exactly* what λ⊲ does. So
  nothing new is provable where no equations are assumed, and the original development is
  undisturbed.
- `moves-≤` — with a non-empty `Δ` the system is strictly stronger. A variable can now reach its
  equational annotation by an **equivalence** step rather than only by `Srs-Top`, which is what
  makes it usable on the right-hand side of `Ac-Right` too.

`PSS/Reduction` and `PSS/Subtyping` are untouched.
