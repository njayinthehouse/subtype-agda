# Scoping and context reduction for the rebuilt system

The rebuilt commutation theorem needs what v1's needed — reduction of extended contexts, lookup
along it, and preservation of prevalidity — but over `⟶≐` rather than `⟶≡`.

One thing genuinely changes. v1 has `fv-⟶≡ : t ⟶≡ t' → fv t' ⊑ fv t`: equivalence never
introduces a free variable. That is **false** for `⟶≐`, since `Ce-Pro` replaces `x` by `α` and
`α` may mention anything. What survives is the scoped form: if everything `Δ` can unfold to is
scoped in `N`, then reduction keeps terms scoped in `N`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module PSS.CtxScope where

open import Data.Nat.Base using (ℕ; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Scope using (fv-open-lower; fv-open-split)
open import PSS.EquivCtx
```

## Scoping

```agda
Scoped : List Name → EqCtx → Set
Scoped N Δ = ∀ {x α} → (x , α) ∈ Δ → fv α ⊑ N

Scoped-mono : ∀ {N M Δ} → N ⊑ M → Scoped N Δ → Scoped M Δ
Scoped-mono f sc m h = f (sc m h)

fv-⟶≐ : ∀ {Δ N t t'} → Scoped N Δ → Δ ⊢ t ⟶≐ t' → fv t ⊑ N → fv t' ⊑ N
fv-⟶≐ sc Ce-Var        ft = ft
fv-⟶≐ sc Ce-Top        ft = ft
fv-⟶≐ sc (Ce-Pro m _)  ft = sc m
fv-⟶≐ sc Ce-TopApp     ft = λ ()
fv-⟶≐ {t = app u v} sc (Ce-App {u' = u'} d e) ft h with ∈-++⁻ (fv u') h
... | inj₁ p = fv-⟶≐ sc d (λ q → ft (∈-++⁺ˡ q)) p
... | inj₂ p = fv-⟶≐ sc e (λ q → ft (∈-++⁺ʳ (fv u) q)) p
fv-⟶≐ {Δ} {N} {t = lam a b} {t' = lam a' b'} sc (Ce-Fun L d F) ft h with ∈-++⁻ (fv a') h
... | inj₁ p = fv-⟶≐ sc d (λ q → ft (∈-++⁺ˡ q)) p
... | inj₂ p = body p
  where
    A   = L ++ fv b ++ fv b'
    x   = fresh A
    a∉  = fresh-∉ A
    x∉L = ∉-++ˡ a∉
    x∉b' : x ∉ fv b'
    x∉b' = ∉-++ʳ (fv b) (∉-++ʳ L a∉)

    ftb : fv (b ^ fvar x) ⊑ (x ∷ N)
    ftb q with fv-open-split 0 (fvar x) b q
    ... | inj₁ r = there (ft (∈-++⁺ʳ (fv a) r))
    ... | inj₂ (here refl) = here refl

    inner : fv (b' ^ fvar x) ⊑ (x ∷ N)
    inner = fv-⟶≐ (Scoped-mono there sc) (F x∉L) ftb

    body : ∀ {y} → y ∈ fv b' → y ∈ N
    body {y} q with inner (fv-open-lower 0 (fvar x) b' q)
    ... | there r      = r
    ... | here refl    = ⊥-elim (x∉b' q)
fv-⟶≐ {Δ} {N} {t = app (lam a b) v} sc (Ce-Beta {u' = b'} {v' = v'} L F e) ft h
  with fv-open-split 0 v' b' h
... | inj₂ q = fv-⟶≐ sc e (λ r → ft (∈-++⁺ʳ (fv (lam a b)) r)) q
... | inj₁ q = body q
  where
    A   = L ++ fv b ++ fv b'
    x   = fresh A
    a∉  = fresh-∉ A
    x∉L = ∉-++ˡ a∉
    x∉b' : x ∉ fv b'
    x∉b' = ∉-++ʳ (fv b) (∉-++ʳ L a∉)

    ftb : fv (b ^ fvar x) ⊑ (x ∷ N)
    ftb r with fv-open-split 0 (fvar x) b r
    ... | inj₁ w = there (ft (∈-++⁺ˡ (∈-++⁺ʳ (fv a) w)))
    ... | inj₂ (here refl) = here refl

    inner : fv (b' ^ fvar x) ⊑ (x ∷ N)
    inner = fv-⟶≐ (Scoped-mono there sc) (F x∉L) ftb

    body : ∀ {y} → y ∈ fv b' → y ∈ N
    body {y} r with inner (fv-open-lower 0 (fvar x) b' r)
    ... | there w   = w
    ... | here refl = ⊥-elim (x∉b' r)
```

## Context reduction over `⟶≐`

```agda
data CtxRedᶜ (Δ : EqCtx) : Ctx → Ctx → Set where
  crᶜ-nil  : CtxRedᶜ Δ [] []
  crᶜ-cons : ∀ {Γ Γ' x t t'} → CtxRedᶜ Δ Γ Γ' → Δ ⊢ t ⟶≐ t'
           → CtxRedᶜ Δ ((x , t) ∷ Γ) ((x , t') ∷ Γ')

data StkRedᶜ (Δ : EqCtx) : Stack → Stack → Set where
  srᶜ-nil  : StkRedᶜ Δ [] []
  srᶜ-cons : ∀ {s s' α α'} → StkRedᶜ Δ s s' → Δ ⊢ α ⟶≐ α'
           → StkRedᶜ Δ (α ∷ s) (α' ∷ s')

CtxRedᶜ-dom : ∀ {Δ Γ Γ'} → CtxRedᶜ Δ Γ Γ' → dom Γ' ≡ dom Γ
CtxRedᶜ-dom crᶜ-nil                = refl
CtxRedᶜ-dom (crᶜ-cons {x = x} cr _) = cong (x ∷_) (CtxRedᶜ-dom cr)

CtxRedᶜ-lookup : ∀ {Δ Γ Γ' y t} → CtxRedᶜ Δ Γ Γ' → (y , t) ∈ Γ
               → ∃[ t' ] (((y , t') ∈ Γ') × (Δ ⊢ t ⟶≐ t'))
CtxRedᶜ-lookup (crᶜ-cons cr st) (here refl) = _ , here refl , st
CtxRedᶜ-lookup (crᶜ-cons cr st) (there m)   with CtxRedᶜ-lookup cr m
... | t' , m' , d = t' , there m' , d
```

## Prevalidity is *not* preserved unconditionally

v1's `prevalid-red` goes through because `fv-⟶≡` says equivalence never introduces a free
variable. Here it can, and that breaks the corresponding step for a reason worth recording.

In `P-Ctx2` the context is `(x , t) ∷ Γ₀`, and the constructor demands `fv t' ⊑ dom Γ₀` — the
*tail's* domain. But `Scoped (dom ((x , t) ∷ Γ₀)) Δ` allows a `Δ`-target to mention `x` itself,
and `Ce-Pro` would then introduce `x` into `t'`. So the bound would escape its own scope.

The fix is to require `Δ` scoped in the base context rather than the extended one — which is
again the coherence-style discipline `PSS/CtxCommutation` needs, and again exactly what MPSS
arranges by making the popped operand the bound. Stating it needs the ambient list threaded
through `prevalid`, so it is recorded here rather than assumed.

## What this establishes

Scoping and context reduction for the rebuilt system:

- **`fv-⟶≐`** — the scoped replacement for v1's `fv-⟶≡`. Equivalence over `⟶≐` *can* introduce
  free variables, via `Ce-Pro`, so "never adds a variable" is false; what holds is that reduction
  keeps terms inside any list that already contains everything `Δ` can unfold to.
- **`CtxRedᶜ` / `StkRedᶜ`** and their domain and lookup lemmas — the Figure 3 analogue over `⟶≐`.

**Owed, with the reason identified:** preservation of prevalidity, which needs `Δ` scoped in the
base context rather than the extended one, for the reason above.