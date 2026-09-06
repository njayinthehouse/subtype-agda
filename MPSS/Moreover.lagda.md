# MPSS: Lemma 2's second conjunct is false

Lemma 2 of v2 has two conjuncts. The first is the diamond. The second — the "Moreover" — says:

> for any variable `x`, if in the derivation of `Γ₀;s₀ ⊢ t₀ ⟶≡ t₁` (respectively `t₀ ⟶≡ t₂`)
> there isn't an application of the Rule `Me-Pro` that makes a promotion of variable `x`, then in
> the derivation `Γ₂;s₂ ⊢ t₂ ⟶≡ t₃` (respectively `Γ₁;s₁ ⊢ t₁ ⟶≡ t₃`) there won't be an
> application of the Rule `Me-Pro` that makes a promotion of variable `x`.

The proof's `Me-App`/`Me-Bet` case rests on it: the joining derivation for the body is obtained
under `x ≡ v₁` and has to be moved back to `Γ₁;s₁`, which is only possible if it never promotes
`x`, and the text says "the induction process ensures" that it does not. So the conjunct is
load-bearing.

It is false. Take `Γ₀ = y ≡ ⊤, x′ ≡ y`, the subject `x′`, the reflexive edge `x′ ⟶≡ x′`, the
promoting edge `x′ ⟶≡ y`, a context reduction that rewrites `x′`'s annotation to `⊤` (which
promotes `y`), and the reflexive context reduction on the other side. Every join is `⊤`, and the
edge from `y` to `⊤` at `Γ₀` promotes `y` — although the reflexive edge promotes nothing.

What fails is not the diamond: the join exists. What fails is the claim that a variable not
promoted on one side stays unpromoted on the other. The promotion is forced by the *context
reduction*, which the conjunct does not mention. `MPSS/Diamond` (when it exists) has to carry a
different invariant: one that also requires the context reduction's own annotation steps to avoid
`x`. That version is what the `Me-App`/`Me-Bet` case actually needs, since the parameter it binds
is fresh for everything in the context reduction.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Moreover where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; Σ; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.CtxReduction
```

## Promotion of a variable in a derivation

`Promotes x d` holds when `d` contains an application of `Me-Pro` to the variable `x`, at any
depth, under any binder.

```agda
data Promotes (x : Name) : ∀ {Γ s t u} → Γ ∣ s ⊢ t ⟶ᵉ u → Set where

  pro-here : ∀ {Γ s α α'} {pv : Γ ∣ s prevalid} {m : x ≐ α ∈ Γ} {d : Γ ∣ s ⊢ α ⟶ᵉ α'}
           → Promotes x (Me-Pro pv m d)

  pro-pro  : ∀ {Γ s y α α'} {pv : Γ ∣ s prevalid} {m : y ≐ α ∈ Γ} {d : Γ ∣ s ⊢ α ⟶ᵉ α'}
           → Promotes x d → Promotes x (Me-Pro pv m d)

  pro-appˡ : ∀ {Γ s u u' v v'} {d : Γ ∣ (v ∷ s) ⊢ u ⟶ᵉ u'} {e : Γ ∣ [] ⊢ v ⟶ᵉ v'}
           → Promotes x d → Promotes x (Me-App d e)

  pro-appʳ : ∀ {Γ s u u' v v'} {d : Γ ∣ (v ∷ s) ⊢ u ⟶ᵉ u'} {e : Γ ∣ [] ⊢ v ⟶ᵉ v'}
           → Promotes x e → Promotes x (Me-App d e)

  pro-betˡ : ∀ {Γ s t u u' v v'} {L : List Name}
               {F : ∀ {z} → z ∉ L → Γ ∣ s ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)}
               {e : Γ ∣ [] ⊢ v ⟶ᵉ v'}
           → ∀ {z} (p : z ∉ L) → Promotes x (F p) → Promotes x (Me-Bet {t = t} {u = u} {u' = u'} L F e)

  pro-betʳ : ∀ {Γ s t u u' v v'} {L : List Name}
               {F : ∀ {z} → z ∉ L → Γ ∣ s ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)}
               {e : Γ ∣ [] ⊢ v ⟶ᵉ v'}
           → Promotes x e → Promotes x (Me-Bet {t = t} {u = u} {u' = u'} L F e)

  pro-funˡ : ∀ {Γ t t' u u'} {L : List Name} {d : Γ ∣ [] ⊢ t ⟶ᵉ t'}
               {F : ∀ {z} → z ∉ L → ((z , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)}
           → Promotes x d → Promotes x (Me-Fun {u = u} {u' = u'} L d F)

  pro-funʳ : ∀ {Γ t t' u u'} {L : List Name} {d : Γ ∣ [] ⊢ t ⟶ᵉ t'}
               {F : ∀ {z} → z ∉ L → ((z , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)}
           → ∀ {z} (p : z ∉ L) → Promotes x (F p) → Promotes x (Me-Fun {u = u} {u' = u'} L d F)

  pro-fopˡ : ∀ {Γ s α t t' u u'} {L : List Name} {d : Γ ∣ [] ⊢ t ⟶ᵉ t'}
               {F : ∀ {z} → z ∉ L → ((z , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)}
           → Promotes x d → Promotes x (Me-FOp {u = u} {u' = u'} L d F)

  pro-fopʳ : ∀ {Γ s α t t' u u'} {L : List Name} {d : Γ ∣ [] ⊢ t ⟶ᵉ t'}
               {F : ∀ {z} → z ∉ L → ((z , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)}
           → ∀ {z} (p : z ∉ L) → Promotes x (F p) → Promotes x (Me-FOp {u = u} {u' = u'} L d F)
```

## The conjunct, as printed

Only the direction from the first edge to the second is stated here; the refutation below
does not need the other one.

```agda
Moreover : Set
Moreover = ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂}
           (d₁ : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₁) (d₂ : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂)
         → Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
         → ∃[ t₃ ] Σ (Γ₁ ∣ s₁ ⊢ t₁ ⟶ᵉ t₃) λ f₁ → Σ (Γ₂ ∣ s₂ ⊢ t₂ ⟶ᵉ t₃) λ f₂ →
             (∀ x → ¬ Promotes x d₁ → ¬ Promotes x f₂)
```

## The instance

Names are numbers: `y = 0`, `x′ = 1`.

```agda
Γ₀ Γ₁ : Ctx
Γ₀ = (1 , eqv , fvar 0) ∷ (0 , eqv , Top) ∷ []
Γ₁ = (1 , eqv , Top)    ∷ (0 , eqv , Top) ∷ []

pv-tail : ((0 , eqv , Top) ∷ []) ∣ [] prevalid
pv-tail = Pv-Nil (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ()))

pv₀ : Γ₀ ∣ [] prevalid
pv₀ = Pv-Nil (Pv-EqA (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ())) (λ { (there ()) }) lc-fvar
                     (λ { (here refl) → here refl }))

-- the reflexive edge, and the promoting edge
d₁ : Γ₀ ∣ [] ⊢ fvar 1 ⟶ᵉ fvar 1
d₁ = Me-Var pv₀

d₂ : Γ₀ ∣ [] ⊢ fvar 1 ⟶ᵉ fvar 0
d₂ = Me-Pro pv₀ (here refl) (Me-Var pv₀)

-- the context reduction that promotes y inside x′'s annotation, and the reflexive one
c₁ : Γ₀ ∣ [] ↣ Γ₁ ∣ []
c₁ = Ct-Ann Ct-Refl (Me-Pro pv-tail (here refl) (Me-Top pv-tail))

c₂ : Γ₀ ∣ [] ↣ Γ₀ ∣ []
c₂ = Ct-Refl
```

## Inversion at the instance

`⊤` reduces only to `⊤`; at `Γ₁`, `x′` reduces to itself or to `⊤`; at `Γ₀`, `y` reduces to
itself or, by promoting `y`, to `⊤`.

```agda
top-only : ∀ {Γ s u} → Γ ∣ s ⊢ Top ⟶ᵉ u → u ≡ Top
top-only (Me-Top _) = refl

from-x′ : ∀ {u} → Γ₁ ∣ [] ⊢ fvar 1 ⟶ᵉ u → (u ≡ fvar 1) ⊎ (u ≡ Top)
from-x′ (Me-Var _)                       = inj₁ refl
from-x′ (Me-Pro _ (here refl) d)         = inj₂ (top-only d)
from-x′ (Me-Pro _ (there (here ())) d)
from-x′ (Me-Pro _ (there (there ())) d)

from-y : ∀ {u} (f : Γ₀ ∣ [] ⊢ fvar 0 ⟶ᵉ u) → (u ≡ fvar 0) ⊎ ((u ≡ Top) × Promotes 0 f)
from-y (Me-Var _)                          = inj₁ refl
from-y (Me-Pro _ (here ()) d)
from-y (Me-Pro _ (there (here refl)) d)    = inj₂ (top-only d , pro-here)
from-y (Me-Pro _ (there (there ())) d)
```

## The refutation

The reflexive edge promotes nothing, so the conjunct promises a join at which `y` is not
promoted from `Γ₀`. Every join is `⊤`, and reaching `⊤` from `y` at `Γ₀` promotes `y`.

```agda
var-no-pro : ∀ {Γ s x y} {pv : Γ ∣ s prevalid} → ¬ Promotes x (Me-Var {x = y} pv)
var-no-pro ()

moreover-false : ¬ Moreover
moreover-false h with h d₁ d₂ c₁ c₂
... | t₃ , f₁ , f₂ , clause with from-x′ f₁ | from-y f₂
...   | inj₁ refl | inj₁ ()
...   | inj₁ refl | inj₂ (() , _)
...   | inj₂ refl | inj₁ ()
...   | inj₂ refl | inj₂ (_ , p) = clause 0 var-no-pro p
```

## What this establishes

`moreover-false`: the second conjunct of Lemma 2, in the direction from the first edge to the
second, is false, and stays false however the join is chosen — the instance forces `t₃ = ⊤` and
forces the `Me-Pro` on `y`. The diamond itself holds at the instance.

The other direction is refuted by the mirror instance (swap the roles of the two edges and of the
two context reductions), and is not written out.

The variable the conjunct fails on is promoted by the *context reduction* `c₁`, which the
conjunct does not constrain. The conjunct that the `Me-App`/`Me-Bet` case can use, and that a
proof of the diamond can maintain, is the one that also assumes `x` is promoted nowhere in the
context reduction on the other side; for the fresh parameter that case binds, that assumption
holds outright.
