# MPSS, candidate C: a term the stack-reading judgement accepts and Figure 4 rejects

The judgements of `MPSS/StackWf` are not a restriction of Figure 4. `Wc-FOp` checks the body of a
consumed abstraction under `x ≡ δ`, the operand, and never under the declared bound alone; so a
redex can be well-formed when its abstraction, taken alone, is not:

    (λx≤⊤. x ⊤) (λy≤⊤. y)

Under `x ≤ ⊤` the body `x ⊤` is ill-formed — `x` promotes to `⊤`, which is below no abstraction —
so Figure 4 rejects the term. Under `x ≡ λy≤⊤.y` the body is `(λy≤⊤.y) ⊤` in effect, and `wfˢ`
accepts it. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfAccepts where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.WellFormed
open import MPSS.StackWf
open import MPSS.Unconditional using (Thm-3wf)
```

## The term

```agda
g f t : Tm
g = lam Top (bvar 0)               -- λy≤⊤. y
f = lam Top (app (bvar 0) Top)     -- λx≤⊤. x ⊤
t = app f g

lc-g : LC g
lc-g = lc-lam [] lc-Top (λ _ → lc-fvar)

pv₀ : [] ∣ [] prevalid
pv₀ = Pv-Nil Pv-Emp

pv-g : [] ∣ (g ∷ []) prevalid
pv-g = Pv-Sta pv₀ lc-g (λ ())
```

## It is `wfˢ`

```agda
module _ {x : Name} where

  Γx : Ctx
  Γx = (x , eqv , g) ∷ []

  cx : Γx prevalid
  cx = Pv-EqA Pv-Emp (λ ()) lc-g (λ ())

  px : Γx ∣ [] prevalid
  px = Pv-Nil cx

  px⊤ : Γx ∣ (Top ∷ []) prevalid
  px⊤ = Pv-Sta px lc-Top (λ ())

  py : ∀ {y} → y ∉ (x ∷ []) → ((y , eqv , Top) ∷ Γx) ∣ [] prevalid
  py y∉ = Pv-Nil (Pv-EqA cx y∉ lc-Top (λ ()))

  wf-g⊤ : Γx ∣ (Top ∷ []) ⊢ g wfˢ
  wf-g⊤ = Wc-FOp (x ∷ []) (λ y∉ → Wc-PrE (py y∉) (here refl) (Wc-Top (py y∉))) (Wc-Top px)

  wf-cod : Γx ∣ (Top ∷ []) ⊢ lam Top Top wfˢ
  wf-cod = Wc-FOp (x ∷ []) (λ y∉ → Wc-Top (py y∉)) (Wc-Top px)

  g⟶ᵉg : Γx ∣ (Top ∷ []) ⊢ g ⟶ᵉ g
  g⟶ᵉg = Me-FOp {u' = bvar 0} (x ∷ []) (Me-Top px) (λ y∉ → Me-Var (py y∉))

  x≤ : Γx ∣ (Top ∷ []) ⊢ fvar x ≤ lam Top Top
  x≤ = As-Left-1 (Ms-Equ px⊤ (Me-Pro px⊤ (here refl) g⟶ᵉg))
      (As-Left-1 (Ms-FOp {u' = Top} (x ∷ []) (λ y∉ → Ms-Top (py y∉))) (As-Refl px⊤))

  wf-body : Γx ∣ [] ⊢ app (fvar x) Top wfˢ
  wf-body = Wc-App (Wc-Sub (Wc-Rule (Wc-PrE px⊤ (here refl) wf-g⊤) wf-cod x≤))
                   (Wc-Sub (Wc-Rule (Wc-Top px) (Wc-Top px) (As-Refl px)))

wf-f : [] ∣ (g ∷ []) ⊢ f wfˢ
wf-f = Wc-FOp [] (λ {x} _ → wf-body {x}) (Wc-Top pv₀)

wf-cod₀ : [] ∣ (g ∷ []) ⊢ lam Top Top wfˢ
wf-cod₀ = Wc-FOp [] (λ {x} _ → Wc-Top (px {x})) (Wc-Top pv₀)

f≤ : [] ∣ (g ∷ []) ⊢ f ≤ lam Top Top
f≤ = As-Left-1 (Ms-FOp {u' = Top} [] (λ {x} _ → Ms-Top (px {x}))) (As-Refl pv-g)

wf-g : [] ∣ [] ⊢ g wfˢ
wf-g = Wc-Fun [] (λ _ → Wc-PrS pvy (here refl) (Wc-Top pvy)) (Wc-Top pv₀)
  where
    pvy : ∀ {y} → ((y , sub , Top) ∷ []) ∣ [] prevalid
    pvy = Pv-Nil (Pv-Ctx Pv-Emp (λ ()) lc-Top (λ ()))

wfˢ-t : [] ∣ [] ⊢ t wfˢ
wfˢ-t = Wc-App (Wc-Sub (Wc-Rule wf-f wf-cod₀ f≤))
               (Wc-Sub (Wc-Rule wf-g (Wc-Top pv₀) (As-Left-1 (Ms-Top pv₀) (As-Refl pv₀))))
```

## Figure 4 rejects it

Under `x ≤ ⊤` a variable is below no abstraction: it promotes to `⊤` or stays, and `⊤` stays.

```agda
Top≰ : ∀ {Γ s a b} → ¬ (Γ ∣ s ⊢ Top ≤ lam a b)
Top≰ (As-Left-1 (Ms-Top _) d)            = Top≰ d
Top≰ (As-Left-1 (Ms-Equ _ (Me-Top _)) d) = Top≰ d
Top≰ (As-Right d (Me-Fun _ _ _))         = Top≰ d
Top≰ (As-Right d (Me-FOp _ _ _))         = Top≰ d

var≰ : ∀ {x s a b} → ¬ (((x , sub , Top) ∷ []) ∣ s ⊢ fvar x ≤ lam a b)
var≰ (As-Left-1 (Ms-Pro _ (here refl)) d)               = Top≰ d
var≰ (As-Left-1 (Ms-Top _) d)                           = Top≰ d
var≰ (As-Left-1 (Ms-Equ _ (Me-Var _)) d)                = var≰ d
var≰ (As-Left-1 (Ms-Equ _ (Me-Pro _ (there ()) _)) d)
var≰ (As-Right d (Me-Fun _ _ _))                        = var≰ d
var≰ (As-Right d (Me-FOp _ _ _))                        = var≰ d

¬wf-t : ¬ ([] ⊢ t wf)
¬wf-t (Wf-App d₁ _) with ⊑*wf⇒wfˡ d₁
... | Wf-Fun L F _ with F {fresh L} (fresh-∉ L)
...   | Wf-App e₁ _ = var≰ (Thm-3wf e₁)
```

## What this establishes

`wfˢ-t` and `¬wf-t`: the stack-reading judgement accepts `(λx≤⊤. x ⊤) (λy≤⊤. y)` and Figure 4 does
not. Candidate C types a redex by what its body does with the actual operand, as v1 does; the
declared bound is consulted only for an abstraction that meets no operand (`Wc-Fun`) and for the
operand itself (`Wc-App`'s second premise). With `MPSS/StackWfRejects` (the term `t₆`, accepted by
Figure 4) the two judgements are incomparable.
