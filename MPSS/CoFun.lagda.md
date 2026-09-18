# MPSS: well-subtyping is a congruence under a binder

Conjecture 8's induction on the covariant context needs, at `λx≤a.Co`, that a well-subtyping
chain between the bodies at every fresh name lifts to the abstractions (`FunCongr*` in
`MPSS/Conjecture8Star`). The chain is given at every fresh name but its derivations differ from
name to name, so one name is chosen, its chain is closed over that name step by step, and each
step's cofinite family is recovered by renaming — `MPSS/Wrap` for the reduction steps,
`MPSS/WfRename` (through `wrap-wf`) for the well-formedness premises that `Ws-Lf2`, `Ws-Sub` and
`Ws-Trs` carry.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CoFun where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import MPSS.WellFormed
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
open import MPSS.Wrap using (wrapᵉ-fun; wrapˢ-fun)
open import MPSS.Prop17Chain using (wrap-wf)
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; closeRec)
open import PSS.Close using (close-open)
```

## One layer, closed over the chosen name

Both ends locally closed, so that the wrap lemmas apply to every intermediate; local closure
travels along the steps in each direction.

```agda
layer-fun : ∀ {Γ a p q} x → x ∉ dom Γ → LC p → LC q → Γ ⊢ a wf
          → ((x , sub , a) ∷ Γ) ⊢ p ⊑wf[ sub-m ] q
          → Γ ⊢ lam a (closeRec 0 x p) ⊑wf[ sub-m ] lam a (closeRec 0 x q)
layer-fun x x∉ lp lq wa (Ws-Rfl pv)        = Ws-Rfl (wf⇒prevalid wa)
layer-fun x x∉ lp lq wa (Ws-Lf1 e d)       =
  Ws-Lf1 (wrapᵉ-fun x x∉ lp (⟶ᵉ-lc lp e) e) (layer-fun x x∉ (⟶ᵉ-lc lp e) lq wa d)
layer-fun x x∉ lp lq wa (Ws-Lf2 w e w' d)  =
  Ws-Lf2 (wrap-wf x x∉ lp w wa) (wrapˢ-fun x x∉ lp (⟶ˢ-lc lp e) e)
         (wrap-wf x x∉ (⟶ˢ-lc lp e) w' wa) (layer-fun x x∉ (⟶ˢ-lc lp e) lq wa d)
layer-fun x x∉ lp lq wa (Ws-Rgh d e)       =
  Ws-Rgh (layer-fun x x∉ lp (⟶ᵉ-lc lq e) wa d) (wrapᵉ-fun x x∉ lq (⟶ᵉ-lc lq e) e)

chain-fun : ∀ {Γ a p q} x → x ∉ dom Γ → Γ ⊢ a wf
          → ((x , sub , a) ∷ Γ) ⊢ p ⊑*wf[ sub-m ] q
          → Γ ⊢ lam a (closeRec 0 x p) ⊑*wf[ sub-m ] lam a (closeRec 0 x q)
chain-fun x x∉ wa (Ws-Sub w d w')  =
  Ws-Sub (wrap-wf x x∉ (wf⇒lc w) w wa) (layer-fun x x∉ (wf⇒lc w) (wf⇒lc w') wa d)
         (wrap-wf x x∉ (wf⇒lc w') w' wa)
chain-fun x x∉ wa (Ws-Trs d₁ wm d₂) =
  Ws-Trs (chain-fun x x∉ wa d₁) (wrap-wf x x∉ (wf⇒lc wm) wm wa) (chain-fun x x∉ wa d₂)
```

## The congruence

```agda
FunCongr : ∀ {Γ a b b'} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , sub , a) ∷ Γ) ⊢ (b ^ fvar x) ⊑*wf[ sub-m ] (b' ^ fvar x))
         → Γ ⊢ lam a b wf → Γ ⊢ lam a b' wf
         → Γ ⊢ lam a b ⊑*wf[ sub-m ] lam a b'
FunCongr {Γ} {a} {b} {b'} L F (Wf-Fun _ _ wa) _ =
  subst₂ (λ p q → Γ ⊢ lam a p ⊑*wf[ sub-m ] lam a q)
         (close-open 0 x b x∉b) (close-open 0 x b' x∉b')
         (chain-fun x x∉Γ wa (F x∉L))
  where
    A    = L ++ dom Γ ++ fv b ++ fv b'
    x    = fresh A
    x∉A  = fresh-∉ A
    x∉L  = ∉-++ˡ x∉A
    x∉Γ  = ∉-++ˡ (∉-++ʳ L x∉A)
    x∉b  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L x∉A))
    x∉b' = ∉-++ʳ (fv b) (∉-++ʳ (dom Γ) (∉-++ʳ L x∉A))
```

## What this establishes

`FunCongr`, the abstraction congruence of well-subtyping, with nothing assumed: the piece
Conjecture 8's context induction needs at `λx≤a.Co`. Its statement opens the bodies at the fresh
name, so it applies to a covariant context whose inner terms mention the binder — the form
`MPSS/Assumed`'s `Conj-8` needs, which has no `CoLC` premise.
