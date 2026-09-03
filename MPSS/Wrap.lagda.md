# MPSS: wrapping chains under a binder

`MPSS/Frame` wraps a chain under an application by construction. Under a binder the wrapping
needs a cofinite family of body steps, one per fresh name, from the chain at a single fresh name
— which is what the close-and-rename lemmas of `MPSS/Rename` supply. The side condition moves
along: a body term `z`, open at `x`, stands for the abstraction `λx≤w. close x z`. It also
records local closure of `z`, because the rename lemmas need every intermediate locally closed
and a chain's right endpoint has no other source of it.

Two shapes: `Ms-Fun`/`Me-Fun` at the empty stack with the parameter bound `x ≤ w`, and
`Ms-FOp`/`Me-FOp` with an operand `α` popped from the stack and the parameter bound `x ≡ α`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Wrap where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Frame
open import MPSS.Rename using (⟶ᵉ-rename-head; ⟶ˢ-rename-head; x∉-w)
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
open import PSS.Close using (close-open; open-close; fv-close)
open import PSS.Syntax using (closeRec)
```

## The side condition under a binder

```agda
Fun : (Tm → Set) → Tm → Name → Tm → Set
Fun P w x z = LC z × P (lam w (closeRec 0 x z))
```

## Single steps

Stated over an arbitrary open source `a`, which is rewritten as `(close x a) ^ x` so that the
rename-head lemma applies.

```agda
wrapˢ-fun : ∀ {Γ w a a′} x → x ∉ dom Γ → LC a → LC a′
          → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ˢ a′
          → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ˢ lam w (closeRec 0 x a′)
wrapˢ-fun {Γ} {w} {a} {a′} x x∉Γ la la′ d = Ms-Fun (dom Γ) fam
  where
    pv = prevalid-ctx (⟶ˢ-prevalid d)

    d′ : ((x , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ˢ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ˢ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ˢ-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) (λ ()) la′ d′

wrapᵉ-fun : ∀ {Γ w a a′} x → x ∉ dom Γ → LC a → LC a′
          → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ a′
          → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ᵉ lam w (closeRec 0 x a′)
wrapᵉ-fun {Γ} {w} {a} {a′} x x∉Γ la la′ d =
  Me-Fun (dom Γ) (⟶ᵉ-refl (Pv-Nil (tail-prevalid pv)) (head-lc pv) (head-fv pv)) fam
  where
    pv = prevalid-ctx (⟶ᵉ-prevalid d)

    d′ : ((x , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ᵉ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ᵉ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ᵉ-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) (λ ()) la′ d′
```

With an operand popped, the annotation `w` is not in the context, so its local closure and
scoping are hypotheses.

```agda
wrapˢ-fop : ∀ {Γ s w α a a′} x → x ∉ dom Γ → x ∉ fvStack s → LC a → LC a′
          → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ˢ a′
          → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ˢ lam w (closeRec 0 x a′)
wrapˢ-fop {Γ} {s} {w} {α} {a} {a′} x x∉Γ x∉s la la′ d = Ms-FOp (dom Γ) fam
  where
    pv = prevalid-ctx (⟶ˢ-prevalid d)

    d′ : ((x , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ˢ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ˢ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ˢ-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) x∉s la′ d′

wrapᵉ-fop : ∀ {Γ s w α a a′} x → x ∉ dom Γ → x ∉ fvStack s → LC a → LC a′
          → LC w → fv w ⊑ dom Γ
          → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ᵉ a′
          → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ᵉ lam w (closeRec 0 x a′)
wrapᵉ-fop {Γ} {s} {w} {α} {a} {a′} x x∉Γ x∉s la la′ lw fw d =
  Me-FOp (dom Γ) (⟶ᵉ-refl (Pv-Nil (tail-prevalid pv)) lw fw) fam
  where
    pv = prevalid-ctx (⟶ᵉ-prevalid d)

    d′ : ((x , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ᵉ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ᵉ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ᵉ-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) x∉s la′ d′
```

## Chains, over open endpoints

Local closure of both ends is carried along; a transitive chain's middle term gets it from its
side condition.

```agda
◁-fun′ : ∀ {Γ P w a c} x → x ∉ dom Γ → LC a → LC c
       → ((x , sub , w) ∷ Γ) ∣ [] ⊢[ Fun P w x ] a ◁ c
       → Γ ∣ [] ⊢[ P ] lam w (closeRec 0 x a) ◁ lam w (closeRec 0 x c)
◁-fun′ x x∉ la lc (c-refl pv)       = c-refl (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
◁-fun′ x x∉ la lc (c-lf1 e d)       =
  c-lf1 (wrapᵉ-fun x x∉ la (⟶ᵉ-lc la e) e) (◁-fun′ x x∉ (⟶ᵉ-lc la e) lc d)
◁-fun′ x x∉ la lc (c-lf2 p st p′ d) =
  c-lf2 (proj₂ p) (wrapˢ-fun x x∉ la (⟶ˢ-lc la st) st) (proj₂ p′)
        (◁-fun′ x x∉ (⟶ˢ-lc la st) lc d)
◁-fun′ x x∉ la lc (c-rgh d e)       =
  c-rgh (◁-fun′ x x∉ la (⟶ᵉ-lc lc e) d) (wrapᵉ-fun x x∉ lc (⟶ᵉ-lc lc e) e)

◁*-fun′ : ∀ {Γ P w a c} x → x ∉ dom Γ → LC a → LC c
        → ((x , sub , w) ∷ Γ) ∣ [] ⊢[ Fun P w x ] a ◁* c
        → Γ ∣ [] ⊢[ P ] lam w (closeRec 0 x a) ◁* lam w (closeRec 0 x c)
◁*-fun′ x x∉ la lc (c-sub p d p′)   = c-sub (proj₂ p) (◁-fun′ x x∉ la lc d) (proj₂ p′)
◁*-fun′ x x∉ la lc (c-trs d₁ p d₂)  =
  c-trs (◁*-fun′ x x∉ la (proj₁ p) d₁) (proj₂ p) (◁*-fun′ x x∉ (proj₁ p) lc d₂)

◁-fop′ : ∀ {Γ P s w α a c} x → x ∉ dom Γ → x ∉ fvStack s → LC w → fv w ⊑ dom Γ → LC a → LC c
       → ((x , eqv , α) ∷ Γ) ∣ s ⊢[ Fun P w x ] a ◁ c
       → Γ ∣ (α ∷ s) ⊢[ P ] lam w (closeRec 0 x a) ◁ lam w (closeRec 0 x c)
◁-fop′ x x∉ x∉s lw fw la lc (c-refl pv) =
  c-refl (Pv-Sta (prevalid-strengthen x∉s pv) (head-lc ctx) (head-fv ctx))
  where ctx = prevalid-ctx pv
◁-fop′ x x∉ x∉s lw fw la lc (c-lf1 e d) =
  c-lf1 (wrapᵉ-fop x x∉ x∉s la (⟶ᵉ-lc la e) lw fw e) (◁-fop′ x x∉ x∉s lw fw (⟶ᵉ-lc la e) lc d)
◁-fop′ x x∉ x∉s lw fw la lc (c-lf2 p st p′ d) =
  c-lf2 (proj₂ p) (wrapˢ-fop x x∉ x∉s la (⟶ˢ-lc la st) st) (proj₂ p′)
        (◁-fop′ x x∉ x∉s lw fw (⟶ˢ-lc la st) lc d)
◁-fop′ x x∉ x∉s lw fw la lc (c-rgh d e) =
  c-rgh (◁-fop′ x x∉ x∉s lw fw la (⟶ᵉ-lc lc e) d) (wrapᵉ-fop x x∉ x∉s lc (⟶ᵉ-lc lc e) lw fw e)

◁*-fop′ : ∀ {Γ P s w α a c} x → x ∉ dom Γ → x ∉ fvStack s → LC w → fv w ⊑ dom Γ → LC a → LC c
        → ((x , eqv , α) ∷ Γ) ∣ s ⊢[ Fun P w x ] a ◁* c
        → Γ ∣ (α ∷ s) ⊢[ P ] lam w (closeRec 0 x a) ◁* lam w (closeRec 0 x c)
◁*-fop′ x x∉ x∉s lw fw la lc (c-sub p d p′)  =
  c-sub (proj₂ p) (◁-fop′ x x∉ x∉s lw fw la lc d) (proj₂ p′)
◁*-fop′ x x∉ x∉s lw fw la lc (c-trs d₁ p d₂) =
  c-trs (◁*-fop′ x x∉ x∉s lw fw la (proj₁ p) d₁) (proj₂ p)
        (◁*-fop′ x x∉ x∉s lw fw (proj₁ p) lc d₂)
```

## Chains, over bodies opened at the fresh name

The usual shape: the endpoints are `b ^ x` and `c ^ x` with `x` fresh for `b` and `c`, and the
wrapped endpoints are `λx≤w.b` and `λx≤w.c`, by `close-open`.

```agda
◁*-fun : ∀ {Γ P w b c} x → x ∉ dom Γ → x ∉ fv b → x ∉ fv c → LC (b ^ fvar x) → LC (c ^ fvar x)
       → ((x , sub , w) ∷ Γ) ∣ [] ⊢[ Fun P w x ] (b ^ fvar x) ◁* (c ^ fvar x)
       → Γ ∣ [] ⊢[ P ] lam w b ◁* lam w c
◁*-fun {Γ} {P} {w} {b} {c} x x∉ x∉b x∉c lb lc d =
  subst (λ z → Γ ∣ [] ⊢[ P ] lam w z ◁* lam w c) (close-open 0 x b x∉b)
    (subst (λ z → Γ ∣ [] ⊢[ P ] lam w (closeRec 0 x (b ^ fvar x)) ◁* lam w z)
           (close-open 0 x c x∉c)
           (◁*-fun′ x x∉ lb lc d))

◁*-fop : ∀ {Γ P s w α b c} x → x ∉ dom Γ → x ∉ fvStack s → LC w → fv w ⊑ dom Γ
       → x ∉ fv b → x ∉ fv c → LC (b ^ fvar x) → LC (c ^ fvar x)
       → ((x , eqv , α) ∷ Γ) ∣ s ⊢[ Fun P w x ] (b ^ fvar x) ◁* (c ^ fvar x)
       → Γ ∣ (α ∷ s) ⊢[ P ] lam w b ◁* lam w c
◁*-fop {Γ} {P} {s} {w} {α} {b} {c} x x∉ x∉s lw fw x∉b x∉c lb lc d =
  subst (λ z → Γ ∣ (α ∷ s) ⊢[ P ] lam w z ◁* lam w c) (close-open 0 x b x∉b)
    (subst (λ z → Γ ∣ (α ∷ s) ⊢[ P ] lam w (closeRec 0 x (b ^ fvar x)) ◁* lam w z)
           (close-open 0 x c x∉c)
           (◁*-fop′ x x∉ x∉s lw fw lb lc d))
```

## What this establishes

Chains wrap under both binder rules, with the side condition transported as `Fun P w x`: a body
term `z` satisfies it when `z` is locally closed and the abstraction `λx≤w. close x z` satisfies
`P`. Together with `◁*-app` from `MPSS/Frame`, every covariant context former now has its
wrapping lemma. The renaming needed for the cofinite families is spent once, in the single-step
lemmas.
