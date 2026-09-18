# MPSS: renaming a bound variable in a well-formedness derivation

`MPSS/Rename` transports a reduction derivation under a bound name `x` to one under a fresh
`y`. The well-formedness judgements need the same transport: `Wf-Fun` binds its parameter
cofinitely, so any proof that builds a well-formed abstraction from a body at one fresh name has
to hand back the whole family. This is the renaming lemma for the three mutually inductive
judgements `wf`, `⊑wf` and `⊑*wf`, by mutual induction, with the reduction cases delegated to
`⟶ᵉ-rename` and `⟶ˢ-rename` at the empty stack.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.WfRename where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Rename
  using (substCtx; ∈-substCtx; x∉-domΔ; x∉-domΓ; prevalid-rename-ctx;
         ⟶ᵉ-rename; ⟶ˢ-rename; open-rename)
open import PSS.Syntax using (subst-fvar-≡; subst-fvar-≢; ∉-tail)
```

## The three lemmas

```agda
wf-rename   : ∀ (Δ : Ctx) {Γ x y a w t}
            → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
            → (Δ ++ (x , a , w) ∷ Γ) ⊢ t wf
            → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ⊢ (t [ x := fvar y ]) wf

⊑wf-rename  : ∀ (Δ : Ctx) {Γ x y a w u m v}
            → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
            → (Δ ++ (x , a , w) ∷ Γ) ⊢ u ⊑wf[ m ] v
            → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)
                ⊢ (u [ x := fvar y ]) ⊑wf[ m ] (v [ x := fvar y ])

⊑*wf-rename : ∀ (Δ : Ctx) {Γ x y a w u m v}
            → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
            → (Δ ++ (x , a , w) ∷ Γ) ⊢ u ⊑*wf[ m ] v
            → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)
                ⊢ (u [ x := fvar y ]) ⊑*wf[ m ] (v [ x := fvar y ])
```

A variable is well-formed by its entry. The entry is in `Δ` (renamed along with it), is the
entry for `x` itself (which becomes the entry for `y`), or is in `Γ` (untouched).

```agda
wf-rename Δ {Γ} {x} {y} {a} {w} y∉ (Wf-PrS {x = z} {t} pv mem) with ∈-++⁻ Δ mem
... | inj₁ m = goal
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ pv (subst (_∈ dom Δ) (sym p) (∈-dom m))
    goal : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ⊢ ((fvar z) [ x := fvar y ]) wf
    goal rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Wf-PrS (prevalid-rename-ctx Δ y∉ pv) (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m))
... | inj₂ (here refl) = goal
  where
    goal : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ⊢ ((fvar x) [ x := fvar y ]) wf
    goal rewrite subst-fvar-≡ {x} (fvar y) =
      Wf-PrS (prevalid-rename-ctx Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl))
... | inj₂ (there m) = goal
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ pv (subst (_∈ dom Γ) (sym p) (∈-dom m))
    goal : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ⊢ ((fvar z) [ x := fvar y ]) wf
    goal rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Wf-PrS (prevalid-rename-ctx Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m))

wf-rename Δ {Γ} {x} {y} {a} {w} y∉ (Wf-PrE {x = z} {α} pv mem) with ∈-++⁻ Δ mem
... | inj₁ m = goal
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ pv (subst (_∈ dom Δ) (sym p) (∈-dom m))
    goal : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ⊢ ((fvar z) [ x := fvar y ]) wf
    goal rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Wf-PrE (prevalid-rename-ctx Δ y∉ pv) (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m))
... | inj₂ (here refl) = goal
  where
    goal : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ⊢ ((fvar x) [ x := fvar y ]) wf
    goal rewrite subst-fvar-≡ {x} (fvar y) =
      Wf-PrE (prevalid-rename-ctx Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl))
... | inj₂ (there m) = goal
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ pv (subst (_∈ dom Γ) (sym p) (∈-dom m))
    goal : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ⊢ ((fvar z) [ x := fvar y ]) wf
    goal rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Wf-PrE (prevalid-rename-ctx Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m))

wf-rename Δ y∉ (Wf-Top pv) = Wf-Top (prevalid-rename-ctx Δ y∉ pv)
```

The binder case chooses a body name avoiding `x` and `y` and applies the induction hypothesis
with the new entry prepended to `Δ`; renaming commutes with opening at that name.

```agda
wf-rename Δ {Γ} {x} {y} {a} {w} y∉ (Wf-Fun {t = t} {u = u} L F wt) =
  Wf-Fun (x ∷ y ∷ L) body (wf-rename Δ y∉ wt)
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
             ⊢ ((u [ x := fvar y ]) ^ fvar z) wf
    body {z} z∉ =
      subst (λ q → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ⊢ q wf)
            (open-rename y x≢z u)
            (wf-rename ((z , sub , t) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))
        y∉' : y ∉ dom ((z , sub , t) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there q) = y∉ q

wf-rename Δ y∉ (Wf-App d₁ d₂) = Wf-App (⊑*wf-rename Δ y∉ d₁) (⊑*wf-rename Δ y∉ d₂)
```

The subtyping judgements delegate their reduction premises, which sit at the empty stack.

```agda
⊑wf-rename Δ y∉ (Ws-Rfl pv)        = Ws-Rfl (prevalid-rename-ctx Δ y∉ pv)
⊑wf-rename Δ y∉ (Ws-Lf1 e d)       = Ws-Lf1 (⟶ᵉ-rename Δ y∉ e) (⊑wf-rename Δ y∉ d)
⊑wf-rename Δ y∉ (Ws-Lf2 w e w' d)  =
  Ws-Lf2 (wf-rename Δ y∉ w) (⟶ˢ-rename Δ y∉ e) (wf-rename Δ y∉ w') (⊑wf-rename Δ y∉ d)
⊑wf-rename Δ y∉ (Ws-Rgh d e)       = Ws-Rgh (⊑wf-rename Δ y∉ d) (⟶ᵉ-rename Δ y∉ e)

⊑*wf-rename Δ y∉ (Ws-Sub w d w')   = Ws-Sub (wf-rename Δ y∉ w) (⊑wf-rename Δ y∉ d) (wf-rename Δ y∉ w')
⊑*wf-rename Δ y∉ (Ws-Trs d₁ w d₂)  = Ws-Trs (⊑*wf-rename Δ y∉ d₁) (wf-rename Δ y∉ w) (⊑*wf-rename Δ y∉ d₂)
```

## At the head of the context

The form the binder lemmas use: the renamed variable is the most recent entry.

```agda
wf-rename-head : ∀ {Γ x y a w t}
               → y ∉ (x ∷ dom Γ)
               → ((x , a , w) ∷ Γ) ⊢ t wf
               → ((y , a , w) ∷ Γ) ⊢ (t [ x := fvar y ]) wf
wf-rename-head y∉ = wf-rename [] y∉
```

## What this establishes

Renaming for the three well-formedness judgements, with nothing assumed. It is what lets a
well-formed body at one fresh name become the cofinite family `Wf-Fun` demands — the missing
piece for lifting a chain of well-formed terms under a binder.
