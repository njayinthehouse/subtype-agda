# MPSS: annotating a promotion derivation for the push

`MPSS/PushWf` replays an *annotated* derivation `⇛`. This module produces the annotation from a
plain `⟶ˢ` derivation, so that the structural half of Conjecture 8's recursion is closed:

> a promotion at `Γˢ ∣ s₀`, the side condition at its two ends, and — for each variable the
> narrowing has rebound, and for each abstraction that meets an operand on the way — a supplier of
> the chain from the operand to the bound, give the well-subtyping chain at `Γᵉ ∣ s₀ ++ s`.

Everything a future proof has to add is in the two suppliers; nothing else about the derivation
is asked. The side condition is carried down unchanged: under an application `App P v u` *is*
`P (app u v)`, and under a binder `Fun P t x (u ^ x)` is `P (lam t u)` up to `close-open`. So at
every leaf that is not a narrowed variable the side condition at the leaf's two ends is the side
condition at the two ends of the whole step.

The suppliers are restricted to an abstract class `𝒫` of side conditions, closed under the two
wrappers, so that a caller can keep in it whatever it needs to build a chain — that `P` is
well-formedness of some wrapped term, with the facts that make the points of a lifted chain
satisfy it.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Annotate where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.StackPush using (prevalid-cons; fv-lam-ann; fv-lam-body; fv-app-op; fv-app-arg; fv-open-cons)
open import MPSS.Scope using (⟶ˢ-lc)
open import MPSS.Frame using (_∣_⊢[_]_◁*_; App)
open import MPSS.Wrap using (Fun)
open import MPSS.Push using (_▶_; m-nil; m-keep; m-eqv)
open import MPSS.PushWf
open import PSS.Close using (close-open)
open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ)
```

## Extensions of a context

```agda
infix 4 _⊒_
data _⊒_ : Ctx → Ctx → Set where
  ⊒-refl : ∀ {Γ} → Γ ⊒ Γ
  ⊒-cons : ∀ {Γ′ Γ e} → Γ′ ⊒ Γ → (e ∷ Γ′) ⊒ Γ

⊒-tail : ∀ {Γ′ Γ e} → Γ′ ⊒ (e ∷ Γ) → Γ′ ⊒ Γ
⊒-tail ⊒-refl     = ⊒-cons ⊒-refl
⊒-tail (⊒-cons p) = ⊒-cons (⊒-tail p)
```

## The class of side conditions, and the suppliers

```agda
module _ (𝒫 : Ctx → Stack → (Tm → Set) → Set₁)
         (𝒫-app : ∀ {Γ s P v} → 𝒫 Γ s P → 𝒫 Γ (v ∷ s) (App P v))
         (𝒫-fop : ∀ {Γ s P α t x} → 𝒫 Γ (α ∷ s) P → x ∉ dom Γ
                → 𝒫 ((x , eqv , α) ∷ Γ) s (Fun P t x))
         (𝒫-fun : ∀ {Γ P t x} → 𝒫 Γ [] P → x ∉ dom Γ
                → 𝒫 ((x , sub , t) ∷ Γ) [] (Fun P t x))
         where

  -- the chain from the operand to the bound, at any stack of any extension, for any admissible
  -- side condition that holds at the bound
  Supply : Ctx → Tm → Tm → Set₁
  Supply Γ₀ α t = ∀ {Γ′ σ P} → Γ′ ⊒ Γ₀ → 𝒫 Γ′ σ P → Γ′ ∣ σ prevalid → P t
                → Γ′ ∣ σ ⊢[ P ] α ◁* t

  supply-tail : ∀ {Γ₀ e α t} → Supply Γ₀ α t → Supply (e ∷ Γ₀) α t
  supply-tail sup p = sup (⊒-tail p)

  -- the narrowing, with a supplier at each rebound variable
  infix 4 _▶ᴸ_
  data _▶ᴸ_ : Ctx → Ctx → Set₁ where
    l-nil  : [] ▶ᴸ []
    l-keep : ∀ {Γˢ Γᵉ x a t} → Γˢ ▶ᴸ Γᵉ → ((x , a , t) ∷ Γˢ) ▶ᴸ ((x , a , t) ∷ Γᵉ)
    l-eqv  : ∀ {Γˢ Γᵉ x w α} → Γˢ ▶ᴸ Γᵉ → LC α → fv α ⊑ dom Γᵉ
           → Supply ((x , eqv , α) ∷ Γᵉ) α w
           → ((x , sub , w) ∷ Γˢ) ▶ᴸ ((x , eqv , α) ∷ Γᵉ)

  forget : ∀ {Γˢ Γᵉ} → Γˢ ▶ᴸ Γᵉ → Γˢ ▶ Γᵉ
  forget l-nil             = m-nil
  forget (l-keep n)        = m-keep (forget n)
  forget (l-eqv n lα fα _) = m-eqv (forget n) lα fα

  -- a subtype lookup survives, or hits a rebound variable and returns its supplier
  lookup : ∀ {Γˢ Γᵉ y t} → Γˢ ▶ᴸ Γᵉ → y ≤ t ∈ Γˢ
         → (y ≤ t ∈ Γᵉ)
         ⊎ (∃[ α ] ((y ≐ α ∈ Γᵉ) × LC α × (fv α ⊑ dom Γᵉ) × Supply Γᵉ α t))
  lookup (l-keep n)          (here refl) = inj₁ (here refl)
  lookup (l-eqv n lα fα sup) (here refl) = inj₂ (_ , here refl , lα , (λ h → there (fα h)) , sup)
  lookup (l-keep n) (there m) with lookup n m
  ... | inj₁ k                      = inj₁ (there k)
  ... | inj₂ (α , k , lα , fα , sup) = inj₂ (α , there k , lα , (λ h → there (fα h)) , supply-tail sup)
  lookup (l-eqv n _ _ _) (there m) with lookup n m
  ... | inj₁ k                      = inj₁ (there k)
  ... | inj₂ (α , k , lα , fα , sup) = inj₂ (α , there k , lα , (λ h → there (fα h)) , supply-tail sup)
```

## The annotation

The second supplier, `NewLeaf`, is asked when an abstraction meets an operand: the chain from that
operand to the abstraction's annotation. It is given everything in hand at that point — the
narrowing so far with its suppliers, the step itself, the side condition at its two ends.

```agda
  NewLeaf : Set₁
  NewLeaf = ∀ {Γˢ Γᵉ α s′ P t u u′ x}
          → Γˢ ▶ᴸ Γᵉ → Γˢ ∣ [] ⊢ lam t u ⟶ˢ lam t u′
          → Γᵉ ∣ (α ∷ s′) prevalid
          → 𝒫 Γᵉ (α ∷ s′) P → P (lam t u) → P (lam t u′) → x ∉ dom Γᵉ
          → Supply ((x , eqv , α) ∷ Γᵉ) α t

  module _ (new-leaf : NewLeaf) where

    annotate : ∀ {Γˢ Γᵉ s₀ P a a′} (s : Stack)
             → Γˢ ▶ᴸ Γᵉ → LC a → fv a ⊑ dom Γᵉ
             → Γˢ ∣ s₀ ⊢ a ⟶ˢ a′
             → 𝒫 Γᵉ (s₀ ++ s) P → Γᵉ ∣ (s₀ ++ s) prevalid
             → P a → P a′
             → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] a ⇛ a′

    annotate s n la fa (Ms-Pro pv m) ok pvᵉ pa pa′ with lookup n m
    ... | inj₁ k                      = q-pro pv m k pa pa′
    ... | inj₂ (α , k , lα , fα , sup) = q-pro-eqv pv m k lα fα pa (sup ⊒-refl ok pvᵉ pa′)

    annotate s n la fa (Ms-Top pv)   ok pvᵉ pa pa′ = q-top pv pa pa′
    annotate s n la fa (Ms-Equ pv e) ok pvᵉ pa pa′ = q-equ pv e pa pa′

    annotate s n (lc-app lu lv) fa (Ms-App {u = u} {v = v} d) ok pvᵉ pa pa′ =
      q-app (annotate s n lu (fv-app-op {u = u} {v = v} fa) d (𝒫-app ok)
                      (Pv-Sta pvᵉ lv (fv-app-arg {u = u} {v = v} fa)) pa pa′)

    annotate {Γᵉ = Γᵉ} {P = P} s n (lc-lam L₀ lt F₀) fa
             (Ms-FOp {s = s₀} {α = α} {t = t} {u = u} {u' = u′} L F) ok pvᵉ pa pa′ =
      q-fop (L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′) (fv-lam-ann {t = t} {b = u} fa) body
      where
        body : ∀ {x} → x ∉ (L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′)
             → _ ∣ ((x , eqv , α) ∷ Γᵉ) ∣ s₀ ∣ s ⊢[ Fun P t x ] (u ^ fvar x) ⇛ (u′ ^ fvar x)
        body {x} x∉ =
          annotate s (l-keep n) (F₀ x∉L₀) (fv-open-cons {b = u} x (fv-lam-body {t = t} {b = u} fa)) (F x∉L)
                   (𝒫-fop ok x∉Γ)
                   (prevalid-cons (prevalid-pop pvᵉ) x∉Γ (prevalid-head-lc pvᵉ) (prevalid-head-fv pvᵉ))
                   (F₀ x∉L₀ , subst (λ z → P (lam t z)) (sym (close-open 0 x u x∉u)) pa)
                   (⟶ˢ-lc (F₀ x∉L₀) (F x∉L) , subst (λ z → P (lam t z)) (sym (close-open 0 x u′ x∉u′)) pa′)
          where
            r₁   = ∉-++ʳ L₀ x∉
            r₂   = ∉-++ʳ L r₁
            r₃   = ∉-++ʳ (dom Γᵉ) r₂
            x∉L₀ = ∉-++ˡ x∉
            x∉L  = ∉-++ˡ r₁
            x∉Γ  : x ∉ dom Γᵉ
            x∉Γ  = ∉-++ˡ r₂
            x∉u  : x ∉ fv u
            x∉u  = ∉-++ˡ r₃
            x∉u′ : x ∉ fv u′
            x∉u′ = ∉-++ʳ (fv u) r₃

    annotate {Γᵉ = Γᵉ} {P = P} [] n (lc-lam L₀ lt F₀) fa
             (Ms-Fun {t = t} {u = u} {u' = u′} L F) ok pvᵉ pa pa′ =
      q-fun-nil (L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′) body
      where
        body : ∀ {x} → x ∉ (L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′)
             → _ ∣ ((x , sub , t) ∷ Γᵉ) ∣ [] ∣ [] ⊢[ Fun P t x ] (u ^ fvar x) ⇛ (u′ ^ fvar x)
        body {x} x∉ =
          annotate [] (l-keep n) (F₀ x∉L₀) (fv-open-cons {b = u} x (fv-lam-body {t = t} {b = u} fa)) (F x∉L)
                   (𝒫-fun ok x∉Γ)
                   (Pv-Nil (Pv-Ctx (prevalid-ctx pvᵉ) x∉Γ lt (fv-lam-ann {t = t} {b = u} fa)))
                   (F₀ x∉L₀ , subst (λ z → P (lam t z)) (sym (close-open 0 x u x∉u)) pa)
                   (⟶ˢ-lc (F₀ x∉L₀) (F x∉L) , subst (λ z → P (lam t z)) (sym (close-open 0 x u′ x∉u′)) pa′)
          where
            r₁   = ∉-++ʳ L₀ x∉
            r₂   = ∉-++ʳ L r₁
            r₃   = ∉-++ʳ (dom Γᵉ) r₂
            x∉L₀ = ∉-++ˡ x∉
            x∉L  = ∉-++ˡ r₁
            x∉Γ  : x ∉ dom Γᵉ
            x∉Γ  = ∉-++ˡ r₂
            x∉u  : x ∉ fv u
            x∉u  = ∉-++ˡ r₃
            x∉u′ : x ∉ fv u′
            x∉u′ = ∉-++ʳ (fv u) r₃

    annotate {Γᵉ = Γᵉ} {P = P} (α ∷ s′) n (lc-lam L₀ lt F₀) fa
             (Ms-Fun {t = t} {u = u} {u' = u′} L F) ok pvᵉ pa pa′ =
      q-fun-cons (L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′) lα fα (fv-lam-ann {t = t} {b = u} fa) body
      where
        lα = prevalid-head-lc pvᵉ
        fα = prevalid-head-fv pvᵉ
        body : ∀ {x} → x ∉ (L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′)
             → _ ∣ ((x , eqv , α) ∷ Γᵉ) ∣ [] ∣ s′ ⊢[ Fun P t x ] (u ^ fvar x) ⇛ (u′ ^ fvar x)
        body {x} x∉ =
          annotate s′ (l-eqv n lα fα (new-leaf {u = u} {u′ = u′} n (Ms-Fun {u' = u′} L F) pvᵉ ok pa pa′ x∉Γ))
                   (F₀ x∉L₀) (fv-open-cons {b = u} x (fv-lam-body {t = t} {b = u} fa)) (F x∉L)
                   (𝒫-fop ok x∉Γ)
                   (prevalid-cons (prevalid-pop pvᵉ) x∉Γ lα fα)
                   (F₀ x∉L₀ , subst (λ z → P (lam t z)) (sym (close-open 0 x u x∉u)) pa)
                   (⟶ˢ-lc (F₀ x∉L₀) (F x∉L) , subst (λ z → P (lam t z)) (sym (close-open 0 x u′ x∉u′)) pa′)
          where
            r₁   = ∉-++ʳ L₀ x∉
            r₂   = ∉-++ʳ L r₁
            r₃   = ∉-++ʳ (dom Γᵉ) r₂
            x∉L₀ = ∉-++ˡ x∉
            x∉L  = ∉-++ˡ r₁
            x∉Γ  : x ∉ dom Γᵉ
            x∉Γ  = ∉-++ˡ r₂
            x∉u  : x ∉ fv u
            x∉u  = ∉-++ˡ r₃
            x∉u′ : x ∉ fv u′
            x∉u′ = ∉-++ʳ (fv u) r₃
```

## The push, from a plain derivation

```agda
    push-from-leaves : ∀ {Γˢ Γᵉ s₀ P a a′} (s : Stack)
                     → Γˢ ▶ᴸ Γᵉ → LC a → fv a ⊑ dom Γᵉ
                     → Γˢ ∣ s₀ ⊢ a ⟶ˢ a′
                     → 𝒫 Γᵉ (s₀ ++ s) P → Γᵉ ∣ (s₀ ++ s) prevalid
                     → P a → P a′
                     → Γᵉ ∣ (s₀ ++ s) ⊢[ P ] a ◁* a′
    push-from-leaves s n la fa d ok pvᵉ pa pa′ =
      ⇛-push (forget n) la (annotate s n la fa d ok pvᵉ pa pa′) pvᵉ
```

## What this establishes

`push-from-leaves`: for any class `𝒫` of side conditions closed under the two wrappers, a promotion
at `Γˢ ∣ s₀` whose two ends satisfy `P` lifts to `Γᵉ ∣ s₀ ++ s` as a chain under `P`, given the
chain from the operand to the bound at each rebound variable (`_▶ᴸ_`) and at each abstraction that
meets an operand (`NewLeaf`). Conjecture 8 is now exactly the existence of those two suppliers for
the class of side conditions "the wrapped term is well-formed".
