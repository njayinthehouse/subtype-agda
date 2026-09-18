# MPSS: the push theorem with the well-formedness side condition

`MPSS/Push` replays a promotion derivation taken at `Γˢ ∣ s₀` as a chain of promotions at
`Γᵉ ∣ s₀ ++ s`, where `Γᵉ` narrows some entries `x ≤ w` of `Γˢ` to `x ≡ α` — the machine's own
reading of an abstraction that meets an operand (`Ms-FOp` binds `x ≡ α`, where `Ms-Fun` had
`x ≤ t`). Its chains are bare `⟶ˢ*`, and its datum at a narrowed variable is reachability at
*every* stack, which `MPSS/ReachFails` shows is too much to ask.

This module is the same theorem one level up, for the chains Conjecture 8 is about. The result is
a well-subtyping chain at a stack, `Γᵉ ∣ s₀ ++ s ⊢[ P ] a ◁* a′` of `MPSS/Frame`, whose side
condition `P` is a parameter; under an application it becomes `App P v`, under a binder
`Fun P t x` (`MPSS/Wrap`), so that at the top `P` can be well-formedness of the whole applied
term. And the datum at a narrowed variable `x ≡ α`, promoted to its old bound `t`, is one chain
`α ◁* t` **at that stack, under that side condition** — Conjecture 8 for the pair `(α, t)` and
the spine in force, nothing stack-polymorphic.

It is `MPSS/CONJ8.md` §9's `push`, mechanized: everything in the recursion of Conjecture 8 that
is structural in the promotion's derivation. What is left outside is the supply of the chains at
the narrowed variables, which is where the domain order on bounds comes in.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.PushWf where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import MPSS.WellFormed
open import MPSS.StackPush using (pushᵉ; prevalid-cons; ⟶ᵉ-refl)
open import MPSS.Scope using (⟶ˢ-lc)
open import MPSS.Frame
  using (_∣_⊢[_]_◁*_; App; ◁*-app; ◁*-lf1; step-◁*; estep-◁*)
open import MPSS.Wrap using (Fun; ◁*-fun; ◁*-fop)
open import MPSS.Push using (_▶_; m-keep; m-eqv; ▶-dom; ⟶ᵉ-▶)
open import PSS.Syntax using (∉-++ˡ; ∉-++ʳ; fresh; fresh-∉)
```

## The annotated derivation

A `⟶ˢ` derivation at `Γˢ ∣ s₀`, read against the narrowed context `Γᵉ`, the extra stack `s` and
the side condition `P`. Each leaf carries the side condition at its two ends; the leaf at a
narrowed variable carries the chain from the operand to the old bound instead of the second.

```agda
infix 3 _∣_∣_∣_⊢[_]_⇛_
data _∣_∣_∣_⊢[_]_⇛_ : Ctx → Ctx → Stack → Stack → (Tm → Set) → Tm → Tm → Set₁ where

  q-pro : ∀ {Γˢ Γᵉ s₀ s P x t}
        → Γˢ ∣ s₀ prevalid → x ≤ t ∈ Γˢ → x ≤ t ∈ Γᵉ
        → P (fvar x) → P t
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] fvar x ⇛ t

  q-pro-eqv : ∀ {Γˢ Γᵉ s₀ s P x t α}
        → Γˢ ∣ s₀ prevalid → x ≤ t ∈ Γˢ
        → x ≐ α ∈ Γᵉ → LC α → fv α ⊑ dom Γᵉ
        → P (fvar x)
        → Γᵉ ∣ (s₀ ++ s) ⊢[ P ] α ◁* t
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] fvar x ⇛ t

  q-top : ∀ {Γˢ Γᵉ s₀ s P u}
        → Γˢ ∣ s₀ prevalid
        → P u → P Top
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] u ⇛ Top

  q-equ : ∀ {Γˢ Γᵉ s₀ s P u v}
        → Γˢ ∣ s₀ prevalid → Γˢ ∣ s₀ ⊢ u ⟶ᵉ v
        → P u → P v
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] u ⇛ v

  q-app : ∀ {Γˢ Γᵉ s₀ s P u u′ v}
        → Γˢ ∣ Γᵉ ∣ (v ∷ s₀) ∣ s ⊢[ App P v ] u ⇛ u′
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] app u v ⇛ app u′ v

  q-fop : ∀ {Γˢ Γᵉ s₀ s P α t u u′} (L : List Name)
        → fv t ⊑ dom Γᵉ
        → (∀ {x} → x ∉ L
             → ((x , eqv , α) ∷ Γˢ) ∣ ((x , eqv , α) ∷ Γᵉ) ∣ s₀ ∣ s
                 ⊢[ Fun P t x ] (u ^ fvar x) ⇛ (u′ ^ fvar x))
        → Γˢ ∣ Γᵉ ∣ (α ∷ s₀) ∣ s ⊢[ P ] lam t u ⇛ lam t u′

  q-fun-nil : ∀ {Γˢ Γᵉ P t u u′} (L : List Name)
        → (∀ {x} → x ∉ L
             → ((x , sub , t) ∷ Γˢ) ∣ ((x , sub , t) ∷ Γᵉ) ∣ [] ∣ []
                 ⊢[ Fun P t x ] (u ^ fvar x) ⇛ (u′ ^ fvar x))
        → Γˢ ∣ Γᵉ ∣ [] ∣ [] ⊢[ P ] lam t u ⇛ lam t u′

  q-fun-cons : ∀ {Γˢ Γᵉ α s P t u u′} (L : List Name)
        → LC α → fv α ⊑ dom Γᵉ → fv t ⊑ dom Γᵉ
        → (∀ {x} → x ∉ L
             → ((x , sub , t) ∷ Γˢ) ∣ ((x , eqv , α) ∷ Γᵉ) ∣ [] ∣ s
                 ⊢[ Fun P t x ] (u ^ fvar x) ⇛ (u′ ^ fvar x))
        → Γˢ ∣ Γᵉ ∣ [] ∣ (α ∷ s) ⊢[ P ] lam t u ⇛ lam t u′
```

It is a `⟶ˢ` derivation at the source configuration.

```agda
⇛⇒⟶ˢ : ∀ {Γˢ Γᵉ s₀ s P a a′} → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] a ⇛ a′ → Γˢ ∣ s₀ ⊢ a ⟶ˢ a′
⇛⇒⟶ˢ (q-pro pv m _ _ _)               = Ms-Pro pv m
⇛⇒⟶ˢ (q-pro-eqv pv m _ _ _ _ _)       = Ms-Pro pv m
⇛⇒⟶ˢ (q-top pv _ _)                   = Ms-Top pv
⇛⇒⟶ˢ (q-equ pv e _ _)                 = Ms-Equ pv e
⇛⇒⟶ˢ (q-app d)                        = Ms-App (⇛⇒⟶ˢ d)
⇛⇒⟶ˢ (q-fop {u′ = u′} L _ F)          = Ms-FOp {u' = u′} L (λ x∉ → ⇛⇒⟶ˢ (F x∉))
⇛⇒⟶ˢ (q-fun-nil {u′ = u′} L F)        = Ms-Fun {u' = u′} L (λ x∉ → ⇛⇒⟶ˢ (F x∉))
⇛⇒⟶ˢ (q-fun-cons {u′ = u′} L _ _ _ F) = Ms-Fun {u' = u′} L (λ x∉ → ⇛⇒⟶ˢ (F x∉))
```

## The push

```agda
⇛-push : ∀ {Γˢ Γᵉ s₀ s P a a′}
       → Γˢ ▶ Γᵉ → LC a
       → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢[ P ] a ⇛ a′
       → Γᵉ ∣ (s₀ ++ s) prevalid
       → Γᵉ ∣ (s₀ ++ s) ⊢[ P ] a ◁* a′

⇛-push n la (q-pro _ _ k p p′) pv = step-◁* p (Ms-Pro pv k) p′

⇛-push n la (q-pro-eqv _ _ k lα fα p R) pv =
  ◁*-lf1 (Me-Pro pv k (⟶ᵉ-refl pv lα fα)) R p

⇛-push n la (q-top _ p p′)   pv = step-◁* p (Ms-Top pv) p′
⇛-push n la (q-equ _ e p p′) pv = estep-◁* p (pushᵉ (⟶ᵉ-▶ n e) pv) p′

⇛-push n (lc-app lu lv) (q-app d) pv =
  ◁*-app (⇛-push n lu d
            (Pv-Sta pv (prevalid-head-lc pv₀)
                       (λ h → subst (_ ∈_) (▶-dom n) (prevalid-head-fv pv₀ h))))
  where pv₀ = ⟶ˢ-prevalid (⇛⇒⟶ˢ d)

⇛-push {Γᵉ = Γᵉ} {s = s} {P = P} n (lc-lam L₀ lt F₀)
       (q-fop {s₀ = s₀} {α = α} {t = t} {u = u} {u′ = u′} L ft F) pv =
  ◁*-fop x x∉Γ x∉s lt ft x∉u x∉u′ (F₀ x∉L₀) (⟶ˢ-lc (F₀ x∉L₀) (⇛⇒⟶ˢ (F x∉L))) inner
  where
    A   = L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′ ++ fvStack (s₀ ++ s)
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L r₁
    r₃  = ∉-++ʳ (dom Γᵉ) r₂
    r₄  = ∉-++ʳ (fv u) r₃
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉Γ : x ∉ dom Γᵉ
    x∉Γ  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ˡ r₄
    x∉s : x ∉ fvStack (s₀ ++ s)
    x∉s  = ∉-++ʳ (fv u′) r₄

    inner : ((x , eqv , α) ∷ Γᵉ) ∣ (s₀ ++ s) ⊢[ Fun P t x ] (u ^ fvar x) ◁* (u′ ^ fvar x)
    inner = ⇛-push (m-keep n) (F₀ x∉L₀) (F x∉L)
                   (prevalid-cons (prevalid-pop pv) x∉Γ
                                  (prevalid-head-lc pv) (prevalid-head-fv pv))

⇛-push {Γᵉ = Γᵉ} {P = P} n (lc-lam L₀ lt F₀) (q-fun-nil {t = t} {u = u} {u′ = u′} L F) pv =
  ◁*-fun x x∉Γ x∉u x∉u′ (F₀ x∉L₀) (⟶ˢ-lc (F₀ x∉L₀) (⇛⇒⟶ˢ (F x∉L))) inner
  where
    A   = L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L r₁
    r₃  = ∉-++ʳ (dom Γᵉ) r₂
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉Γ : x ∉ dom Γᵉ
    x∉Γ  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ (fv u) r₃

    ctxˢ = prevalid-ctx (⟶ˢ-prevalid (⇛⇒⟶ˢ (F x∉L)))

    fvt : fv t ⊑ dom Γᵉ
    fvt h = subst (_ ∈_) (▶-dom n) (head-fv ctxˢ h)

    inner : ((x , sub , t) ∷ Γᵉ) ∣ [] ⊢[ Fun P t x ] (u ^ fvar x) ◁* (u′ ^ fvar x)
    inner = ⇛-push (m-keep n) (F₀ x∉L₀) (F x∉L)
                   (Pv-Nil (Pv-Ctx (prevalid-ctx pv) x∉Γ (head-lc ctxˢ) fvt))

⇛-push {Γᵉ = Γᵉ} {P = P} n (lc-lam L₀ lt F₀)
       (q-fun-cons {α = α} {s = s} {t = t} {u = u} {u′ = u′} L lα fα ft F) pv =
  ◁*-fop x x∉Γ x∉s lt ft x∉u x∉u′ (F₀ x∉L₀) (⟶ˢ-lc (F₀ x∉L₀) (⇛⇒⟶ˢ (F x∉L))) inner
  where
    A   = L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′ ++ fvStack s
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L r₁
    r₃  = ∉-++ʳ (dom Γᵉ) r₂
    r₄  = ∉-++ʳ (fv u) r₃
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉Γ : x ∉ dom Γᵉ
    x∉Γ  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ˡ r₄
    x∉s : x ∉ fvStack s
    x∉s  = ∉-++ʳ (fv u′) r₄

    inner : ((x , eqv , α) ∷ Γᵉ) ∣ s ⊢[ Fun P t x ] (u ^ fvar x) ◁* (u′ ^ fvar x)
    inner = ⇛-push (m-eqv n lα fα) (F₀ x∉L₀) (F x∉L)
                   (prevalid-cons (prevalid-pop pv) x∉Γ
                                  (prevalid-head-lc pv) (prevalid-head-fv pv))
```

## What this establishes

`⇛-push`: a promotion derivation at `Γˢ ∣ s₀`, annotated with the side condition at its leaves
and, at each variable the narrowing `Γˢ ▶ Γᵉ` rebinds, with the chain from the operand to the old
bound at the stack in force, replays at `Γᵉ ∣ s₀ ++ s` as a well-subtyping chain under that side
condition. The three binder cases and the application case are structural; an abstraction that
meets an operand (`q-fun-cons`) narrows its parameter and goes on. No rank, no measure: those are
needed only to *supply* the chains at the narrowed leaves.
