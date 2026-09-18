# MPSS: the obligation reduced to the two binding rules

`MPSS/Conj8Reduction` rests Conjecture 8 on `StepLift`: one promotion at the empty stack,
between well-formed terms, lifted under one well-formed application. Generalised to a promotion
at any stack `s₀` lifted under any further stack `s` — the terms being the *spines* `a ⋅ s₀ ⋅ s`
— the statement follows its own derivation: `Ms-Pro`, `Ms-Top` and `Ms-Equ` hold at every stack
outright, and `Ms-App` is the same statement one operand deeper. What is left are the two rules
that bind a parameter: `Ms-Fun`, whose parameter the extra stack's first operand is about to be
bound to, and `Ms-FOp`, whose parameter is already bound to an operand and whose body is replayed
under it. Those two, with a non-empty extra stack, are the obligations, and everything else is
proved here.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conj8Push where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Product.Base using (_,_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (subst)

open import MPSS.WellFormed
open import MPSS.StackPush using (pushᵉ)
open import MPSS.Congruence using (refl-head)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Conj8Reduction using (StepLift; conj8)
open import MPSS.Assumed using (Conj-8)
```

## Spines

The stack read as a term: the head of the stack is the innermost operand, as `Ms-App` and
`Me-App` push it.

```agda
spine : Tm → Stack → Tm
spine a []      = a
spine a (v ∷ s) = spine (app a v) s

spine-s : ∀ {Γ s a a'} → Γ ∣ s ⊢ a ⟶ˢ a' → Γ ∣ [] ⊢ spine a s ⟶ˢ spine a' s
spine-s {s = []}    d = d
spine-s {s = v ∷ s} d = spine-s {s = s} (Ms-App d)

spine-e : ∀ {Γ s a a'} → Γ ∣ s ⊢ a ⟶ᵉ a' → Γ ∣ [] ⊢ spine a s ⟶ᵉ spine a' s
spine-e {s = []}    d = d
spine-e {s = v ∷ s} d = spine-e {s = s} (Me-App d (refl-head (⟶ᵉ-prevalid d)))
```

## The general statement and the two obligations

```agda
Push : Set
Push = ∀ {Γ s₀ s a a'}
     → Γ ∣ s₀ ⊢ a ⟶ˢ a'
     → Γ ∣ (s₀ ++ s) prevalid
     → Γ ⊢ spine a (s₀ ++ s) wf → Γ ⊢ spine a' (s₀ ++ s) wf
     → Γ ⊢ spine a (s₀ ++ s) ⊑*wf[ sub-m ] spine a' (s₀ ++ s)

FunLift : Set
FunLift = ∀ {Γ t u u' v s} (L : List Name)
        → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶ˢ (u' ^ fvar x))
        → Γ ∣ (v ∷ s) prevalid
        → Γ ⊢ spine (lam t u) (v ∷ s) wf → Γ ⊢ spine (lam t u') (v ∷ s) wf
        → Γ ⊢ spine (lam t u) (v ∷ s) ⊑*wf[ sub-m ] spine (lam t u') (v ∷ s)

FOpLift : Set
FOpLift = ∀ {Γ α s₀ t u u' v s} (L : List Name)
        → (∀ {x} → x ∉ L → ((x , eqv , α) ∷ Γ) ∣ s₀ ⊢ (u ^ fvar x) ⟶ˢ (u' ^ fvar x))
        → Γ ∣ (α ∷ s₀ ++ v ∷ s) prevalid
        → Γ ⊢ spine (lam t u) (α ∷ s₀ ++ v ∷ s) wf → Γ ⊢ spine (lam t u') (α ∷ s₀ ++ v ∷ s) wf
        → Γ ⊢ spine (lam t u) (α ∷ s₀ ++ v ∷ s) ⊑*wf[ sub-m ] spine (lam t u') (α ∷ s₀ ++ v ∷ s)
```

## The push

A single step on the spines, wrapped as one well-subtyping layer, for the rules that hold at
every stack; the same statement one operand deeper for `Ms-App`; the step itself when there is
no extra stack; and the obligations otherwise.

```agda
module _ (fun : FunLift) (fop : FOpLift) where

  one : ∀ {Γ a a' s} → Γ ∣ s ⊢ a ⟶ˢ a'
      → Γ ⊢ spine a s wf → Γ ⊢ spine a' s wf
      → Γ ⊢ spine a s ⊑*wf[ sub-m ] spine a' s
  one d wa wa' = Ws-Sub wa (Ws-Lf2 wa (spine-s d) wa' (Ws-Rfl (wf⇒prevalid wa))) wa'

  push : Push
  push (Ms-Pro _ m)   pv wa wa' = one (Ms-Pro pv m) wa wa'
  push (Ms-Top _)     pv wa wa' = one (Ms-Top pv) wa wa'
  push (Ms-Equ _ e)   pv wa wa' =
    Ws-Sub wa (Ws-Lf1 (spine-e (pushᵉ e pv)) (Ws-Rfl (wf⇒prevalid wa))) wa'
  push (Ms-App d)     pv wa wa' =
    push d (Pv-Sta pv (prevalid-head-lc pv₀) (prevalid-head-fv pv₀)) wa wa'
    where pv₀ = ⟶ˢ-prevalid d
  push {s = []}    (Ms-Fun L F) pv wa wa' = one (Ms-Fun L F) wa wa'
  push {s = v ∷ s} (Ms-Fun L F) pv wa wa' = fun L F pv wa wa'
  push {s = []}    (Ms-FOp L F) pv wa wa' = one′ (Ms-FOp L F) pv wa wa'
    where
      one′ : ∀ {Γ a a' s₀} → Γ ∣ s₀ ⊢ a ⟶ˢ a'
           → Γ ∣ (s₀ ++ []) prevalid
           → Γ ⊢ spine a (s₀ ++ []) wf → Γ ⊢ spine a' (s₀ ++ []) wf
           → Γ ⊢ spine a (s₀ ++ []) ⊑*wf[ sub-m ] spine a' (s₀ ++ [])
      one′ {s₀ = s₀} d pv′ w w′ rewrite ++-identityʳ s₀ = one d w w′
  push {s = v ∷ s} (Ms-FOp L F) pv wa wa' = fop L F pv wa wa'

  steplift : StepLift
  steplift {v = v} wa d wa' wav wa'v = push {s₀ = []} {s = v ∷ []} d (wf⇒prevalidˢ wav) wav wa'v
    where
      wf⇒prevalidˢ : ∀ {Γ f v} → Γ ⊢ app f v wf → Γ ∣ (v ∷ []) prevalid
      wf⇒prevalidˢ (Wf-App d₁ d₂) =
        Pv-Sta (Pv-Nil (wf⇒prevalid (⊑*wf⇒wfˡ d₂))) (wf⇒lc (⊑*wf⇒wfˡ d₂)) (wf-fv (⊑*wf⇒wfˡ d₂))


  conj8-from-lifts : Conj-8
  conj8-from-lifts = conj8 steplift
```

## What this establishes

`conj8-from-lifts : FunLift → FOpLift → Conj-8`. Conjecture 8 — and type safety with it —
rests on the two binding rules: a promotion under `λx≤t` replayed when the parameter is about to
meet an operand, and one under a parameter already bound to an operand replayed with more stack.
Both are the situation `MPSS/CONJ8.md` §3 isolates, in which the parameter's own promotion
becomes the conjecture again for the pair (operand, annotation) inside the body — the recursion
whose measure is the open question.
