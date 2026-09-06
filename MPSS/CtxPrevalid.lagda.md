# MPSS: a reduced extended context is prevalid

`MPSS/CtxReduce` proves that `↣` preserves prevalidity of the *logical* context (`↣-ctx`) and
stops short of the extended one, recording why: `Ct-Ann` reduces the stack at the tail context,
so a stack entry mentioning the head variable is reduced where that variable is unbound, and the
projection v1 used does not go through. `MPSS/Commutation` takes the extended statement as the
hypothesis `↣-Prevalid`.

The statement is nonetheless true, and the proof is short once the scoping target is separated
from the reducing context. A reduct's free variables lie in any set containing the source's free
variables and the reducing context's domain (`fv-⟶ᵉ`, with an arbitrary `N`). Along a `↣`
derivation the reducing context only shrinks, so the domain of the *original* full context is
such a set at every step, and it equals the domain of the reduced full context (`↣-dom`). That
the head variable is unbound where its stack entries are reduced does not matter: it is still in
`N`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CtxPrevalid where

open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-ctx)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ)
```

## Stacks scoped in a fixed set

```agda
StackOK : List Name → Stack → Set
StackOK N []      = ⊤
StackOK N (α ∷ s) = (LC α × fv α ⊑ N) × StackOK N s

stack-ok : ∀ {Γ s} → Γ ∣ s prevalid → StackOK (dom Γ) s
stack-ok (Pv-Nil _)         = tt
stack-ok (Pv-Sta pv lα fα)  = (lα , fα) , stack-ok pv

ok-stack : ∀ {Γ s} → Γ prevalid → StackOK (dom Γ) s → Γ ∣ s prevalid
ok-stack {s = []}    pv _                 = Pv-Nil pv
ok-stack {s = α ∷ s} pv ((lα , fα) , ok)  = Pv-Sta (ok-stack pv ok) lα fα

ok-⊑ : ∀ {N N′ s} → N ⊑ N′ → StackOK N s → StackOK N′ s
ok-⊑ {s = []}    inc _                = tt
ok-⊑ {s = α ∷ s} inc ((lα , fα) , ok) = (lα , (λ h → inc (fα h))) , ok-⊑ inc ok
```

## The stack along a reduction

```agda
↣-stack : ∀ {Γ s Γ' s' N} → dom Γ ⊑ N → Γ ∣ s ↣ Γ' ∣ s' → StackOK N s → StackOK N s'
↣-stack dn Ct-Refl      ok = ok
↣-stack dn (Ct-Ann d e) ok = ↣-stack (λ h → dn (there h)) d ok
↣-stack dn (Ct-Stk d e) ((lα , fα) , ok) =
  (⟶ᵉ-lc lα e , fv-⟶ᵉ dn e fα) , ↣-stack dn d ok
```

## The lemma

```agda
↣-prevalid : ∀ {Γ s Γ' s'} → Γ ∣ s prevalid → Γ ∣ s ↣ Γ' ∣ s' → Γ' ∣ s' prevalid
↣-prevalid {Γ} {s} {Γ'} {s'} pv c =
  ok-stack (↣-ctx c (prevalid-ctx pv))
           (ok-⊑ (λ h → subst (_ ∈_) (↣-dom c) h)
                 (↣-stack (λ h → h) c (stack-ok pv)))
```

## What this establishes

`↣-prevalid`: the hypothesis `↣-Prevalid` of `MPSS/Commutation` is a theorem. The note in
`MPSS/CtxReduce` is correct that stack entries are reduced at a context that may not bind the
variables they mention; it does not follow that scoping is lost, because scoping is a statement
about a set of names and the set can be fixed in advance. What `↣` restricts, if anything, is
which *reductions* of such an entry are available, not whether the result is prevalid.
