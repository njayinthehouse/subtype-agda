# System λ⊲: well-formedness and well-subtyping

The rest of Figure 1 — `Γ ∣ s ⊢ t wf`, well-subtyping `≤wf`, and transitive well-subtyping
`≤*wf`.

Well-formedness is λ⊲'s **safety condition**: a well-formed term never gets stuck. Every
application `u v` inside it is well-typed in the sense that `u` is a subtype of some function
`λx≤t.Top` and `v` is a subtype of that function's bound. Unlike prevalidity it is *not*
preserved by reduction — which is exactly why the two are separate judgements.

The three relations are mutually inductive: `wf` appeals to `≤*wf` in `W-App`, and `≤wf`
appeals back to `wf` in `Wf-Rule`. They also depend on `≤` from `PSS.Subtyping`, which is
self-contained.

```agda
{-# OPTIONS --safe #-}

module PSS.WellFormed where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
```

## The three judgements

`W-Var` requires the variable's bound to itself be well-formed in the same extended context —
a genuine recursive appeal, not a structural one, so this is an inductively generated relation
rather than a recursive function.

`W-Fun` and `W-FunOp` split on whether an operand is waiting. `W-FunOp` binds the formal
parameter to the operand `δ` from the stack, matching `Srs-FunOp`; `W-Fun` binds it to the
abstraction's own annotation.

```agda
infix 3 _∣_⊢_wf _∣_⊢_≤wf_ _∣_⊢_≤*wf_

data _∣_⊢_wf    : Ctx → Stack → Tm → Set
data _∣_⊢_≤wf_  : Ctx → Stack → Tm → Tm → Set
data _∣_⊢_≤*wf_ : Ctx → Stack → Tm → Tm → Set

data _∣_⊢_wf where

  W-Var   : ∀ {Γ s x t}
          → Γ ∣ s prevalid
          → x ≤ t ∈ Γ
          → Γ ∣ s ⊢ t wf
          → Γ ∣ s ⊢ fvar x wf

  W-Top   : ∀ {Γ s}
          → Γ ∣ s prevalid
          → Γ ∣ s ⊢ Top wf

  W-Fun   : ∀ {Γ t u} (L : List Name)
          → (∀ {x} → x ∉ L → ((x , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) wf)
          → Γ ∣ [] ⊢ t wf
          → Γ ∣ [] ⊢ lam t u wf

  W-FunOp : ∀ {Γ s δ t u} (L : List Name)
          → (∀ {x} → x ∉ L → ((x , δ) ∷ Γ) ∣ s ⊢ (u ^ fvar x) wf)
          → Γ ∣ [] ⊢ t wf
          → Γ ∣ (δ ∷ s) ⊢ lam t u wf

  W-App   : ∀ {Γ s u v t}
          → Γ ∣ (v ∷ s) ⊢ u ≤*wf lam t Top
          → Γ ∣ [] ⊢ v ≤*wf t
          → Γ ∣ s ⊢ app u v wf

data _∣_⊢_≤wf_ where

  Wf-Rule : ∀ {Γ s u t}
          → Γ ∣ s ⊢ u wf
          → Γ ∣ s ⊢ t wf
          → Γ ∣ s ⊢ u ≤ t
          → Γ ∣ s ⊢ u ≤wf t

data _∣_⊢_≤*wf_ where

  Wf-Sub   : ∀ {Γ s v t}
           → Γ ∣ s ⊢ v ≤wf t
           → Γ ∣ s ⊢ v ≤*wf t

  Wf-Trans : ∀ {Γ s v u t}
           → Γ ∣ s ⊢ v ≤*wf u
           → Γ ∣ s ⊢ u ≤*wf t
           → Γ ∣ s ⊢ u wf
           → Γ ∣ s ⊢ v ≤*wf t
```

## Proposition 2.3 — well-subtyping is stronger than subtyping

Forgetting the well-formedness side conditions turns a `≤*wf` derivation into a `⊲*` one. The
converse fails, which is the content of the proposition: `≤*wf` is the stronger relation.

```agda
≤wf⇒⊲ : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤wf t → Γ ∣ s ⊢ v ≤ t
≤wf⇒⊲ (Wf-Rule _ _ d) = d

≤*wf⇒⊲* : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤*wf t → Γ ∣ s ⊢ v ⊲*[ sub ] t
≤*wf⇒⊲* (Wf-Sub d)         = Ast-Sub (≤wf⇒⊲ d)
≤*wf⇒⊲* (Wf-Trans d₁ d₂ _) = Ast-Trans (≤*wf⇒⊲* d₁) (≤*wf⇒⊲* d₂)
```

## Prevalidity is recoverable from well-formedness

Every well-formedness derivation carries a prevalidity derivation for the same extended
context. Used repeatedly downstream, where a rule needs prevalidity and only well-formedness
is to hand.

`W-FunOp` is the case with content. Its premise gives prevalidity of the *extended* context
`(x ≤ δ) ∷ Γ` against the stack `s`, but the goal needs prevalidity of `Γ` against `δ ∷ s` —
so the stack entries must be re-scoped from `x ∷ dom Γ` down to `dom Γ`. That step is sound
only because `x` does not occur in the stack, which is where cofinite quantification earns its
keep: the premise holds for *every* `x ∉ L`, so we may choose one that also avoids the stack.

```agda
fvStack : Stack → List Name
fvStack []       = []
fvStack (α ∷ s)  = fv α ++ fvStack s

⊑-strengthen : ∀ {x xs ys} → x ∉ xs → xs ⊑ (x ∷ ys) → xs ⊑ ys
⊑-strengthen x∉ incl {y} y∈ with incl y∈
... | here refl = ⊥-elim (x∉ y∈)
... | there q   = q

prevalid-strengthen : ∀ {Γ s x δ}
                    → x ∉ fvStack s
                    → ((x , δ) ∷ Γ) ∣ s prevalid
                    → Γ ∣ s prevalid
prevalid-strengthen {s = []}    x∉ (P-Ctx2 p _ _) = p
prevalid-strengthen {s = α ∷ s} x∉ (P-Ctx3 p fvα) =
  P-Ctx3 (prevalid-strengthen (∉-++ʳ (fv α) x∉) p)
         (⊑-strengthen (∉-++ˡ x∉) fvα)

prevalid-bound : ∀ {Γ s x δ} → ((x , δ) ∷ Γ) ∣ s prevalid → fv δ ⊑ dom Γ
prevalid-bound (P-Ctx2 _ _ fvδ) = fvδ
prevalid-bound (P-Ctx3 p _)     = prevalid-bound p

prevalid-pop : ∀ {Γ s v} → Γ ∣ (v ∷ s) prevalid → Γ ∣ s prevalid
prevalid-pop (P-Ctx3 p _) = p

wf⇒prevalid   : ∀ {Γ s t} → Γ ∣ s ⊢ t wf → Γ ∣ s prevalid
≤wf⇒prevalid  : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤wf t → Γ ∣ s prevalid
≤*wf⇒prevalid : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤*wf t → Γ ∣ s prevalid

wf⇒prevalid (W-Var p _ _)  = p
wf⇒prevalid (W-Top p)      = p
wf⇒prevalid (W-Fun L F wt) = wf⇒prevalid wt
wf⇒prevalid (W-App d₁ d₂)  = prevalid-pop (≤*wf⇒prevalid d₁)
wf⇒prevalid (W-FunOp {Γ} {s} {δ} L F wt) =
  P-Ctx3 (prevalid-strengthen x∉stk pv) (prevalid-bound pv)
  where
    x : Name
    x = fresh (L ++ fvStack s)

    x∉L : x ∉ L
    x∉L = ∉-++ˡ (fresh-∉ (L ++ fvStack s))

    x∉stk : x ∉ fvStack s
    x∉stk = ∉-++ʳ L (fresh-∉ (L ++ fvStack s))

    pv : ((x , δ) ∷ Γ) ∣ s prevalid
    pv = wf⇒prevalid (F x∉L)

≤wf⇒prevalid  (Wf-Rule w _ _)  = wf⇒prevalid w
≤*wf⇒prevalid (Wf-Sub d)       = ≤wf⇒prevalid d
≤*wf⇒prevalid (Wf-Trans d _ _) = ≤*wf⇒prevalid d
```

## What this establishes

Figure 1 in full. Together with `PSS.Reduction` and `PSS.Subtyping`, the whole of Figures 1–3
is now mechanized.

**Next** (`PSS/Metatheory`): §4's theorems, in dependency order — 4.5, then 4.4, then 4.3, then
4.1 and 4.2.
