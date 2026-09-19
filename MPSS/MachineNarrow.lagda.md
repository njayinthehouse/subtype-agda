# MPSS: the machine relation is preserved when the configuration is reduced

If `Γ ∣ s ⊢ u ≤ t` and `Γ ∣ s ↣ Γ′ ∣ s′`, then `Γ′ ∣ s′ ⊢ u ≤ t`, for locally closed `u` and `t`
with free variables in `dom Γ`; the same for `≋`. In v1 this is `⊲-narrow` of `PSS/Narrowing`,
proved by stripping with strong commutation, and that proof reuses a residual step at the reduced
configuration, which v1 may do because its `⟶≡` does not read the context. MPSS's `⟶ᵉ` reads the
`x ≡ α` entries, so a step made at `Γ ∣ s` is not a step at `Γ′ ∣ s′`.

The proof here works in the variant (`⟶ᵉ′`, `⟶ˢ′`, `↣′`, `⊲′`), where the diamond `Lem-2′` and
the commutation lemma `Lem-1′` are proved with a context reduction on each side. `Lem-2′` with the
same context reduction on both sides and one edge reflexive says that a step `t₀ ⟶ᵉ′ t₁` at
`Γ ∣ s` leaves `t₀` and `t₁` with a common `⟶ᵉ′`-reduct at `Γ′ ∣ s′`. So each step of a derivation
at `Γ ∣ s` gives a derivation at `Γ′ ∣ s′` between the same two terms, and transitivity of `⊲′`
(`⊲′-trans`, from `MPSS/VariantTransitivity`) joins them. An original context reduction is then
cut into a sequence of variant ones, and the result is carried back to `⊲`.

Reflexivity of `⟶ᵉ′` holds for locally closed terms scoped in the context (`⟶ᵉ′-refl`), which is
where the scoping hypotheses on `u` and `t` come from. No well-formedness is assumed.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.MachineNarrow where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-lc; ⟶ᵉ′-refl; ⟶ᵉ′-prevalid; ⟶ᵉ′-weaken)
open import MPSS.VariantChain using (_∣_⊢_⟶ᵉ′*_; ε′; _◅′_)
open import MPSS.VariantCtx
open import MPSS.VariantSub
open import MPSS.VariantMachine
open import MPSS.VariantDiamond using (Lem-2′)
open import MPSS.VariantCommutation using (Lem-1′)
open import MPSS.VariantTransitivity using (⊲′-trans)
open import MPSS.Peel using (⟶ᵉ⊆⟶ᵉ′*)
open import MPSS.Preserve using (fv-⟶ᵉ-dom)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Narrowing24 using (fv-⟶ˢ-dom)
```

## A step at the old configuration, seen from the new one

`Lem-2′` with both context reductions the given one, and the first edge reflexive.

```agda
move : ∀ {Γ s Γ′ s′ t₀ t₁} → LC t₀ → fv t₀ ⊑ dom Γ
     → Γ ∣ s ↣′ Γ′ ∣ s′
     → Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁
     → ∃[ t₃ ] ((Γ′ ∣ s′ ⊢ t₀ ⟶ᵉ′ t₃) × (Γ′ ∣ s′ ⊢ t₁ ⟶ᵉ′ t₃))
move l f c e = Lem-2′ l (⟶ᵉ′-refl (⟶ᵉ′-prevalid e) l f) e c c
```

Two terms with a common `⟶ᵉ′`-reduct are related by `⊲′`, in either mode: the left term steps
(`As-Left-2′`, or `As-Left-1′` through `Ms-Equ′`), the right term steps (`As-Right′`).

```agda
left′ : ∀ {Γ s v v' t} m
      → Γ ∣ s ⊢ v ⟶ᵉ′ v'
      → Γ ∣ s ⊢ v' ⊲′[ m ] t
      → Γ ∣ s ⊢ v ⊲′[ m ] t
left′ sub-m e d = As-Left-1′ (Ms-Equ′ (⟶ᵉ′-prevalid e) e) d
left′ eqv-m e d = As-Left-2′ e d

meet : ∀ {Γ s a b c} m
     → Γ ∣ s ⊢ a ⟶ᵉ′ c
     → Γ ∣ s ⊢ b ⟶ᵉ′ c
     → Γ ∣ s ⊢ a ⊲′[ m ] b
meet m ea eb = left′ m ea (As-Right′ (As-Refl′ (⟶ᵉ′-prevalid ea)) eb)
```

## One variant context reduction

By induction on the derivation. Each rule gives a derivation at the new configuration between the
two terms its step relates, and `⊲′-trans` joins it to the induction hypothesis.

- `As-Left-2′`, `As-Right′`: `move`, then `meet`.
- `As-Left-1′`, with `u ⟶ˢ′ u₂`: `Lem-1′` with its `⟶ᵉ′` edge reflexive gives `u ⟶ˢ′ t₃` at the
  new configuration and `u₂ ⟶ᵉ′ t₃` at the old one; `move` takes the latter to the new
  configuration, where `t₃` and `u₂` then have a common reduct.

```agda
narrow′ : ∀ {Γ s Γ′ s′ u t m} → LC u → LC t → fv u ⊑ dom Γ → fv t ⊑ dom Γ
        → Γ ∣ s ↣′ Γ′ ∣ s′
        → Γ ∣ s ⊢ u ⊲′[ m ] t
        → Γ′ ∣ s′ ⊢ u ⊲′[ m ] t
narrow′ lu lt fu ft c (As-Refl′ pv) = As-Refl′ (↣′-prevalid pv c)
narrow′ lu lt fu ft c (As-Left-1′ {v' = u₂} st d) =
  let pv            = ⟶ˢ′-prevalid st
      lu₂           = ⟶ˢ′-lc lu st
      fu₂           = fv-⟶ˢ-dom (⟶ˢ′⊆⟶ˢ st) fu
      (t₃ , e₂ , st′) = Lem-1′ lu (⟶ᵉ′-refl pv lu fu) st c
      (t₄ , a , b)  = move lu₂ fu₂ c e₂
  in ⊲′-trans Lem-1′ lu₂ (As-Left-1′ st′ (meet sub-m b a)) (narrow′ lu₂ lt fu₂ ft c d)
narrow′ lu lt fu ft c (As-Left-2′ e d) =
  let lu₁          = ⟶ᵉ′-lc lu e
      fu₁          = fv-⟶ᵉ-dom (⟶ᵉ′⊆⟶ᵉ e) fu
      (t₃ , a , b) = move lu fu c e
  in ⊲′-trans Lem-1′ lu₁ (meet eqv-m a b) (narrow′ lu₁ lt fu₁ ft c d)
narrow′ {m = m} lu lt fu ft c (As-Right′ d e) =
  let lt₁          = ⟶ᵉ′-lc lt e
      ft₁          = fv-⟶ᵉ-dom (⟶ᵉ′⊆⟶ᵉ e) ft
      (t₃ , a , b) = move lt ft c e
  in ⊲′-trans Lem-1′ lt₁ (narrow′ lu lt₁ fu ft₁ c d) (meet m b a)
```

## A sequence of variant context reductions

```agda
infixr 5 _◅ᶜ_
infix 3 _∣_↣′*_∣_
data _∣_↣′*_∣_ : Ctx → Stack → Ctx → Stack → Set where
  εᶜ   : ∀ {Γ s} → Γ ∣ s ↣′* Γ ∣ s
  _◅ᶜ_ : ∀ {Γ s Γ₁ s₁ Γ′ s′} → Γ ∣ s ↣′ Γ₁ ∣ s₁ → Γ₁ ∣ s₁ ↣′* Γ′ ∣ s′ → Γ ∣ s ↣′* Γ′ ∣ s′

_++ᶜ_ : ∀ {Γ s Γ₁ s₁ Γ′ s′} → Γ ∣ s ↣′* Γ₁ ∣ s₁ → Γ₁ ∣ s₁ ↣′* Γ′ ∣ s′ → Γ ∣ s ↣′* Γ′ ∣ s′
εᶜ       ++ᶜ q = q
(c ◅ᶜ p) ++ᶜ q = c ◅ᶜ (p ++ᶜ q)

⊑-dom : ∀ {Γ s Γ′ s′} {N : List Name} → Γ ∣ s ↣′ Γ′ ∣ s′ → N ⊑ dom Γ → N ⊑ dom Γ′
⊑-dom {N = N} c f = subst (λ D → N ⊑ D) (↣′-dom c) f

↣′*-prevalid : ∀ {Γ s Γ′ s′} → Γ ∣ s prevalid → Γ ∣ s ↣′* Γ′ ∣ s′ → Γ′ ∣ s′ prevalid
↣′*-prevalid pv εᶜ        = pv
↣′*-prevalid pv (c ◅ᶜ cs) = ↣′*-prevalid (↣′-prevalid pv c) cs

narrow′* : ∀ {Γ s Γ′ s′ u t m} → LC u → LC t → fv u ⊑ dom Γ → fv t ⊑ dom Γ
         → Γ ∣ s ↣′* Γ′ ∣ s′
         → Γ ∣ s ⊢ u ⊲′[ m ] t
         → Γ′ ∣ s′ ⊢ u ⊲′[ m ] t
narrow′* lu lt fu ft εᶜ        d = d
narrow′* lu lt fu ft (c ◅ᶜ cs) d =
  narrow′* lu lt (⊑-dom c fu) (⊑-dom c ft) cs (narrow′ lu lt fu ft c d)
```

## An original context reduction is a sequence of variant ones

`Ct-Ann` and `Ct-Stk` each reduce one entry by a `⟶ᵉ` step, which is a chain of `⟶ᵉ′` steps
(`MPSS/Peel`), and reduce the rest of the configuration at the same time. A variant context
reduction takes one `⟶ᵉ′` step per entry, and the steps of the chain are all at the unreduced
context, so the entry is reduced first, the rest held fixed (`Ct-Refl′`), and then the rest is
reduced, the entry held fixed by a reflexive step. The reflexive step needs the entry scoped in
the context below it.

An annotation is scoped in the context below it by prevalidity. A stack entry is scoped in the
whole context, but `Ct-Stk` under `Ct-Ann` reduces it at a shorter one. So the stack is treated
separately: every stack step is weakened to the whole context, the stack is reduced there with
the context held fixed, and then the annotations are reduced under the reduced stack.

Holding the head fixed:

```agda
lift-ann : ∀ {Γ s Γ′ s′ x c t} → Γ prevalid → LC t → fv t ⊑ dom Γ
         → Γ ∣ s ↣′* Γ′ ∣ s′
         → ((x , c , t) ∷ Γ) ∣ s ↣′* ((x , c , t) ∷ Γ′) ∣ s′
lift-ann pv l f εᶜ        = εᶜ
lift-ann pv l f (c ◅ᶜ cs) =
  Ct-Ann′ c (⟶ᵉ′-refl (Pv-Nil pv) l f) ◅ᶜ lift-ann (↣′-ctx c pv) l (⊑-dom c f) cs

lift-stk : ∀ {Γ s Γ′ s′ α} → Γ prevalid → LC α → fv α ⊑ dom Γ
         → Γ ∣ s ↣′* Γ′ ∣ s′
         → Γ ∣ (α ∷ s) ↣′* Γ′ ∣ (α ∷ s′)
lift-stk pv l f εᶜ        = εᶜ
lift-stk pv l f (c ◅ᶜ cs) =
  Ct-Stk′ c (⟶ᵉ′-refl (Pv-Nil pv) l f) ◅ᶜ lift-stk (↣′-ctx c pv) l (⊑-dom c f) cs
```

Reducing the head along a chain:

```agda
head-ann : ∀ {Γ s x c t t′} → Γ ∣ [] ⊢ t ⟶ᵉ′* t′
         → ((x , c , t) ∷ Γ) ∣ s ↣′* ((x , c , t′) ∷ Γ) ∣ s
head-ann (ε′ _)   = εᶜ
head-ann (e ◅′ p) = Ct-Ann′ Ct-Refl′ e ◅ᶜ head-ann p

head-stk : ∀ {Γ s α α′} → Γ ∣ [] ⊢ α ⟶ᵉ′* α′
         → Γ ∣ (α ∷ s) ↣′* Γ ∣ (α′ ∷ s)
head-stk (ε′ _)   = εᶜ
head-stk (e ◅′ p) = Ct-Stk′ Ct-Refl′ e ◅ᶜ head-stk p
```

The annotations of a context reduction, at the empty stack:

```agda
ann-part : ∀ {Γ s Γ′ s′} → Γ prevalid → Γ ∣ s ↣ Γ′ ∣ s′ → Γ ∣ [] ↣′* Γ′ ∣ []
ann-part pv Ct-Refl      = εᶜ
ann-part pv (Ct-Stk d _) = ann-part pv d
ann-part pv (Ct-Ann d e) =
  head-ann (⟶ᵉ⊆⟶ᵉ′* (head-lc pv) e)
  ++ᶜ lift-ann (tail-prevalid pv)
               (⟶ᵉ-lc (head-lc pv) e)
               (fv-⟶ᵉ-dom e (head-fv pv))
               (ann-part (tail-prevalid pv) d)
```

The stack entries of a context reduction, each step weakened to the whole context:

```agda
infixr 5 _∷ˢ_
data StackSteps (Γ : Ctx) : Stack → Stack → Set where
  []ˢ  : StackSteps Γ [] []
  _∷ˢ_ : ∀ {α α′ s s′} → Γ ∣ [] ⊢ α ⟶ᵉ′* α′ → StackSteps Γ s s′ → StackSteps Γ (α ∷ s) (α′ ∷ s′)

steps-id : ∀ {Γ} → Γ prevalid → (s : Stack) → StackSteps Γ s s
steps-id pv []      = []ˢ
steps-id pv (_ ∷ s) = ε′ (Pv-Nil pv) ∷ˢ steps-id pv s

chain-weaken : ∀ {Γ x c t a b} → ((x , c , t) ∷ Γ) prevalid
             → Γ ∣ [] ⊢ a ⟶ᵉ′* b → ((x , c , t) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ′* b
chain-weaken pv (ε′ _)   = ε′ (Pv-Nil pv)
chain-weaken {x = x} {c} {t} pv (e ◅′ p) =
  ⟶ᵉ′-weaken [] ((x , c , t) ∷ []) (Pv-Nil pv) e ◅′ chain-weaken pv p

steps-weaken : ∀ {Γ x c t s s′} → ((x , c , t) ∷ Γ) prevalid
             → StackSteps Γ s s′ → StackSteps ((x , c , t) ∷ Γ) s s′
steps-weaken pv []ˢ      = []ˢ
steps-weaken pv (p ∷ˢ r) = chain-weaken pv p ∷ˢ steps-weaken pv r

stack-part : ∀ {Γ s Γ′ s′} → Γ prevalid → All LC s → Γ ∣ s ↣ Γ′ ∣ s′ → StackSteps Γ s s′
stack-part {s = s} pv ls Ct-Refl     = steps-id pv s
stack-part pv (l ∷ ls) (Ct-Stk d e)  = ⟶ᵉ⊆⟶ᵉ′* l e ∷ˢ stack-part pv ls d
stack-part pv ls       (Ct-Ann d e)  = steps-weaken pv (stack-part (tail-prevalid pv) ls d)

stack-lc : ∀ {Γ s} → Γ ∣ s prevalid → All LC s
stack-lc (Pv-Nil _)     = []
stack-lc (Pv-Sta pv l _) = l ∷ stack-lc pv
```

Reducing the stack with the context held fixed, and the context under a fixed stack:

```agda
stack-seq : ∀ {Γ s s′} → Γ ∣ s prevalid → StackSteps Γ s s′ → Γ ∣ s ↣′* Γ ∣ s′
stack-seq pv []ˢ = εᶜ
stack-seq (Pv-Sta pv l f) (p ∷ˢ r) =
  lift-stk (prevalid-ctx pv) l f (stack-seq pv r) ++ᶜ head-stk p

under-stack : ∀ {Γ Γ′ s} → Γ ∣ s prevalid → Γ ∣ [] ↣′* Γ′ ∣ [] → Γ ∣ s ↣′* Γ′ ∣ s
under-stack (Pv-Nil _)      cs = cs
under-stack (Pv-Sta pv l f) cs = lift-stk (prevalid-ctx pv) l f (under-stack pv cs)
```

Together:

```agda
↣⊆↣′* : ∀ {Γ s Γ′ s′} → Γ ∣ s prevalid → Γ ∣ s ↣ Γ′ ∣ s′ → Γ ∣ s ↣′* Γ′ ∣ s′
↣⊆↣′* pv c =
  let ss = stack-seq pv (stack-part (prevalid-ctx pv) (stack-lc pv) c)
  in ss ++ᶜ under-stack (↣′*-prevalid pv ss) (ann-part (prevalid-ctx pv) c)
```

## The machine relation under context reduction

Prevalidity of `Γ ∣ s` is read off the derivation (`chain-prevalid`).

```agda
⊲-↣ : ∀ {Γ s Γ′ s′ u t m} → LC u → LC t → fv u ⊑ dom Γ → fv t ⊑ dom Γ
    → Γ ∣ s ↣ Γ′ ∣ s′
    → Γ ∣ s ⊢ u ⊲[ m ] t
    → Γ′ ∣ s′ ⊢ u ⊲[ m ] t
⊲-↣ lu lt fu ft c d =
  ⊲′⊆⊲ (narrow′* lu lt fu ft (↣⊆↣′* (chain-prevalid d) c) (⊲⊆⊲′ lu lt d))

≤-↣ : ∀ {Γ s Γ′ s′ u t} → LC u → LC t → fv u ⊑ dom Γ → fv t ⊑ dom Γ
    → Γ ∣ s ↣ Γ′ ∣ s′
    → Γ ∣ s ⊢ u ≤ t
    → Γ′ ∣ s′ ⊢ u ≤ t
≤-↣ = ⊲-↣

≋-↣ : ∀ {Γ s Γ′ s′ u t} → LC u → LC t → fv u ⊑ dom Γ → fv t ⊑ dom Γ
    → Γ ∣ s ↣ Γ′ ∣ s′
    → Γ ∣ s ⊢ u ≋ t
    → Γ′ ∣ s′ ⊢ u ≋ t
≋-↣ = ⊲-↣
```

## What this establishes

`⊲-↣`: MPSS's machine relation, in both modes, is preserved when the configuration is reduced by
the original `↣`, for locally closed terms scoped in the context. The hypotheses beyond the
statement in v1 are `fv u ⊑ dom Γ` and `fv t ⊑ dom Γ`, needed for reflexivity of `⟶ᵉ′`; no
well-formedness is assumed. `narrow′` and `narrow′*` are the same statement for `⊲′` under one
and under a sequence of variant context reductions, and `↣⊆↣′*` says a context reduction from a
prevalid configuration is a sequence of variant ones.

What is spent: `Lem-2′` (`MPSS/VariantDiamond`), `Lem-1′` (`MPSS/VariantCommutation`), `⊲′-trans`
(`MPSS/VariantTransitivity`), the two inclusions between `⊲` and `⊲′` (`MPSS/VariantMachine`), and
`⟶ᵉ ⊆ ⟶ᵉ′*` (`MPSS/Peel`).
