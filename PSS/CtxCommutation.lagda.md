# Strong commutation over the context-sensitive equivalence: the new cases

`PSS/CtxSubtyping` rebuilds promotion and subtyping over `⟶≐`. The metatheory's load-bearing
theorem is strong commutation (v1's Theorem 4.5). Since `⟶≐` extends `⟶≡` by exactly one rule —
`Ce-Pro`, which fires only on a variable — the rebuilt commutation proof should be v1's plus the
cases where `Ce-Pro` is the left-hand step. This module settles those cases **at a fixed extended
context**: `Γ`, `s` and `Δ` are the same on both sides of the square, with no context reduction.
Theorem 4.5 proper reduces `Γ` and `s` along `↣`, and its rebuilt form would also have to reduce
`Δ` to keep coherence with the reduced bounds; that version, and the transfer of v1's remaining
cases over `⟶≐`, are owed (`PSS/CtxScope` has the reduction relations but not the theorem).

They do **not** close unconditionally. If `Δ` says `x ≡ α` while `Γ` says `x ≤ t` with `α` and `t`
unrelated, the two edges land in unrelated places and nothing joins them. What is needed is that
the equational context **refines** the subtyping context.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module PSS.CtxCommutation where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.EquivCtx
open import PSS.CtxSubtyping
open import PSS.MinimalUnique using (bound-unique)
```

## Coherence

An equational context refines a subtyping context when every equation it asserts is backed by
the corresponding bound. This is exactly the situation MPSS engineers into its rules, where
`Ms-FOp` records the popped operand as `x ≡ α` and the operand is the bound.

```agda
Coherent : Ctx → EqCtx → Set
Coherent Γ Δ = ∀ {x α} → (x , α) ∈ Δ → x ≤ α ∈ Γ
```

## The new critical pairs

`Ce-Pro` on the left against every promotion on the right.

```agda
ce-pro-commute : ∀ {Γ s Δ x α t₂}
               → Coherent Γ Δ → EqOK Δ
               → (x , α) ∈ Δ → LC α
               → Γ ∣ s ∣ Δ ⊢ fvar x ⟶≤ᶜ t₂
               → ∃[ t₃ ] ((Δ ⊢ t₂ ⟶≐ t₃) × (Γ ∣ s ∣ Δ ⊢ α ⟶≤ᶜ t₃))

-- against Srs-Prom: coherence and uniqueness of bounds make the two targets the same
ce-pro-commute {α = α} {t₂ = t₂} coh ok m lα (Sc-Prom pv m') =
  α , subst (λ z → _ ⊢ t₂ ⟶≐ z) same (⟶≐-refl lt₂) , Sc-Eq pv (⟶≐-refl lα)
  where
    same : t₂ ≡ α
    same = bound-unique pv m' (coh m)
    lt₂ : LC t₂
    lt₂ = subst LC (sym same) lα

-- against Srs-Top: both sides reach Top
ce-pro-commute coh ok m lα (Sc-Top pv) = Top , Ce-Top , Sc-Top pv

-- against an equivalence step: the variable either stays put or unfolds to the same α
ce-pro-commute {α = α} coh ok m lα (Sc-Eq pv Ce-Var) =
  α , Ce-Pro m lα , Sc-Eq pv (⟶≐-refl lα)
ce-pro-commute {α = α} coh ok m lα (Sc-Eq pv (Ce-Pro m' lα'))
  with eq-unique ok m' m
... | refl = α , ⟶≐-refl lα , Sc-Eq pv (⟶≐-refl lα)
```

The `Srs-Prom` case is the one that needs coherence, and it is the case that fails without it:
with `x ≡ α ∈ Δ` and `x ≤ t ∈ Γ` for unrelated `α` and `t`, the left edge lands on `α`, the right
on `t`, and no `t₃` joins them.

## No collapse, even under coherence

The tempting shortcut is that under coherence the rebuilt system might collapse onto λ⊲ — every
`⟶≤ᶜ` step being a `⟶≤` step — so that the whole metatheory transfers with no restatement. It
does not. `Ce-App` can change an *operand* by unfolding it, and no λ⊲ promotion can: `Srs-App`
rewrites only the operator, and `Srs-Eq` would need `⟶≡` to move a variable, which it cannot.

```agda
Γ₃ : Ctx
Γ₃ = (1 , Top) ∷ (0 , Top) ∷ []

Δ₃ : EqCtx
Δ₃ = (1 , Top) ∷ []

coh₃ : Coherent Γ₃ Δ₃
coh₃ (here refl) = here refl

pv₃ : Γ₃ ∣ [] prevalid
pv₃ = P-Ctx2 (P-Ctx2 P-Ctx1 (λ ()) lc-Top (λ ())) 1∉ lc-Top (λ ())
  where
    1∉ : ∀ {A : Set} → 1 ∈ dom ((0 , Top) ∷ []) → A
    1∉ (here ())

steps-ᶜ : Γ₃ ∣ [] ∣ Δ₃ ⊢ app (fvar 0) (fvar 1) ⟶≤ᶜ app (fvar 0) Top
steps-ᶜ = Sc-Eq pv₃ (Ce-App Ce-Var (Ce-Pro (here refl) lc-Top))

no-collapse : ¬ (Γ₃ ∣ [] ⊢ app (fvar 0) (fvar 1) ⟶≤ app (fvar 0) Top)
no-collapse (Srs-Eq _ (Cr-App _ ()))

collapse-is-false :
  ¬ (∀ {Γ s Δ u v} → Coherent Γ Δ → Γ ∣ s ∣ Δ ⊢ u ⟶≤ᶜ v → Γ ∣ s ⊢ u ⟶≤ v)
collapse-is-false collapse = no-collapse (collapse coh₃ steps-ᶜ)
```

## What this establishes

**The `Ce-Pro` critical pairs of strong commutation at a fixed extended context, and the side
condition they need.**

`Ce-Pro` is the only rule `⟶≐` adds and it fires only on a variable, so it forms a critical pair
with nothing except the promotions out of that same variable; those pairs are `ce-pro-commute`.
What is *not* here: context reduction. Theorem 4.5 commutes over `Γ ∣ s ↣ Γ' ∣ s'`, and the
rebuilt theorem must also reduce `Δ`, since coherence between an unreduced `Δ` and a reduced `Γ'`
fails as soon as a bound moves. Nothing in the rebuild has yet been proved with reduced contexts,
so "v1's Theorem 4.5 plus exactly these cases" is the expected shape of the proof, not a
proved statement.

**Coherence is necessary, not decorative.** The `Srs-Prom` case is the whole difficulty: the left
edge unfolds `x` to its equational annotation `α`, the right promotes `x` to its bound `t`, and
unless `Δ` refines `Γ` those are unrelated terms with no join. Under coherence they are the same
term, by uniqueness of bounds in a prevalid context.

That condition is not an artefact of this construction. It is precisely the discipline MPSS builds
into its rules: `Ms-FOp` records the popped operand as `x ≡ α`, and the operand *is* what the
parameter is bounded by. So the design v2 arrived at is what makes a context-sensitive equivalence
commute with promotion — which is a second, independent reason for the change beyond the one the
paper gives.