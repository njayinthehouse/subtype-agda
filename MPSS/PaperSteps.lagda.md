# MPSS: the paper's steps, transcribed

Each entry below takes one step of a printed proof, writes it in Agda as the paper writes it, and
puts our own version of the same step beside it. Ours typecheck. The paper's are commented out —
a `--safe` module cannot contain a failure — with the error Agda actually gave, recorded verbatim
from a run.

That is the point of the exercise: an error message names the mismatch more precisely than prose
can, and it is checkable rather than asserted.

```agda
{-# OPTIONS --safe #-}

module MPSS.PaperSteps where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.WellFormed
open import MPSS.Rename using (substCtx)
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Subst28 using (Lem-28-ctx)
open import MPSS.Assumed using (Prop-17ʳ)

open import PSS.Reduction using (_↦_)
```

## Proposition 27 — `Ws-Lf1` where `Ws-Rgh` is meant

> By rule `Ws-Rfl` and `Ws-Lf1`, we have `Γ ⊢ u′ ≤wf u`.

```agda
-- paper-27 : ∀ {Γ u u'} → Γ prevalid → Γ ∣ [] ⊢ u ⟶ᵉ u' → Γ ⊢ u' ⊑wf[ sub-m ] u
-- paper-27 pv e = Ws-Lf1 e (Ws-Rfl pv)
--
--   error: [UnequalTerms]
--   u != u' of type Tm
--   when checking that the expression e has type Γ ∣ [] ⊢ u' ⟶ᵉ _v'_11

ours-27 : ∀ {Γ u u'} → Γ prevalid → Γ ∣ [] ⊢ u ⟶ᵉ u' → Γ ⊢ u' ⊑wf[ sub-m ] u
ours-27 pv e = Ws-Rgh (Ws-Rfl pv) e
```

`Ws-Lf1` moves the left-hand side, so it wants the step to start at `u′`. `Ws-Rgh` moves the
right, which is the side the conclusion actually moves.

## Lemma 9 — a rule that does not exist

> Hence, by rule `Ws-Lft`, …

```agda
-- paper-9 : ∀ {Γ v v' t} → Γ ⊢ v wf → Γ ∣ [] ⊢ v ⟶ˢ v' → Γ ⊢ v' ⊑wf[ sub-m ] t
--         → Γ ⊢ v ⊑wf[ sub-m ] t
-- paper-9 w st d = Ws-Lft st d
--
--   error: [NotInScope]
--   Not in scope: Ws-Lft   (did you mean '_⊢_⊑wf[_]_.Ws-Lf1' …)

ours-9 : ∀ {Γ v v' t} → Γ ⊢ v wf → Γ ∣ [] ⊢ v ⟶ˢ v' → Γ ⊢ v' wf → Γ ⊢ v' ⊑wf[ sub-m ] t
       → Γ ⊢ v ⊑wf[ sub-m ] t
ours-9 w st w' d = Ws-Lf2 w st w' d
```

The step carries a promotion, so the rule is `Ws-Lf2` — which also wants both sides well-formed,
premises the lemma already has and the paper attaches to the following `Ws-Sub` instead.

## Proposition 18 — the operator premise sits at the pushed stack

> at the rest of the nodes only rules `Me-App`, `Me-Fun`, and `Me-FOp` occur

```agda
-- paper-18 : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ u → Γ ∣ [] ⊢ v ⟶ᵉ v → Γ ∣ s ⊢ app u v ⟶ᵉ app u v
-- paper-18 du dv = Me-App du dv
--
--   error: [UnequalTerms]
--   s != (v ∷ s) of type (List Tm)
--   when checking that the expression du has type Γ ∣ v ∷ s ⊢ u ⟶ᵉ u

ours-18 : ∀ {Γ s u v} → Γ ∣ (v ∷ s) ⊢ u ⟶ᵉ u → Γ ∣ [] ⊢ v ⟶ᵉ v → Γ ∣ s ⊢ app u v ⟶ᵉ app u v
ours-18 du dv = Me-App du dv
```

Naming the rule is not enough: `Me-App` takes its operator premise one stack entry deeper, and
every leaf under it carries `Γ ∣ v :: s prevalid`, which `Pv-Sta` grants only when `v` is scoped.
Recovering the premise is the whole content of `⟶ᵉ-refl`, and it needs the scoping hypothesis the
proposition omits.

## Theorem 5 — an operational step is not an equivalence step

> hence `Γ ⊢ t′ ≤*wf t` by rule `Ws-Rgh`

```agda
-- paper-5 : ∀ {Γ t t'} → Γ ⊢ t wf → t ↦ t' → Γ ⊢ t' ⊑wf[ sub-m ] t
-- paper-5 w st = Ws-Rgh (Ws-Rfl (wf⇒prevalid w)) st
--
--   error: [UnequalTerms]
--   (t ↦ t') !=< (Γ ∣ [] ⊢ t ⟶ᵉ t')
--   when checking that the expression st has type Γ ∣ [] ⊢ t ⟶ᵉ t'

ours-5 : Prop-17ʳ → ∀ {Γ t t'} → Γ ⊢ t wf → fv t ⊑ dom Γ → t ↦ t' → Γ ⊢ t' ⊑wf[ sub-m ] t
ours-5 prop-17 w ft st =
  Ws-Rgh (Ws-Rfl (wf⇒prevalid w))
         (prop-17 (Pv-Nil (wf⇒prevalid w)) (wf⇒lc w) ft st)
```

The error is the missing citation, spelled out by the typechecker: bridging `↦` and `⟶≡` is
Proposition 17, which the proof of Theorem 5 never mentions — and which is refuted.

## Lemma 7 — Lemma 28 does not substitute what Lemma 7 needs

> we establish that `Γ, Γ′[x\α]` is prevalid by Lemma 28

```agda
Lem-28-as-printed : Set
Lem-28-as-printed = ∀ (Δ : Ctx) {Γ x c t}
                  → (Δ ++ (x , c , t) ∷ Γ) prevalid
                  → (substCtx x t Δ ++ Γ) prevalid

-- paper-7 : Lem-28-as-printed
--         → ∀ (Δ : Ctx) {Γ x c t α}
--         → (Δ ++ (x , c , t) ∷ Γ) prevalid → (substCtx x α Δ ++ Γ) prevalid
-- paper-7 l28 Δ pv = l28 Δ pv
--
--   error: [UnequalTerms]
--   t != α of type Tm
--   when checking that the expression pv has type Δ ++ (x , c , α) ∷ Γ prevalid

ours-7 : ∀ (Δ : Ctx) {Γ x c t α}
       → LC α → fv α ⊑ dom Γ
       → (Δ ++ (x , c , t) ∷ Γ) prevalid → (substCtx x α Δ ++ Γ) prevalid
ours-7 Δ lα fα pv = Lem-28-ctx Δ lα fα pv
```

The printed lemma substitutes the annotation and only the annotation. The general form is true
given `α` locally closed and scoped, both of which `Γ ⊢ α ≤*wf t` supplies — so the citation is
repairable, but not as it stands.

## Lemma 24 — well-formedness is not a structural property

> Case `v′ = x`: A variable is well-formed by rule `Wf-PrS` or `Wf-PrE`.

```agda
-- paper-24 : ∀ {Γ x} → Γ prevalid → Γ ⊢ fvar x wf
-- paper-24 pv = Wf-PrS pv (here refl)
--
--   error: [UnequalTerms]
--   _x_9 ∷ _xs_10 != Γ of type List …

ours-24 : ∀ {Γ x t} → Γ prevalid → x ≤ t ∈ Γ → Γ ⊢ fvar x wf
ours-24 pv m = Wf-PrS pv m
```

A variable is well-formed only when the context has an entry for it, and the case gives no
hypothesis relating `v′` to anything. An induction of that shape would prove every term
well-formed, and `Top Top` is not.

## Lemma 33 — which side of `≤` promotes

> we have a term `t` such that `Γ;v::s ⊢ u ⟶≡↠ t` and `Γ;v::s ⊢ u′ ⟶≤↠ t`

```agda
-- paper-33 : ∀ {Γ s v v' t} → Γ ∣ s ⊢ v ⟶ᵉ v' → Γ ∣ s ⊢ v' ⊲[ sub-m ] t → Γ ∣ s ⊢ v ⊲[ sub-m ] t
-- paper-33 e d = As-Left-2 e d
--
--   error: [UnequalTerms]
--   eqv-m != sub-m of type Mode

ours-33 : ∀ {Γ s v v' t} → Γ ∣ s ⊢ v ⟶ˢ v' → Γ ∣ s ⊢ v' ⊲[ sub-m ] t → Γ ∣ s ⊢ v ⊲[ sub-m ] t
ours-33 st d = As-Left-1 st d
```

The mode index catches it: an equivalence step on the left is the *equivalence* reading, and in
the subtyping reading the left side takes a promotion. Both congruences hold, so the lemma stands
and only the attribution is wrong.

## Proposition 17 — the premise `Me-Bet` demands is refutable

> the result holds by rule `Me-Bet` and reflexivity of `⟶≡` (Proposition 18)

Here the rule application is not the problem; supplying its body premise is. `MPSS/BetaScopeWf`
proves the premise *false* at the paper's own base case:

> `body-stuck : ∀ {x w} → x ∉ dom Γ₀ → Γ₀ ∣ [] ⊢ (Body ^ fvar x) ⟶ᵉ w → ⊥`
> `body-stuck x∉ (Me-App d _) with ⟶ᵉ-prevalid d`
> `... | Pv-Sta _ _ f = x∉ (f (here refl))`

Two lines: the body passes the parameter as an operand, so `Me-App`'s own prevalidity at the
pushed stack forces the parameter into `dom Γ₀`, and it is fresh. No reflexivity, repaired or
otherwise, can produce that derivation.

## What this establishes

Nothing new about the system — every claim here is already proved or refuted elsewhere in the
development. What it adds is a check on the *reading*: each error is what Agda says when the
paper's own sentence is written down as it stands.
