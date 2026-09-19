# MPSS: Conjecture 8 is false over contexts with well-formed annotations

`MPSS/Conj8Refuted` refutes Conjecture 8 in a prevalid context whose annotation is ill-formed.
`MPSS/WfCtx` restates it with the annotations of the context well-formed (`Conj-8ʷᶜ`). That
statement is false too, in the **empty context**.

The instance (`MPSS/CONJ8.md` §21) is Hurkens' paradox `[L₀ R₀]` of `MPSS/HurkensTerm`:

    u = L₀        t = ¬φ₀ = λ0≤φ₀.⊥        covariant context □ R₀

- `L₀ ≤*wf ¬φ₀`, and `L₀ R₀` and `(¬φ₀) R₀` are well-formed: found by the checker of
  `MPSS/CheckerFns`, run by the type checker, and turned into derivations by `MPSS/CheckerSound`.
- `(¬φ₀) R₀ ⟶ᵉ* ⊥ = λp≤⊤.p`, an abstraction: one head contraction (two `⟶ᵉ` steps).
- No `⟶ᵉ*`-reduct of `L₀ R₀` is an abstraction: it has kind `S` (`MPSS/Kinding`,
  `MPSS/HurkensTerm`).
- So no chain of promotions from `L₀ R₀` ends in an abstraction (`MPSS/PromotionNoWhnf`), and
  `L₀ R₀ ≤*wf (¬φ₀) R₀`, which the conjecture would give, is not derivable
  (`MPSS/Conj8NoAbstraction`: Theorem 3, then confluence).

The conclusion the conjecture would give is the application rule of the source calculus: the
paradox has type `⊥`. MPSS does not derive it, because the only way up from an application of
an abstraction is through its body with the parameter bound by `≡`, where `Ms-Pro` does not
apply, and no reduct of this term is an abstraction (every reduct has kind `S`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conj8WfCtxRefuted where

open import Data.List.Base using ([])
open import Data.Product.Base using (_,_)
open import Relation.Nullary using (¬_)
open import Data.Bool.Base using (true)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.WfCtx using (Conj-8ʷᶜ)
open import MPSS.Conj8NoAbstraction using (Reaches)
open import MPSS.PromotionNoWhnf using (refutes-NR)
open import MPSS.CheckerFns using (wf?; sub?)
open import MPSS.NormalizeSound using (hred-sound)
open import MPSS.CheckerSound using (wf-sound; sub-sound)
open import MPSS.HurkensTerm
open import PSS.Syntax using (Top; bvar; lam)
```

## The static facts, by the checker

The three runs of the checker are `abstract`: what is used of them afterwards is their type, and
nothing should ever unfold them.

```agda
app-wfˡ : ∀ {Γ f v} → Γ ⊢ app f v wf → Γ ⊢ f wf
app-wfˡ (Wf-App d _) = ⊑*wf⇒wfˡ d

app-wfʳ : ∀ {Γ f v} → Γ ⊢ app f v wf → Γ ⊢ v wf
app-wfʳ (Wf-App _ d) = ⊑*wf⇒wfˡ d

abstract
  wf-H : [] ⊢ H wf
  wf-H = wf-sound 200 300 Pv-Emp refl

  wf-H′ : [] ⊢ H′ wf
  wf-H′ = wf-sound 200 300 Pv-Emp refl

wf-L₀ : [] ⊢ L₀ wf
wf-L₀ = app-wfˡ wf-H

wf-R₀ : [] ⊢ R₀ wf
wf-R₀ = app-wfʳ wf-H

wf-¬φ₀ : [] ⊢ ¬φ₀ wf
wf-¬φ₀ = app-wfˡ wf-H′

abstract
  L₀≤¬φ₀ : [] ⊢ L₀ ≤*wf ¬φ₀
  L₀≤¬φ₀ = sub-sound 200 300 {k = true} Pv-Emp (wf⇒lc wf-L₀) (wf-fv wf-L₀) (λ _ → wf-L₀) wf-¬φ₀ wf-L₀
                     (λ l → l) refl
```

## The right side reduces to an abstraction

```agda
H′-reaches : Reaches H′
H′-reaches = Top , bvar 0 , hred-sound H′ {t′ = lam Top (bvar 0)} (Pv-Nil Pv-Emp) (wf⇒lc wf-H′) (wf-fv wf-H′) refl
```

## Conjecture 8 over well-formed contexts is false

```agda
¬Conj-8ʷᶜ : ¬ Conj-8ʷᶜ
¬Conj-8ʷᶜ =
  refutes-NR {f = L₀} {q = R₀} {A = φ₀} {B = ⊥ᵗ} (wf⇒lc wf-L₀) (wf⇒lc wf-¬φ₀) (wf⇒lc wf-R₀) (wf-fv wf-H)
             L₀≤¬φ₀ wf-H wf-H′ H′-reaches (H-NR (wf⇒lc wf-H))
```

## What this establishes

`¬Conj-8ʷᶜ`, with nothing assumed: well-subtyping in MPSS is not closed under covariant contexts,
even in the empty context. The paper's route to Lemma 7, Lemma 6 and Theorem 5 goes through the
conjecture, so it is closed over well-formed contexts as well. The instance does not refute
`Lem-6ʷᶜ` or `Preservationʷᶜ` of `MPSS/WfCtx`, which stay open.
