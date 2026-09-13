# MPSS: the downstream theorems with Lemmas 1 and 2 discharged

`MPSS/Inversion`, `MPSS/Progress`, `MPSS/Evaluation` and `MPSS/TypeSafety` take Lemmas 1 and 2
of `MPSS/Assumed` as parameters and use them in exactly one way: Theorem 3, on a machine chain
read off a well-formed static chain. `MPSS/VariantTransfer` proves Theorem 3 outright on chains
that record local closure, and a well-formed chain records the well-formedness, hence the local
closure, of every term on it. So the four modules' results follow with the two lemmas gone.
Each is transcribed with its uses of Lemma 1 and 2 replaced by `Thm-3wf`; nothing else changes.

What is left assumed by type safety is then what the paper itself flags (Conjecture 8) and the
repaired Proposition 17 (`MPSS/Assumed`, `MPSS/BetaScope`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Unconditional where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

open import MPSS.WellFormed
open import MPSS.Static using (⊑wf⇒⊲; Lem-15; Lem-16; ⊑*wf⇒wfʳ)
open import MPSS.Inversion using (lam-inv)
open import MPSS.TopLemma using (Top≰lam)
open import MPSS.Congruence using (_∣_⊢_⊲*ᴸ[_]_; subᴸ; trsᴸ)
open import MPSS.VariantTransfer using (Thm-3ᴸ)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Preservation using (Prop-27; Thm-5)
open import MPSS.Evaluation using (Lem-7₀; Lem-23)
open import MPSS.Lemma7 using (Lem-7₀-holds)
open import MPSS.Lemma23 using (Lem-23-holds)
open import MPSS.Assumed using (Prop-17ʳ; Conj-8)

open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; closeRec)
open import PSS.Reduction
  using (_↦_; E-App; E-Lam-l; E-Lam-r; E-App-l; E-App-r;
         NF; Neutral; nf-Top; nf-lam; nf-ne; ne-var; ne-app)
open import PSS.Progress using (NF-open-rename; ↦-lc; ↦-close-rename)
```

## Theorem 3 on well-formed chains

```agda
⊑*wf⇒⊲*ᴸ : ∀ {Γ u m t} → Γ ⊢ u ⊑*wf[ m ] t → Γ ∣ [] ⊢ u ⊲*ᴸ[ m ] t
⊑*wf⇒⊲*ᴸ (Ws-Sub w d w′)   = subᴸ (wf⇒lc w) (wf⇒lc w′) (⊑wf⇒⊲ d)
⊑*wf⇒⊲*ᴸ (Ws-Trs d₁ wu d₂) = trsᴸ (⊑*wf⇒⊲*ᴸ d₁) (wf⇒lc wu) (⊑*wf⇒⊲*ᴸ d₂)

Thm-3wf : ∀ {Γ u m t} → Γ ⊢ u ⊑*wf[ m ] t → Γ ∣ [] ⊢ u ⊲[ m ] t
Thm-3wf d = Thm-3ᴸ (⊑*wf⇒⊲*ᴸ d)
```

## Theorem 11 and Lemma 10

```agda
Thm-11wf : ∀ {Γ t u} → ¬ (Γ ⊢ Top ⊑*wf[ sub-m ] lam t u)
Thm-11wf d = Top≰lam (Thm-3wf d)

Lem-10 : ∀ {Γ t u t' u'} → Γ ⊢ lam t u ⊑*wf[ sub-m ] lam t' u' → Γ ⊢ t ⊑wf[ eqv-m ] t'
Lem-10 d = lam-inv (Thm-3wf d)
```

## Theorem 4 (progress)

`MPSS/Progress`'s proof, with `Thm-11wf` in place of its parameterised form.

```agda
Thm-4 : ∀ {Γ t} → LC t → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')
Thm-4 lc-fvar (Wf-PrS _ _) = inj₁ (nf-ne ne-var)
Thm-4 lc-fvar (Wf-PrE _ _) = inj₁ (nf-ne ne-var)
Thm-4 lc-Top  (Wf-Top _)   = inj₁ nf-Top
Thm-4 (lc-lam {a} {b} L₀ la F₀) (Wf-Fun L F wa) = result
  where
    A  = L₀ ++ L ++ fv b
    x  = fresh A
    a∉ = fresh-∉ A
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ (∉-++ʳ L₀ a∉)
    x∉b : x ∉ fv b
    x∉b  = ∉-++ʳ L (∉-++ʳ L₀ a∉)

    result : NF (lam a b) ⊎ ∃[ t' ] (lam a b ↦ t')
    result with Thm-4 la wa
    ... | inj₂ (a' , st) = inj₂ (lam a' b , E-Lam-l st)
    ... | inj₁ na with Thm-4 (F₀ x∉L₀) (F x∉L)
    ...   | inj₁ nb = inj₁ (nf-lam [] na (λ {y} _ → NF-open-rename {b} x y x∉b nb))
    ...   | inj₂ (w , stw) =
             inj₂ ( lam a (closeRec 0 x w)
                  , E-Lam-r [] (λ {y} _ →
                      ↦-close-rename {b} {w} x y (↦-lc (F₀ x∉L₀) stw) x∉b stw) )
Thm-4 (lc-app {u} {v} lu lv) (Wf-App d₁ d₂)
  with Thm-4 lu (⊑*wf⇒wfˡ d₁)
... | inj₂ (u' , st)              = inj₂ (app u' v , E-App-l st)
... | inj₁ nf-Top                 = ⊥-elim (Thm-11wf d₁)
... | inj₁ (nf-lam {a} {b} _ _ _) = inj₂ ((b ^ v) , E-App lu lv)
... | inj₁ (nf-ne ne) with Thm-4 lv (⊑*wf⇒wfˡ d₂)
...   | inj₂ (v' , st) = inj₂ (app u v' , E-App-r st)
...   | inj₁ nv        = inj₁ (nf-ne (ne-app ne nv))

Thm-4′ : ∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')
Thm-4′ w = Thm-4 (wf⇒lc w) w
```

## Lemma 6 (evaluation preserves well-formedness)

`MPSS/Evaluation`'s proof, with `Lem-10` above in place of its parameterised form.

```agda
module _ (prop-17 : Prop-17ʳ) (lem-7 : Lem-7₀) (lem-23 : Lem-23) where

  Lem-6 : ∀ {Γ t t'} → Γ ⊢ t wf → t ↦ t' → Γ ⊢ t' wf
  Lem-6 (Wf-App {u = lam a b} {v = c} d₁ d₂) (E-App _ _)
    with ⊑*wf⇒wfˡ d₁ | ⊑*wf⇒wfʳ d₁
  ... | Wf-Fun L F wa | Wf-Fun _ _ wz =
        lem-7 b L F (Ws-Trs d₂ wz (Ws-Sub wz (Lem-16 (Lem-15 (Lem-10 d₁))) wa))
  Lem-6 {Γ} (Wf-Fun L F wu) (E-Lam-l st) =
    Wf-Fun L (λ {x} x∉ → lem-23 [] (F x∉) wu e wu') wu'
    where
      wu' = Lem-6 wu st
      e   = prop-17 (Pv-Nil (wf⇒prevalid wu)) (wf⇒lc wu) (wf-fv wu) st
  Lem-6 (Wf-Fun L F wu) (E-Lam-r L' F') =
    Wf-Fun (L ++ L') (λ {x} x∉ → Lem-6 (F (∉-++ˡ x∉)) (F' (∉-++ʳ L x∉))) wu
  Lem-6 (Wf-App d₁ d₂) (E-App-l st) =
    Wf-App (Prop-27 prop-17 d₁ st (Lem-6 (⊑*wf⇒wfˡ d₁) st)) d₂
  Lem-6 (Wf-App d₁ d₂) (E-App-r st) =
    Wf-App d₁ (Prop-27 prop-17 d₂ st (Lem-6 (⊑*wf⇒wfˡ d₂) st))
```

## Type safety

```agda
module _ (prop-17 : Prop-17ʳ) (conj-8 : Conj-8) where

  progress : ∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')
  progress = Thm-4′

  preservation : ∀ {Γ t t' u}
               → Γ ⊢ t ⊑*wf[ sub-m ] u → t ↦ t' → Γ ⊢ t' ⊑*wf[ sub-m ] u
  preservation = Thm-5 prop-17 (Lem-6 prop-17 (Lem-7₀-holds conj-8) Lem-23-holds)

  type-safety : (∀ {Γ t} → Γ ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t'))
              × (∀ {Γ t t' u} → Γ ⊢ t ⊑*wf[ sub-m ] u → t ↦ t' → Γ ⊢ t' ⊑*wf[ sub-m ] u)
  type-safety = progress , preservation
```

## What this establishes

Theorem 11 (as printed), Lemma 10, Theorem 4 with **nothing assumed**; Lemma 6 and Theorem 5
from the repaired Proposition 17 and Lemma 7 and Lemma 23 as before; and type safety for MPSS
from exactly two statements: Conjecture 8, the paper's own, and the repaired Proposition 17.
Lemmas 1 and 2 of `MPSS/Assumed` are no longer on the path to any of the paper's theorems.
