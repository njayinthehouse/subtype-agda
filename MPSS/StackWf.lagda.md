# MPSS, candidate C: well-formedness that reads the operand stack — the judgements, and progress

`CONJ8.md` §25, candidate C. MPSS's machine (`⟶ᵉ`, `⟶ˢ`, contexts with `≡` entries, the machine
relation `⊲`) is kept as printed. Figure 4 is replaced by the static judgements of v1
(`PSS/WellFormed`), which are indexed by the operand stack:

- an abstraction that meets an operand `δ` is checked with its parameter bound to the operand —
  `x ≡ δ` here, where v1 has `x ≤ δ` — at the remaining stack (`Wc-FOp`);
- an application `u v` at `s` asks `u ≤*wf λt.⊤` at `v ∷ s` (`Wc-App`);
- a variable is well-formed at `s` when its annotation is (`Wc-PrS`, `Wc-PrE`; v1's `W-Var`);
- well-subtyping is the machine relation between terms well-formed at the same configuration
  (`Wc-Rule`), with no condition on the terms in between.

Under these rules the term `t₆ = (λx≤¬φ₀. x R₀ ⊤) L₀` of `MPSS/Lem6WfCtxRefuted` is checked with
`x ≡ L₀`, not under `x ≤ ¬φ₀` alone.

This module: the judgements, what they carry (prevalidity, local closure, both ends), Theorem 11
and **progress** (Theorem 4) for them — from `Thm-3ᴸ`, which holds for the machine
relation at every stack. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWf where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

open import MPSS.Subtyping
open import MPSS.TopLemma using (Top≰lam)
open import MPSS.Congruence using (_∣_⊢_⊲*ᴸ[_]_; subᴸ; trsᴸ)
open import MPSS.VariantTransfer using (Thm-3ᴸ)
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; closeRec)
open import PSS.Reduction
  using (_↦_; E-App; E-Lam-l; E-Lam-r; E-App-l; E-App-r;
         NF; Neutral; nf-Top; nf-lam; nf-ne; ne-var; ne-app)
open import PSS.Progress using (NF-open-rename; ↦-lc; ↦-close-rename)
```

## The three judgements

```agda
infix 3 _∣_⊢_wfˢ _∣_⊢_≤wfˢ_ _∣_⊢_≤*wfˢ_

data _∣_⊢_wfˢ    : Ctx → Stack → Tm → Set
data _∣_⊢_≤wfˢ_  : Ctx → Stack → Tm → Tm → Set
data _∣_⊢_≤*wfˢ_ : Ctx → Stack → Tm → Tm → Set

data _∣_⊢_wfˢ where

  Wc-PrS : ∀ {Γ s x t}
         → Γ ∣ s prevalid → x ≤ t ∈ Γ
         → Γ ∣ s ⊢ t wfˢ
         → Γ ∣ s ⊢ fvar x wfˢ

  Wc-PrE : ∀ {Γ s x α}
         → Γ ∣ s prevalid → x ≐ α ∈ Γ
         → Γ ∣ s ⊢ α wfˢ
         → Γ ∣ s ⊢ fvar x wfˢ

  Wc-Top : ∀ {Γ s}
         → Γ ∣ s prevalid
         → Γ ∣ s ⊢ Top wfˢ

  Wc-Fun : ∀ {Γ t u} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) wfˢ)
         → Γ ∣ [] ⊢ t wfˢ
         → Γ ∣ [] ⊢ lam t u wfˢ

  Wc-FOp : ∀ {Γ s δ t u} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , eqv , δ) ∷ Γ) ∣ s ⊢ (u ^ fvar x) wfˢ)
         → Γ ∣ [] ⊢ t wfˢ
         → Γ ∣ (δ ∷ s) ⊢ lam t u wfˢ

  Wc-App : ∀ {Γ s u v t}
         → Γ ∣ (v ∷ s) ⊢ u ≤*wfˢ lam t Top
         → Γ ∣ [] ⊢ v ≤*wfˢ t
         → Γ ∣ s ⊢ app u v wfˢ

data _∣_⊢_≤wfˢ_ where

  Wc-Rule : ∀ {Γ s u t}
          → Γ ∣ s ⊢ u wfˢ
          → Γ ∣ s ⊢ t wfˢ
          → Γ ∣ s ⊢ u ≤ t
          → Γ ∣ s ⊢ u ≤wfˢ t

data _∣_⊢_≤*wfˢ_ where

  Wc-Sub : ∀ {Γ s v t}
         → Γ ∣ s ⊢ v ≤wfˢ t
         → Γ ∣ s ⊢ v ≤*wfˢ t

  Wc-Trs : ∀ {Γ s v u t}
         → Γ ∣ s ⊢ v ≤*wfˢ u
         → Γ ∣ s ⊢ u ≤*wfˢ t
         → Γ ∣ s ⊢ v ≤*wfˢ t
```

## Both ends, prevalidity, local closure

```agda
≤*wfˢ⇒both : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤*wfˢ t → (Γ ∣ s ⊢ v wfˢ) × (Γ ∣ s ⊢ t wfˢ)
≤*wfˢ⇒both (Wc-Sub (Wc-Rule wv wt _)) = wv , wt
≤*wfˢ⇒both (Wc-Trs d₁ d₂)             = proj₁ (≤*wfˢ⇒both d₁) , proj₂ (≤*wfˢ⇒both d₂)

wfˢ⇒lc : ∀ {Γ s t} → Γ ∣ s ⊢ t wfˢ → LC t
wfˢ⇒lc (Wc-PrS _ _ _) = lc-fvar
wfˢ⇒lc (Wc-PrE _ _ _) = lc-fvar
wfˢ⇒lc (Wc-Top _)     = lc-Top
wfˢ⇒lc (Wc-Fun L F w) = lc-lam L (wfˢ⇒lc w) (λ x∉ → wfˢ⇒lc (F x∉))
wfˢ⇒lc (Wc-FOp L F w) = lc-lam L (wfˢ⇒lc w) (λ x∉ → wfˢ⇒lc (F x∉))
wfˢ⇒lc (Wc-App d₁ d₂) = lc-app (lcˡ d₁) (lcˡ d₂)
  where
    lcˡ : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤*wfˢ t → LC v
    lcˡ (Wc-Sub (Wc-Rule wv _ _)) = wfˢ⇒lc wv
    lcˡ (Wc-Trs d _)              = lcˡ d

wfˢ⇒prevalid : ∀ {Γ s t} → Γ ∣ s ⊢ t wfˢ → Γ ∣ s prevalid
wfˢ⇒prevalid (Wc-PrS pv _ _) = pv
wfˢ⇒prevalid (Wc-PrE pv _ _) = pv
wfˢ⇒prevalid (Wc-Top pv)     = pv
wfˢ⇒prevalid (Wc-Fun L F w)  = wfˢ⇒prevalid w
wfˢ⇒prevalid (Wc-App d₁ _)   = prevalid-pop (pvˡ d₁)
  where
    pvˡ : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤*wfˢ t → Γ ∣ s prevalid
    pvˡ (Wc-Sub (Wc-Rule wv _ _)) = wfˢ⇒prevalid wv
    pvˡ (Wc-Trs d _)              = pvˡ d
wfˢ⇒prevalid (Wc-FOp {Γ} {s} {δ} L F w) =
  Pv-Sta (prevalid-strengthen x∉s pv) (head-lc (prevalid-ctx pv)) (head-fv (prevalid-ctx pv))
  where
    x    = fresh (L ++ fvStack s)
    x∉L  = ∉-++ˡ (fresh-∉ (L ++ fvStack s))
    x∉s : x ∉ fvStack s
    x∉s  = ∉-++ʳ L (fresh-∉ (L ++ fvStack s))
    pv : ((x , eqv , δ) ∷ Γ) ∣ s prevalid
    pv   = wfˢ⇒prevalid (F x∉L)
```

## Theorem 3 on well-formed chains, Theorem 11

```agda
≤*wfˢ⇒⊲*ᴸ : ∀ {Γ s u t} → Γ ∣ s ⊢ u ≤*wfˢ t → Γ ∣ s ⊢ u ⊲*ᴸ[ sub-m ] t
≤*wfˢ⇒⊲*ᴸ (Wc-Sub (Wc-Rule wu wt d)) = subᴸ (wfˢ⇒lc wu) (wfˢ⇒lc wt) d
≤*wfˢ⇒⊲*ᴸ (Wc-Trs d₁ d₂) =
  trsᴸ (≤*wfˢ⇒⊲*ᴸ d₁) (wfˢ⇒lc (proj₂ (≤*wfˢ⇒both d₁))) (≤*wfˢ⇒⊲*ᴸ d₂)

Thm-3ˢ : ∀ {Γ s u t} → Γ ∣ s ⊢ u ≤*wfˢ t → Γ ∣ s ⊢ u ≤ t
Thm-3ˢ d = Thm-3ᴸ (≤*wfˢ⇒⊲*ᴸ d)

≤*wfˢ-one : ∀ {Γ s u t} → Γ ∣ s ⊢ u ≤*wfˢ t → Γ ∣ s ⊢ u ≤wfˢ t
≤*wfˢ-one d = Wc-Rule (proj₁ (≤*wfˢ⇒both d)) (proj₂ (≤*wfˢ⇒both d)) (Thm-3ˢ d)

Thm-11ˢ : ∀ {Γ s t u} → ¬ (Γ ∣ s ⊢ Top ≤*wfˢ lam t u)
Thm-11ˢ d = Top≰lam (Thm-3ˢ d)
```

## Theorem 4 — progress

`MPSS/Unconditional`'s proof; the stack plays no part beyond choosing between `Wc-Fun` and
`Wc-FOp`.

```agda
Thm-4ˢ : ∀ {Γ s t} → LC t → Γ ∣ s ⊢ t wfˢ → NF t ⊎ ∃[ t' ] (t ↦ t')
Thm-4ˢ lc-fvar (Wc-PrS _ _ _) = inj₁ (nf-ne ne-var)
Thm-4ˢ lc-fvar (Wc-PrE _ _ _) = inj₁ (nf-ne ne-var)
Thm-4ˢ lc-Top  (Wc-Top _)     = inj₁ nf-Top
Thm-4ˢ (lc-app {u} {v} lu lv) (Wc-App d₁ d₂)
  with Thm-4ˢ lu (proj₁ (≤*wfˢ⇒both d₁))
... | inj₂ (u' , st)              = inj₂ (app u' v , E-App-l st)
... | inj₁ nf-Top                 = ⊥-elim (Thm-11ˢ d₁)
... | inj₁ (nf-lam {a} {b} _ _ _) = inj₂ ((b ^ v) , E-App lu lv)
... | inj₁ (nf-ne ne) with Thm-4ˢ lv (proj₁ (≤*wfˢ⇒both d₂))
...   | inj₂ (v' , st) = inj₂ (app u v' , E-App-r st)
...   | inj₁ nv        = inj₁ (nf-ne (ne-app ne nv))
Thm-4ˢ (lc-lam {a} {b} L₀ la F₀) (Wc-Fun L F wa) = result
  where
    A  = L₀ ++ L ++ fv b
    x  = fresh A
    a∉ = fresh-∉ A
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ (∉-++ʳ L₀ a∉)
    x∉b : x ∉ fv b
    x∉b  = ∉-++ʳ L (∉-++ʳ L₀ a∉)
    result : NF (lam a b) ⊎ ∃[ t' ] (lam a b ↦ t')
    result with Thm-4ˢ la wa
    ... | inj₂ (a' , st) = inj₂ (lam a' b , E-Lam-l st)
    ... | inj₁ na with Thm-4ˢ (F₀ x∉L₀) (F x∉L)
    ...   | inj₁ nb = inj₁ (nf-lam [] na (λ {y} _ → NF-open-rename {b} x y x∉b nb))
    ...   | inj₂ (w , stw) =
             inj₂ ( lam a (closeRec 0 x w)
                  , E-Lam-r [] (λ {y} _ →
                      ↦-close-rename {b} {w} x y (↦-lc (F₀ x∉L₀) stw) x∉b stw) )
Thm-4ˢ (lc-lam {a} {b} L₀ la F₀) (Wc-FOp L F wa) = result
  where
    A  = L₀ ++ L ++ fv b
    x  = fresh A
    a∉ = fresh-∉ A
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ (∉-++ʳ L₀ a∉)
    x∉b : x ∉ fv b
    x∉b  = ∉-++ʳ L (∉-++ʳ L₀ a∉)
    result : NF (lam a b) ⊎ ∃[ t' ] (lam a b ↦ t')
    result with Thm-4ˢ la wa
    ... | inj₂ (a' , st) = inj₂ (lam a' b , E-Lam-l st)
    ... | inj₁ na with Thm-4ˢ (F₀ x∉L₀) (F x∉L)
    ...   | inj₁ nb = inj₁ (nf-lam [] na (λ {y} _ → NF-open-rename {b} x y x∉b nb))
    ...   | inj₂ (w , stw) =
             inj₂ ( lam a (closeRec 0 x w)
                  , E-Lam-r [] (λ {y} _ →
                      ↦-close-rename {b} {w} x y (↦-lc (F₀ x∉L₀) stw) x∉b stw) )
```

## What this establishes

The judgements of candidate C, and for them: both ends of a well-subtyping chain are well-formed
(`≤*wfˢ⇒both`), prevalidity and local closure are recoverable, a chain is one layer (`Thm-3ˢ`,
`≤*wfˢ-one`), no abstraction is above `⊤` (`Thm-11ˢ`), and **progress** (`Thm-4ˢ`) at every
configuration. Nothing is assumed. Preservation is the subject of the modules that follow.
