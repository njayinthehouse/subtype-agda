# MPSS: Hurkens' paradox, and its kind

The term of A. J. C. Hurkens, *A simplification of Girard's paradox* (TLCA 1995), Section 3,
p. 269, with the names of Section 7, p. 277 (`refs/hurkens95tlca.pdf`), under the encoding of
`MPSS/CONJ8.md` §20: `Πx:A.B ↦ λx≤A.B`, `λx:A.M ↦ λx≤A.M`, every sort `↦ ⊤`. It is the term of
`conj8-hurkens-probe.py`, whose node counts agree with the lengths Hurkens prints.

    ℘S = S → *          ⊥ = ∀p:*.p          ¬φ = [φ ⇒ ⊥]
    U  = ΠX:□.((℘℘X → X) → ℘℘X)
    τt = ΛX:□.λf:(℘℘X→X).λp:℘X.(t λx:U.(p (f ({x X} f))))
    σs = ({s U} λt:℘℘U.τt)
    Δ  = λy:U.¬∀p:℘U.[(σy p) ⇒ (p τσy)]
    Ω  = ΛX:□.λf:(℘℘X→X).λp:℘X.∀x:U.[(σx λy:U.(p (f ({y X} f)))) ⇒ (p (f ({x X} f)))]
    φ₀ = ∀p:℘U.[∀x:U.[(σx p) ⇒ (p x)] ⇒ (p Ω)]
    R₀ = let p:℘U.suppose 1:∀x:U.[(σx p) ⇒ (p x)].[⟨1 Ω⟩ let x:U.⟨1 τσx⟩]
    M₀ = let x:U.suppose 2:(σx Δ).suppose 3:∀p:℘U.[(σx p) ⇒ (p τσx)].
           [[⟨3 Δ⟩ 2] let p:℘U.⟨3 λy:U.(p τσy)⟩]
    L₀ = suppose 0:φ₀.[[⟨0 Δ⟩ M₀] let p:℘U.⟨0 λy:U.(p τσy)⟩]

The terms are written with names and closed binder by binder, as the probe does. `τ` and `σ` are
functions of the metalanguage, as in Hurkens ("we do not consider σ and τ as terms"); the names
they bind (1–5) are different from the names of the terms they are applied to (6–13), so closing
a binder of `τ` captures nothing of its argument.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.HurkensTerm where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import MPSS.Reduction
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_)
open import MPSS.Kinding
open import PSS.Syntax
```

## The terms

```agda
-- λx≤a.b, with x a name of b
ƛ : Name → Tm → Tm → Tm
ƛ x a b = lam a (closeRec 0 x b)

-- a → b, for b that does not mention the binder
infixr 6 _⇒_
_⇒_ : Tm → Tm → Tm
a ⇒ b = lam a b

infixl 7 _·_
_·_ : Tm → Tm → Tm
_·_ = app

℘ : Tm → Tm
℘ s = s ⇒ Top

⊥ᵗ : Tm
⊥ᵗ = ƛ 7 Top (fvar 7)

¬ᵗ : Tm → Tm
¬ᵗ φ = φ ⇒ ⊥ᵗ

U : Tm
U = ƛ 1 Top ((℘ (℘ (fvar 1)) ⇒ fvar 1) ⇒ ℘ (℘ (fvar 1)))

τ : Tm → Tm
τ t = ƛ 1 Top (ƛ 2 (℘ (℘ (fvar 1)) ⇒ fvar 1) (ƛ 3 (℘ (fvar 1))
        (t · ƛ 4 U (fvar 3 · (fvar 2 · (fvar 4 · fvar 1 · fvar 2))))))

σ : Tm → Tm
σ s = s · U · ƛ 5 (℘ (℘ U)) (τ (fvar 5))

τσ : Tm → Tm
τσ s = τ (σ s)

Δ : Tm
Δ = ƛ 6 U (¬ᵗ (ƛ 7 (℘ U) ((σ (fvar 6) · fvar 7) ⇒ (fvar 7 · τσ (fvar 6)))))

Ω : Tm
Ω = ƛ 1 Top (ƛ 2 (℘ (℘ (fvar 1)) ⇒ fvar 1) (ƛ 3 (℘ (fvar 1))
      (ƛ 8 U ((σ (fvar 8) · ƛ 6 U (fvar 3 · (fvar 2 · (fvar 6 · fvar 1 · fvar 2))))
               ⇒ (fvar 3 · (fvar 2 · (fvar 8 · fvar 1 · fvar 2)))))))

-- ∀x:U.[(σx p) ⇒ (p x)]
ind : Tm → Tm
ind p = ƛ 8 U ((σ (fvar 8) · p) ⇒ (p · fvar 8))

-- λy:U.(p τσy)
shift : Tm → Tm
shift p = ƛ 6 U (p · τσ (fvar 6))

φ₀ : Tm
φ₀ = ƛ 7 (℘ U) (ind (fvar 7) ⇒ (fvar 7 · Ω))

R₀ : Tm
R₀ = ƛ 7 (℘ U) (ƛ 11 (ind (fvar 7))
       (fvar 11 · Ω · ƛ 8 U (fvar 11 · τσ (fvar 8))))

M₀ : Tm
M₀ = ƛ 8 U (ƛ 12 (σ (fvar 8) · Δ)
       (ƛ 13 (ƛ 7 (℘ U) ((σ (fvar 8) · fvar 7) ⇒ (fvar 7 · τσ (fvar 8))))
          (fvar 13 · Δ · fvar 12 · ƛ 7 (℘ U) (fvar 13 · shift (fvar 7)))))

L₀ : Tm
L₀ = ƛ 10 φ₀ (fvar 10 · Δ · M₀ · ƛ 7 (℘ U) (fvar 10 · shift (fvar 7)))

¬φ₀ : Tm
¬φ₀ = ¬ᵗ φ₀

-- the paradox [L₀ R₀], and the other side of the instance
H H′ : Tm
H  = L₀ · R₀
H′ = ¬φ₀ · R₀
```

## The kind of the paradox

Only the proof-level skeleton is examined: every operand that is an object is kinded by `k-any`
without being looked at, and no annotation is looked at at all.

```agda
R₀ᵏ : [] ⊢ᵏ R₀ ∶ F
R₀ᵏ = k-lam [] aF λ {p} _ →
      k-lam [] aT λ {h} _ →
        k-app aT (k-app aF (k-var (here refl)) k-any)
                 (k-lam [] aF λ {x} _ → k-app aF (k-var (here refl)) k-any)

M₀ᵏ : ∀ {Φ} → Φ ⊢ᵏ M₀ ∶ F
M₀ᵏ = k-lam [] aF λ {x} _ →
      k-lam [] aT λ {h₂} _ →
      k-lam [] aG λ {h₃} _ →
        k-app aG (k-app aT (k-app aF (k-var (here refl)) k-any)
                           (k-var (there (here refl))))
                 (k-lam [] aF λ {p} _ → k-app aF (k-var (here refl)) k-any)

L₀ᵏ : [] ⊢ᵏ L₀ ∶ G
L₀ᵏ = k-lam [] aG λ {h} _ →
        k-app aG (k-app aT (k-app aF (k-var (here refl)) k-any) M₀ᵏ)
                 (k-lam [] aF λ {p} _ → k-app aF (k-var (here refl)) k-any)

Hᵏ : [] ⊢ᵏ H ∶ S
Hᵏ = k-app aG L₀ᵏ R₀ᵏ

-- no ⟶ᵉ*-reduct of the paradox is an abstraction
H-NR : LC H → ∀ {w b} → ¬ ([] ∣ [] ⊢ H ⟶ᵉ* lam w b)
H-NR lc = S⇒NR lc Hᵏ
```

## What this establishes

`Hᵏ`: Hurkens' paradox has kind `S`. `H-NR`: so, given that it is locally closed, none of its
`⟶ᵉ*`-reducts is an abstraction — the hypothesis `NR` of `MPSS/PromotionNoWhnf`'s `refutes-NR`,
for this term.
