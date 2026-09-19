# MPSS, candidate A: `Ms-FOp` keeps the bound — Lemma 1 and Theorem 3 fail at the machine level

`CONJ8.md` §25 lists three changes that might give an MPSS-style calculus type safety. Candidate A
changes one rule of `⟶ˢ`: when an abstraction `λx≤t.u` consumes an operand `α`, the body is
promoted under `x ≡ α` *and* `x ≤ t`, so `Ms-Pro` fires on the consumed parameter. As printed,
`Ms-FOp` forgets `x ≤ t`.

The relation is written here without touching `Ctx`: the kept bounds travel in a separate list
`Δ`, read only by the new rule `Ms-ProKept`. `⟶ᵉ` is the printed relation, unchanged.

What this module proves: under A, **Lemma 1 (commutation) and Theorem 3 (transitivity
elimination) are false for the machine relation**, which carries no well-formedness. The term is
`(λx≤λ⊤.⊤. x) ⊤`: it promotes to `λ⊤.⊤` through the kept bound and reduces to `⊤` through the
operand, and `⊤` is below no abstraction. The term is ill-formed (`⊤` is not below `λ⊤.⊤`), so
this says nothing against type safety of A; it says that the paper's route to progress — Lemma 1,
Theorem 3, then Lemma 10 and Theorem 11 on the machine relation — is closed under A, and any
proof has to use well-formedness of the terms promoted.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CandidateA where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import MPSS.WellFormed
open import MPSS.CtxReduction using (_∣_↣_∣_; Ct-Refl)
open import MPSS.TopLemma using (Top-⟶ᵉ)
```

## The promotion relation of candidate A

```agda
Bounds : Set
Bounds = List (Name × Tm)

infix 3 _∣_∣_⊢_⟶ˢᴬ_
data _∣_∣_⊢_⟶ˢᴬ_ : Bounds → Ctx → Stack → Tm → Tm → Set where

  Ms-Pro     : ∀ {Δ Γ s x t}
             → Γ ∣ s prevalid
             → x ≤ t ∈ Γ
             → Δ ∣ Γ ∣ s ⊢ fvar x ⟶ˢᴬ t

  Ms-ProKept : ∀ {Δ Γ s x t}
             → Γ ∣ s prevalid
             → (x , t) ∈ Δ
             → Δ ∣ Γ ∣ s ⊢ fvar x ⟶ˢᴬ t

  Ms-Top     : ∀ {Δ Γ s u}
             → Γ ∣ s prevalid
             → Δ ∣ Γ ∣ s ⊢ u ⟶ˢᴬ Top

  Ms-Equ     : ∀ {Δ Γ s u v}
             → Γ ∣ s prevalid
             → Γ ∣ s ⊢ u ⟶ᵉ v
             → Δ ∣ Γ ∣ s ⊢ u ⟶ˢᴬ v

  Ms-App     : ∀ {Δ Γ s u u' v}
             → Δ ∣ Γ ∣ (v ∷ s) ⊢ u ⟶ˢᴬ u'
             → Δ ∣ Γ ∣ s ⊢ app u v ⟶ˢᴬ app u' v

  Ms-Fun     : ∀ {Δ Γ t u u'} (L : List Name)
             → (∀ {x} → x ∉ L → Δ ∣ ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶ˢᴬ (u' ^ fvar x))
             → Δ ∣ Γ ∣ [] ⊢ lam t u ⟶ˢᴬ lam t u'

  Ms-FOpᴬ    : ∀ {Δ Γ s α t u u'} (L : List Name)
             → (∀ {x} → x ∉ L
                  → ((x , t) ∷ Δ) ∣ ((x , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ˢᴬ (u' ^ fvar x))
             → Δ ∣ Γ ∣ (α ∷ s) ⊢ lam t u ⟶ˢᴬ lam t u'
```

The machine relation over it (Figure 3 in the subtyping reading), and its transitive closure.

```agda
infix 3 _∣_⊢_≤ᴬ_ _∣_⊢_≤ᴬ*_
data _∣_⊢_≤ᴬ_ : Ctx → Stack → Tm → Tm → Set where
  Aa-Refl  : ∀ {Γ s t} → Γ ∣ s prevalid → Γ ∣ s ⊢ t ≤ᴬ t
  Aa-Left  : ∀ {Γ s v v' t} → [] ∣ Γ ∣ s ⊢ v ⟶ˢᴬ v' → Γ ∣ s ⊢ v' ≤ᴬ t → Γ ∣ s ⊢ v ≤ᴬ t
  Aa-Right : ∀ {Γ s v t t'} → Γ ∣ s ⊢ v ≤ᴬ t' → Γ ∣ s ⊢ t ⟶ᵉ t' → Γ ∣ s ⊢ v ≤ᴬ t

data _∣_⊢_≤ᴬ*_ : Ctx → Stack → Tm → Tm → Set where
  Aa-Sub   : ∀ {Γ s v t} → Γ ∣ s ⊢ v ≤ᴬ t → Γ ∣ s ⊢ v ≤ᴬ* t
  Aa-Trans : ∀ {Γ s v u t} → Γ ∣ s ⊢ v ≤ᴬ* u → Γ ∣ s ⊢ u ≤ᴬ* t → Γ ∣ s ⊢ v ≤ᴬ* t
```

## The term

```agda
a m m′ : Tm
a  = lam Top Top                  -- λ⊤.⊤
m  = app (lam a (bvar 0)) Top     -- (λx≤λ⊤.⊤. x) ⊤
m′ = app (lam a a) Top            -- (λx≤λ⊤.⊤. λ⊤.⊤) ⊤

pv₀ : [] ∣ [] prevalid
pv₀ = Pv-Nil Pv-Emp

pvᵉ : ∀ {x} → ((x , eqv , Top) ∷ []) ∣ [] prevalid
pvᵉ = Pv-Nil (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ()))

pvˢ : ∀ {x} → ((x , sub , Top) ∷ []) ∣ [] prevalid
pvˢ = Pv-Nil (Pv-Ctx Pv-Emp (λ ()) lc-Top (λ ()))

a⟶ᵉa : [] ∣ [] ⊢ a ⟶ᵉ a
a⟶ᵉa = Me-Fun {u' = Top} [] (Me-Top pv₀) (λ _ → Me-Top pvˢ)
```

`m ⟶ᵉ ⊤` by `Me-Bet`; `m ⟶ˢᴬ m′` by `Ms-App` over `Ms-FOpᴬ` over `Ms-ProKept`; `m′ ⟶ᵉ λ⊤.⊤` by
`Me-Bet`.

```agda
m⟶ᵉTop : [] ∣ [] ⊢ m ⟶ᵉ Top
m⟶ᵉTop = Me-Bet {u' = bvar 0} [] (λ _ → Me-Var pv₀) (Me-Top pv₀)

m⟶ˢᴬm′ : [] ∣ [] ∣ [] ⊢ m ⟶ˢᴬ m′
m⟶ˢᴬm′ = Ms-App (Ms-FOpᴬ {u' = a} [] (λ _ → Ms-ProKept pvᵉ (here refl)))

m′⟶ᵉa : [] ∣ [] ⊢ m′ ⟶ᵉ a
m′⟶ᵉa = Me-Bet {u' = a} [] (λ _ → a⟶ᵉa) (Me-Top pv₀)

Top≤ᴬm : [] ∣ [] ⊢ Top ≤ᴬ m
Top≤ᴬm = Aa-Right (Aa-Refl pv₀) m⟶ᵉTop

m≤ᴬa : [] ∣ [] ⊢ m ≤ᴬ a
m≤ᴬa = Aa-Left m⟶ˢᴬm′ (Aa-Left (Ms-Equ pv₀ m′⟶ᵉa) (Aa-Refl pv₀))

Top≤ᴬ*a : [] ∣ [] ⊢ Top ≤ᴬ* a
Top≤ᴬ*a = Aa-Trans (Aa-Sub Top≤ᴬm) (Aa-Sub m≤ᴬa)
```

## `⊤` is below no abstraction in one layer

As for the printed relation (`MPSS/TopLemma`): the new rule promotes a variable, not `⊤`.

```agda
Top≰ᴬlam : ∀ {Γ s b c} → ¬ (Γ ∣ s ⊢ Top ≤ᴬ lam b c)
Top≰ᴬlam (Aa-Left (Ms-Top _) d)            = Top≰ᴬlam d
Top≰ᴬlam (Aa-Left (Ms-Equ _ (Me-Top _)) d) = Top≰ᴬlam d
Top≰ᴬlam (Aa-Right d (Me-Fun _ _ _))       = Top≰ᴬlam d
Top≰ᴬlam (Aa-Right d (Me-FOp _ _ _))       = Top≰ᴬlam d
```

## Theorem 3 fails

```agda
Thm-3ᴬ : Set
Thm-3ᴬ = ∀ {Γ s u v} → Γ ∣ s ⊢ u ≤ᴬ* v → Γ ∣ s ⊢ u ≤ᴬ v

¬Thm-3ᴬ : ¬ Thm-3ᴬ
¬Thm-3ᴬ thm = Top≰ᴬlam (thm Top≤ᴬ*a)

Thm-11ᴬ : Set
Thm-11ᴬ = ∀ {Γ s b c} → ¬ (Γ ∣ s ⊢ Top ≤ᴬ* lam b c)

¬Thm-11ᴬ : ¬ Thm-11ᴬ
¬Thm-11ᴬ thm = thm Top≤ᴬ*a
```

## Lemma 1 fails

At the configuration `[] ∣ [⊤]` the abstraction `λx≤λ⊤.⊤. x` reduces by `⟶ᵉ` to `λx≤λ⊤.⊤. ⊤` (the
parameter unfolds to the operand) and promotes to `λx≤λ⊤.⊤. λ⊤.⊤` (the parameter is promoted to
the kept bound). A common reduct would have a body that is both a `⟶ᵉ`-reduct of `λ⊤.⊤`, an
abstraction, and a `⟶ˢᴬ`-reduct of `⊤`, which is `⊤`. Stated with the context reduction taken
reflexive.

```agda
lam-⟶ᵉ : ∀ {Γ s b c w} → Γ ∣ s ⊢ lam b c ⟶ᵉ w → ∃[ b′ ] ∃[ c′ ] (w ≡ lam b′ c′)
lam-⟶ᵉ (Me-Fun _ _ _) = _ , _ , refl
lam-⟶ᵉ (Me-FOp _ _ _) = _ , _ , refl

Top-⟶ˢᴬ : ∀ {Δ Γ s w} → Δ ∣ Γ ∣ s ⊢ Top ⟶ˢᴬ w → w ≡ Top
Top-⟶ˢᴬ (Ms-Top _)            = refl
Top-⟶ˢᴬ (Ms-Equ _ (Me-Top _)) = refl

lam≢Top : ∀ {b c} → ¬ (lam b c ≡ Top)
lam≢Top ()

pv₁ : [] ∣ (Top ∷ []) prevalid
pv₁ = Pv-Sta pv₀ lc-Top (λ ())

edge-e : [] ∣ (Top ∷ []) ⊢ lam a (bvar 0) ⟶ᵉ lam a Top
edge-e = Me-FOp {u' = Top} [] a⟶ᵉa
           (λ _ → Me-Pro pvᵉ (here refl) (Me-Top pvᵉ))

edge-s : [] ∣ [] ∣ (Top ∷ []) ⊢ lam a (bvar 0) ⟶ˢᴬ lam a a
edge-s = Ms-FOpᴬ {u' = a} [] (λ _ → Ms-ProKept pvᵉ (here refl))

no-join : ∀ {t₃} → [] ∣ (Top ∷ []) ⊢ lam a a ⟶ᵉ t₃
        → [] ∣ [] ∣ (Top ∷ []) ⊢ lam a Top ⟶ˢᴬ t₃ → ⊥
no-join (Me-FOp L₁ _ F₁) (Ms-FOpᴬ L₂ F₂) with lam-⟶ᵉ (F₁ (∉-++ˡ (fresh-∉ (L₁ ++ L₂))))
... | _ , _ , p₁ = lam≢Top (trans (sym p₁) (Top-⟶ˢᴬ (F₂ (∉-++ʳ L₁ (fresh-∉ (L₁ ++ L₂))))))
no-join (Me-FOp L₁ _ F₁) (Ms-Equ _ (Me-FOp L₂ _ F₂)) with lam-⟶ᵉ (F₁ (∉-++ˡ (fresh-∉ (L₁ ++ L₂))))
... | _ , _ , p₁ = lam≢Top (trans (sym p₁) (Top-⟶ᵉ (F₂ (∉-++ʳ L₁ (fresh-∉ (L₁ ++ L₂))))))

Lem-1ᴬ : Set
Lem-1ᴬ = ∀ {Γ s Γ′ s′ t₀ t₁ t₂}
       → Γ ∣ s ⊢ t₀ ⟶ᵉ t₁
       → [] ∣ Γ ∣ s ⊢ t₀ ⟶ˢᴬ t₂
       → Γ ∣ s ↣ Γ′ ∣ s′
       → ∃[ t₃ ] ((Γ ∣ s ⊢ t₂ ⟶ᵉ t₃) × ([] ∣ Γ′ ∣ s′ ⊢ t₁ ⟶ˢᴬ t₃))

¬Lem-1ᴬ : ¬ Lem-1ᴬ
¬Lem-1ᴬ lem with lem edge-e edge-s Ct-Refl
... | _ , e , s = no-join e s
```

## What this establishes

`¬Lem-1ᴬ`, `¬Thm-3ᴬ`, `¬Thm-11ᴬ`: with the bound kept by `Ms-FOp`, commutation, transitivity
elimination and "no abstraction above `⊤`" all fail for the machine relation, at an ill-formed
term. `Top≰ᴬlam` — the one-layer form of Theorem 11 — still holds. So under candidate A the
statements progress rests on have to be restated over `≤*wf`, where a promotion through a
consumed abstraction is only ever taken in a well-formed term, whose operand is below the bound;
the unfolding `x ⟶ᵉ α` and the promotion `x ⟶ˢ t` then join through `α ≤*wf t`, a chain and not a
step. The promotion `(λx≤t.x) v ⟶ˢ (λx≤t.t) v` that candidate A adds is the one the paper's
introduction names as the cause of the failure of Hutchins' commutativity proof and says MPSS
removes ("premature promotion"; v2 §1, the two diagrams). Candidate A is therefore Hutchins'
algorithmic system at this rule, and its transitivity elimination is the problem Hutchins left
open.
