# The β defect survives restriction to well-formed terms

`MPSS/BetaScope` refutes v2's Proposition 17 with a term that is not well-formed, which leaves
open the charitable reading that the proposition is meant only for the well-formed terms its uses
in Lemma 6 and Theorem 5 supply. This module closes that reading: the counterexample can be made
**well-formed**.

With `T = λz≤Top.Top` and `y ≤ λq≤T.Top` in the context, the redex

> `R = (λx≤T. y x) T`

is well-formed, steps operationally to `y T`, and has no equivalence step to `y T`. `Me-App`
cannot produce it, since an abstraction never equivalence-reduces to a variable; `Me-Bet` cannot,
since contracting requires the body `y x` to reduce in a context that does not bind `x`, and
`Me-App` would push `x` onto the stack against `Pv-Sta`.

So the proofs of Lemma 6 (evaluation preserves well-formedness) and Theorem 5 (preservation),
both of which invoke Proposition 17 on well-formed terms, rest on a step that fails for terms of
exactly the kind they range over.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.BetaScopeWf where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import MPSS.WellFormed
open import PSS.Reduction using (_↦_; E-App)
open import PSS.Syntax using (bvar)
```

## The terms

```agda
T F Body A R : Tm
T    = lam Top Top                  -- λz≤Top. Top
F    = lam T Top                    -- λq≤T. Top
Body = app (fvar 0) (bvar 0)        -- y x
A    = lam T Body                   -- λx≤T. y x
R    = app A T                      -- (λx≤T. y x) T

Γ₀ : Ctx
Γ₀ = (0 , sub , F) ∷ []
```

Local closure and prevalidity.

```agda
lc-T : LC T
lc-T = lc-lam [] lc-Top (λ _ → lc-Top)

lc-F : LC F
lc-F = lc-lam [] lc-T (λ _ → lc-Top)

pv₀ : Γ₀ prevalid
pv₀ = Pv-Ctx Pv-Emp (λ ()) lc-F (λ ())
```

## The terms are well-formed

```agda
Top-wf : ∀ {Γ} → Γ prevalid → Γ ⊢ Top wf
Top-wf = Wf-Top

T-wf : ∀ {Γ} → Γ prevalid → Γ ⊢ T wf
T-wf {Γ} pv = Wf-Fun (dom Γ) (λ {z} z∉ → Wf-Top (Pv-Ctx pv z∉ lc-Top (λ ())))
                     (Wf-Top pv)

F-wf : ∀ {Γ} → Γ prevalid → fv T ⊑ dom Γ → Γ ⊢ F wf
F-wf {Γ} pv fvT = Wf-Fun (dom Γ) (λ {z} z∉ → Wf-Top (Pv-Ctx pv z∉ lc-T fvT))
                         (T-wf pv)
```

`T` is a well-subtype of itself, and of `λ_≤Top.Top` — the shape `Wf-App` asks for.

```agda
T≤*T : ∀ {Γ} → Γ prevalid → Γ ⊢ T ≤*wf T
T≤*T pv = Ws-Sub (T-wf pv) (Ws-Rfl pv) (T-wf pv)
```

`y` promotes to `F = λq≤T.Top`, which is exactly a function type with annotation `T`.

```agda
y-wf : Γ₀ ⊢ fvar 0 wf
y-wf = Wf-PrS pv₀ (here refl)

y≤*F : Γ₀ ⊢ fvar 0 ≤*wf F
y≤*F = Ws-Sub y-wf
              (Ws-Lf2 y-wf (Ms-Pro (Pv-Nil pv₀) (here refl)) (F-wf pv₀ (λ ()))
                      (Ws-Rfl pv₀))
              (F-wf pv₀ (λ ()))
```

The body `y x`, under `x ≤ T`, is well-formed: the operator is below a function type whose
annotation is `T`, and the parameter is below `T` by promotion.

```agda
body-wf : ∀ {x} → x ∉ dom Γ₀ → ((x , sub , T) ∷ Γ₀) ⊢ (Body ^ fvar x) wf
body-wf {x} x∉ = Wf-App op arg
  where
    pvx : ((x , sub , T) ∷ Γ₀) prevalid
    pvx = Pv-Ctx pv₀ x∉ lc-T (λ ())

    y-wfx : ((x , sub , T) ∷ Γ₀) ⊢ fvar 0 wf
    y-wfx = Wf-PrS pvx (there (here refl))

    op : ((x , sub , T) ∷ Γ₀) ⊢ fvar 0 ≤*wf lam T Top
    op = Ws-Sub y-wfx
                (Ws-Lf2 y-wfx (Ms-Pro (Pv-Nil pvx) (there (here refl)))
                        (F-wf pvx (λ ())) (Ws-Rfl pvx))
                (F-wf pvx (λ ()))

    x-wf : ((x , sub , T) ∷ Γ₀) ⊢ fvar x wf
    x-wf = Wf-PrS pvx (here refl)

    arg : ((x , sub , T) ∷ Γ₀) ⊢ fvar x ≤*wf T
    arg = Ws-Sub x-wf
                 (Ws-Lf2 x-wf (Ms-Pro (Pv-Nil pvx) (here refl)) (T-wf pvx)
                         (Ws-Rfl pvx))
                 (T-wf pvx)

A-wf : Γ₀ ⊢ A wf
A-wf = Wf-Fun (dom Γ₀) (λ {x} x∉ → body-wf x∉) (T-wf pv₀)
```

The abstraction promotes to `λx≤T.Top`, since its body promotes to `Top`, so the application is
well-formed.

```agda
A≤*fun : Γ₀ ⊢ A ≤*wf lam T Top
A≤*fun = Ws-Sub A-wf (Ws-Lf2 A-wf step (F-wf pv₀ (λ ())) (Ws-Rfl pv₀)) (F-wf pv₀ (λ ()))
  where
    step : Γ₀ ∣ [] ⊢ A ⟶ˢ lam T Top
    step = Ms-Fun {u' = Top} (dom Γ₀)
                  (λ {x} x∉ → Ms-Top (Pv-Nil (Pv-Ctx pv₀ x∉ lc-T (λ ()))))

R-wf : Γ₀ ⊢ R wf
R-wf = Wf-App A≤*fun (T≤*T pv₀)
```

## It steps, operationally

```agda
lc-A : LC A
lc-A = lc-lam [] lc-T (λ _ → lc-app lc-fvar lc-fvar)

R↦ : R ↦ app (fvar 0) T
R↦ = E-App lc-A lc-T
```

## But no equivalence step reaches the contractum

An abstraction never equivalence-reduces to a variable, which kills `Me-App`; and contracting by
`Me-Bet` needs the body to reduce with its parameter unbound, which `Pv-Sta` forbids.

```agda
A-not-var : ∀ {Γ s x} → ¬ (Γ ∣ s ⊢ A ⟶ᵉ fvar x)
A-not-var ()

body-stuck : ∀ {x w} → x ∉ dom Γ₀ → Γ₀ ∣ [] ⊢ (Body ^ fvar x) ⟶ᵉ w → ⊥
body-stuck x∉ (Me-App d _) with ⟶ᵉ-prevalid d
... | Pv-Sta _ _ f = x∉ (f (here refl))

no-step′ : ∀ {w} → Γ₀ ∣ [] ⊢ R ⟶ᵉ w → w ≢ app (fvar 0) T
no-step′ (Me-App d _)   refl = A-not-var d
no-step′ (Me-Bet L F e) _    = body-stuck x∉Γ (F x∉L)
  where
    x∉Γ : fresh (dom Γ₀ ++ L) ∉ dom Γ₀
    x∉Γ = ∉-++ˡ (fresh-∉ (dom Γ₀ ++ L))

    x∉L : fresh (dom Γ₀ ++ L) ∉ L
    x∉L = ∉-++ʳ (dom Γ₀) (fresh-∉ (dom Γ₀ ++ L))

no-step : ¬ (Γ₀ ∣ [] ⊢ R ⟶ᵉ app (fvar 0) T)
no-step d = no-step′ d refl
```

## What this establishes

The counterexample to Proposition 17 can be made **well-formed**, so the proposition fails on
exactly the terms Lemma 6 and Theorem 5 range over. Restricting the proposition to well-formed
terms does not repair it, and the proofs that invoke it are broken rather than merely imprecise.
