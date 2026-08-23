# System λ⊲: Lemma B.5 — substitution preserves well-formedness

The last input to Lemma B.4, and the one the `E-App` case of reduction needs: contracting a
redex substitutes the operand for the formal parameter, and the result must still be
well-formed.

The subtyping part goes through Lemma 2.4 again — substitute along the promotion chain by
Lemma B.9 and along the equivalence chain by Lemma B.10, then recompose.

```agda
{-# OPTIONS --safe #-}

module PSS.Substitution where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed
open import PSS.Equivalence
open import PSS.Promotion
open import PSS.Scope
open import PSS.Commutation
open import PSS.Transitivity using (wf⇒lc)
open import PSS.Narrowing
```

## Substitution along chains

```agda
⟶≡*-subst : ∀ {t t' v} x → LC v → t ⟶≡* t' → (t [ x := v ]) ⟶≡* (t' [ x := v ])
⟶≡*-subst x lv εₑ        = εₑ
⟶≡*-subst x lv (e ◅ₑ c)  = ⟶≡-subst x lv lv e (⟶≡-refl lv) ◅ₑ ⟶≡*-subst x lv c

⟶≤*-subst : ∀ {Γ s u w v} x (Δ : Ctx)
          → LC v → x ∉ fv v → fv v ⊑ dom Γ
          → (Δ ++ (x , v) ∷ Γ) ∣ s ⊢ u ⟶≤* w
          → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (u [ x := v ]) ⟶≤* (w [ x := v ])
⟶≤*-subst x Δ lv x∉v fvv εₚ        = εₚ
⟶≤*-subst x Δ lv x∉v fvv (st ◅ₚ c) =
  ⟶≤-subst x Δ lv x∉v fvv st ◅ₚ ⟶≤*-subst x Δ lv x∉v fvv c
```

## Substitution in a subtyping derivation

```agda
⊲-subst : ∀ {Γ s u t v} x (Δ : Ctx)
        → LC v → x ∉ fv v → fv v ⊑ dom Γ
        → (Δ ++ (x , v) ∷ Γ) ∣ s ⊢ u ≤ t
        → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (u [ x := v ]) ≤ (t [ x := v ])
⊲-subst x Δ lv x∉v fvv d with ⊲⇒diag d
... | w , chain , c =
      diag⇒⊲ (prevalid-subst x Δ lv fvv (chain-prevalid d))
             (⟶≤*-subst x Δ lv x∉v fvv chain)
             (⟶≡*-subst x lv c)
  where
    chain-prevalid : ∀ {Γ₀ s₀ a b} → Γ₀ ∣ s₀ ⊢ a ≤ b → Γ₀ ∣ s₀ prevalid
    chain-prevalid (As-Refl pv)     = pv
    chain-prevalid (As-Left-1 st _) = ⟶≤-prevalid st
    chain-prevalid (As-Right e _)   = chain-prevalid e
```

## Lemma B.5

By structural induction on the three well-formedness judgements together. `W-Var` splits on
where the variable's binding sits: it may be the substituted one, in which case the result is
the substituted term itself; it may be later, in which case its bound is substituted too; or it
may be earlier, in which case the bound cannot mention `x` and is untouched.

```agda
wf-subst   : ∀ {Γ s u v} x (Δ : Ctx)
           → LC v → x ∉ fv v → fv v ⊑ dom Γ
           → (Δ ++ (x , v) ∷ Γ) ∣ s ⊢ u wf
           → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (u [ x := v ]) wf
≤wf-subst  : ∀ {Γ s u t v} x (Δ : Ctx)
           → LC v → x ∉ fv v → fv v ⊑ dom Γ
           → (Δ ++ (x , v) ∷ Γ) ∣ s ⊢ u ≤wf t
           → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (u [ x := v ]) ≤wf (t [ x := v ])
≤*wf-subst : ∀ {Γ s u t v} x (Δ : Ctx)
           → LC v → x ∉ fv v → fv v ⊑ dom Γ
           → (Δ ++ (x , v) ∷ Γ) ∣ s ⊢ u ≤*wf t
           → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (u [ x := v ]) ≤*wf (t [ x := v ])

wf-subst x Δ lv x∉v fvv (W-Top pv) = W-Top (prevalid-subst x Δ lv fvv pv)

wf-subst {Γ} {s} {v = v} x Δ lv x∉v fvv (W-Var {_} {_} {y} {t} pv mem wt)
  with ∈-++⁻ Δ mem
... | inj₁ m = var-Δ
  where
    x≢y : x ≢ y
    x≢y p = x∉-domΔ Δ pv (subst (_∈ dom Δ) (sym p) (∈-dom-of m))
      where
        ∈-dom-of : ∀ {Δ' w u} → (w , u) ∈ Δ' → w ∈ dom Δ'
        ∈-dom-of (here refl) = here refl
        ∈-dom-of (there q)   = there (∈-dom-of q)

    var-Δ : (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ ((fvar y) [ x := v ]) wf
    var-Δ rewrite subst-fvar-≢ {x} {y} v x≢y =
      W-Var (prevalid-subst x Δ lv fvv pv)
            (∈-++⁺ˡ (∈-substCtx x v Δ m))
            (wf-subst x Δ lv x∉v fvv wt)

wf-subst {Γ} {s} {v = v} x Δ lv x∉v fvv (W-Var {_} {_} {y} {t} pv mem wt)
    | inj₂ (here refl) = var-self
  where
    var-self : (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ ((fvar x) [ x := v ]) wf
    var-self rewrite subst-fvar-≡ {x} v =
      transport (wf-subst x Δ lv x∉v fvv wt)
      where
        transport : (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (v [ x := v ]) wf
                  → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ v wf
        transport h rewrite subst-fresh {v} x v x∉v = h

wf-subst {Γ} {s} {v = v} x Δ lv x∉v fvv (W-Var {_} {_} {y} {t} pv mem wt)
    | inj₂ (there m) = var-Γ
  where
    x≢y : x ≢ y
    x≢y p = x∉-domΓ Δ pv (subst (_∈ dom Γ) (sym p) (∈-dom-of m))
      where
        ∈-dom-of : ∀ {Γ' w u} → (w , u) ∈ Γ' → w ∈ dom Γ'
        ∈-dom-of (here refl) = here refl
        ∈-dom-of (there q)   = there (∈-dom-of q)

    transport : (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (t [ x := v ]) wf
              → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ t wf
    transport h rewrite subst-fresh {t} x v (x∉-boundΓ Δ pv m) = h

    var-Γ : (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ ((fvar y) [ x := v ]) wf
    var-Γ rewrite subst-fvar-≢ {x} {y} v x≢y =
      W-Var (prevalid-subst x Δ lv fvv pv)
            (∈-++⁺ʳ (substCtx x v Δ) m)
            (transport (wf-subst x Δ lv x∉v fvv wt))

wf-subst {Γ} {v = v} x Δ lv x∉v fvv (W-Fun {_} {t} {u} L F wa) =
  W-Fun (x ∷ L ++ fv v) body (wf-subst x Δ lv x∉v fvv wa)
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v)
         → ((y , t [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar y) wf
    body {y} y∉ = transport (wf-subst x ((y , t) ∷ Δ) lv x∉v fvv (F (∉-++ˡ (∉-tail y∉))))
      where
        x≢y : x ≢ y
        x≢y p = y∉ (here (sym p))

        eq : ((u ^ fvar y) [ x := v ]) ≡ ((u [ x := v ]) ^ fvar y)
        eq = trans (subst-open lv 0 (fvar y) u x)
                   (cong (λ q → openRec 0 q (u [ x := v ])) (subst-fvar-≢ v x≢y))

        transport : ((y , t [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ []
                      ⊢ ((u ^ fvar y) [ x := v ]) wf
                  → ((y , t [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar y) wf
        transport h rewrite sym eq = h

wf-subst {Γ} {v = v} x Δ lv x∉v fvv (W-FunOp {_} {s} {δ} {t} {u} L F wa) =
  W-FunOp (x ∷ L ++ fv v) body (wf-subst x Δ lv x∉v fvv wa)
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v)
         → ((y , δ [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ substStack x v s
             ⊢ ((u [ x := v ]) ^ fvar y) wf
    body {y} y∉ = transport (wf-subst x ((y , δ) ∷ Δ) lv x∉v fvv (F (∉-++ˡ (∉-tail y∉))))
      where
        x≢y : x ≢ y
        x≢y p = y∉ (here (sym p))

        eq : ((u ^ fvar y) [ x := v ]) ≡ ((u [ x := v ]) ^ fvar y)
        eq = trans (subst-open lv 0 (fvar y) u x)
                   (cong (λ q → openRec 0 q (u [ x := v ])) (subst-fvar-≢ v x≢y))

        transport : ((y , δ [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ substStack x v s
                      ⊢ ((u ^ fvar y) [ x := v ]) wf
                  → ((y , δ [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ substStack x v s
                      ⊢ ((u [ x := v ]) ^ fvar y) wf
        transport h rewrite sym eq = h

wf-subst x Δ lv x∉v fvv (W-App d₁ d₂) =
  W-App (≤*wf-subst x Δ lv x∉v fvv d₁) (≤*wf-subst x Δ lv x∉v fvv d₂)

≤wf-subst x Δ lv x∉v fvv (Wf-Rule wu wt d) =
  Wf-Rule (wf-subst x Δ lv x∉v fvv wu)
          (wf-subst x Δ lv x∉v fvv wt)
          (⊲-subst x Δ lv x∉v fvv d)

≤*wf-subst x Δ lv x∉v fvv (Wf-Sub d)          = Wf-Sub (≤wf-subst x Δ lv x∉v fvv d)
≤*wf-subst x Δ lv x∉v fvv (Wf-Trans d₁ d₂ wu) =
  Wf-Trans (≤*wf-subst x Δ lv x∉v fvv d₁)
           (≤*wf-subst x Δ lv x∉v fvv d₂)
           (wf-subst x Δ lv x∉v fvv wu)
```

## What this establishes

**Lemma B.5**, plus substitution in a subtyping derivation. With narrowing already in hand,
Lemma B.4 and Theorem 4.2 follow.
