# MPSS, candidate C: substituting away a parameter bound to its operand

The β-case of preservation for the stack-reading judgements of `MPSS/StackWf`. `Wc-FOp` checks the
body of a consumed abstraction under `x ≡ δ`; the reduct is the body with `δ` substituted. So what
is needed is substitution for a name bound by an **equivalence** entry, by its own definition —
v1's Lemma B.5 (`PSS/Substitution`, `wf-subst`) with `≡` in place of `≤`. No statement about
`δ` against a bound is involved, which is where the printed Lemma 7 needed Conjecture 8.

The machine relation under this substitution is `MPSS/SubstEqvS`. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfSubst where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.Subtyping
open import MPSS.StackWf
open import MPSS.Rename using (substCtx; substStack; substStack-id; x∉-w)
open import MPSS.SubstEqv using (prevalid-subst≡; ∈-mid; ∈-sub≡)
open import MPSS.SubstEqvS using (mid-lc; mid-fv; ⊲-subst≡)
open import PSS.Syntax using (subst-open; subst-fvar-≢; subst-intro; subst-fresh; ∉-tail)
```

## The three judgements under the substitution

```agda
wfˢ-subst≡   : ∀ (Δ : Ctx) {Γ s t v} x
             → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ t wfˢ
             → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) wfˢ
≤wfˢ-subst≡  : ∀ (Δ : Ctx) {Γ s a b v} x
             → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ a ≤wfˢ b
             → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (a [ x := v ]) ≤wfˢ (b [ x := v ])
≤*wfˢ-subst≡ : ∀ (Δ : Ctx) {Γ s a b v} x
             → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ a ≤*wfˢ b
             → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (a [ x := v ]) ≤*wfˢ (b [ x := v ])

wfˢ-subst≡ Δ x (Wc-Top pv) = Wc-Top (prevalid-subst≡ Δ (mid-lc Δ pv) (mid-fv Δ pv) pv)

wfˢ-subst≡ Δ {Γ} {s} {v = v} x (Wc-PrS {x = y} {t = b} pv m wb) = go
  where
    pv′ = prevalid-subst≡ Δ (mid-lc Δ pv) (mid-fv Δ pv) pv
    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ ((fvar y) [ x := v ]) wfˢ
    go with x ≟ y
    ... | yes refl with ∈-mid Δ (prevalid-ctx pv) m
    ...   | () , _
    go | no x≢y = Wc-PrS pv′ (∈-sub≡ Δ (prevalid-ctx pv) (λ eq → x≢y (sym eq)) m)
                         (wfˢ-subst≡ Δ x wb)

wfˢ-subst≡ Δ {Γ} {s} {v = v} x (Wc-PrE {x = y} {α = α} pv m wα) = go
  where
    pv′ = prevalid-subst≡ Δ (mid-lc Δ pv) (mid-fv Δ pv) pv
    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ ((fvar y) [ x := v ]) wfˢ
    go with x ≟ y
    ... | yes refl with ∈-mid Δ (prevalid-ctx pv) m
    ...   | refl , refl = subst (λ w → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ w wfˢ)
                                (subst-fresh {v} x v (x∉-w Δ (prevalid-ctx pv)))
                                (wfˢ-subst≡ Δ x wα)
    go | no x≢y = Wc-PrE pv′ (∈-sub≡ Δ (prevalid-ctx pv) (λ eq → x≢y (sym eq)) m)
                         (wfˢ-subst≡ Δ x wα)

wfˢ-subst≡ Δ {Γ} {v = v} x (Wc-Fun {t = t} {u = u} L F wt) =
  Wc-Fun (x ∷ L) body (wfˢ-subst≡ Δ x wt)
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ [] ⊢ ((u [ x := v ]) ^ fvar z) wfˢ
    body {z} z∉ = transport (wfˢ-subst≡ ((z , sub , t) ∷ Δ) x (F (∉-tail z∉)))
      where
        lv = mid-lc ((z , sub , t) ∷ Δ) (wfˢ⇒prevalid (F (∉-tail z∉)))
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        transport : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) wfˢ
                  → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) wfˢ
        transport h rewrite sym eq = h

wfˢ-subst≡ Δ {Γ} {v = v} x (Wc-FOp {s = s} {δ = δ} {t = t} {u = u} L F wt) =
  Wc-FOp (x ∷ L) body (wfˢ-subst≡ Δ x wt)
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , eqv , δ [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) wfˢ
    body {z} z∉ = transport (wfˢ-subst≡ ((z , eqv , δ) ∷ Δ) x (F (∉-tail z∉)))
      where
        lv = mid-lc ((z , eqv , δ) ∷ Δ) (wfˢ⇒prevalid (F (∉-tail z∉)))
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        transport : ((z , eqv , δ [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u ^ fvar z) [ x := v ]) wfˢ
                  → ((z , eqv , δ [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u [ x := v ]) ^ fvar z) wfˢ
        transport h rewrite sym eq = h

wfˢ-subst≡ Δ x (Wc-App d₁ d₂) = Wc-App (≤*wfˢ-subst≡ Δ x d₁) (≤*wfˢ-subst≡ Δ x d₂)

≤wfˢ-subst≡ Δ x (Wc-Rule wa wb d) =
  Wc-Rule (wfˢ-subst≡ Δ x wa) (wfˢ-subst≡ Δ x wb) (⊲-subst≡ Δ x d)

≤*wfˢ-subst≡ Δ x (Wc-Sub d)     = Wc-Sub (≤wfˢ-subst≡ Δ x d)
≤*wfˢ-subst≡ Δ x (Wc-Trs d₁ d₂) = Wc-Trs (≤*wfˢ-subst≡ Δ x d₁) (≤*wfˢ-subst≡ Δ x d₂)
```

## The head instance, in opened form

```agda
wfˢ-subst≡-head : ∀ {Γ s u v} x
                → x ∉ fv u → x ∉ fvStack s
                → ((x , eqv , v) ∷ Γ) ∣ s ⊢ (u ^ fvar x) wfˢ
                → Γ ∣ s ⊢ (u ^ v) wfˢ
wfˢ-subst≡-head {Γ} {s} {u} {v} x x∉u x∉s w =
  subst (λ σ → Γ ∣ σ ⊢ (u ^ v) wfˢ) (substStack-id x v s x∉s) step
  where
    lv = mid-lc [] (wfˢ⇒prevalid w)
    step : Γ ∣ (substStack x v s) ⊢ (u ^ v) wfˢ
    step = subst (λ q → Γ ∣ (substStack x v s) ⊢ q wfˢ)
                 (sym (subst-intro {u} lv x x∉u)) (wfˢ-subst≡ [] x w)
```

## What this establishes

`wfˢ-subst≡`, `≤wfˢ-subst≡`, `≤*wfˢ-subst≡`: the three judgements of candidate C are preserved when
a name bound by `x ≡ v` is replaced by `v`, over a context split, with nothing assumed; and
`wfˢ-subst≡-head`, the form the β-case of preservation consumes. The `Wc-PrE` case on `x` itself
is where the premise "the annotation is well-formed at the same stack" is used: the variable's
derivation already contains one for `v`.
