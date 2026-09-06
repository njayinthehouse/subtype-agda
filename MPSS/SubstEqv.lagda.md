# MPSS: reduction under substitution for an equivalence-bound variable — Lemma 32 as printed

v2's Lemma 32:

> If `Γ, x ≡ v, Γ′; s ⊢ u ⟶≡ u′` and `Γ; nil ⊢ v ⟶≡ v′`, then
> `Γ, Γ′[x\v]; s[x\v] ⊢ u[x\v] ⟶≡ u′[x\v′]`.

`MPSS/Subst` proves reduction under substitution for a name the context does **not** bind — the
form the β-rule's unbound body premise needs, and the form `STATUS.md` records as "31, 32". The
printed Lemma 31 binds `x` by `≤`, and the printed Lemma 32 binds it by `≡`; the `Me-App`/`Me-Bet`
case of Lemma 2 uses Lemma 32 in exactly that bound form, on the body's join obtained under
`x ≡ v₂`. So the bound form is needed, and this module proves it.

The proof follows `MPSS/Subst` clause for clause. Two cases are new: `Me-Var` on `x` itself, where
`x[x\v] = v` and the substituted step `v ⟶≡ v′` is weakened and pushed into place; and `Me-Pro`
on `x`, where the annotation read is `v` itself (prevalidity binds `x` once), the premise
reduces `v`, and `v[x\v] = v` because `x` is not free in `v`. The bookkeeping lemmas differ from
`MPSS/Subst/Base`'s only in the context's shape.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.SubstEqv where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.StackPush using (pushᵉ)
open import MPSS.Weakening using (⟶ᵉ-weaken; dom-⊑)
open import MPSS.Rename using (substCtx; substStack; ∈-substCtx; x∉-domΔ; x∉-domΓ; x∉-boundΓ; x∉-w; substStack-id)
open import MPSS.Subst.Base using (dom-sub; ∈-dom-sub; dom-++)
open import MPSS.Strengthen using (dom-drop)
open import PSS.Syntax using (subst-open; subst-fvar-≢; subst-fresh; subst-lc; subst-intro; ∉-tail; ∉-++ˡ; ∉-++ʳ)
open import PSS.Promotion using (fv-subst)
```

## Bookkeeping

Scoping: a term scoped in the full context is, after substitution, scoped in the substituted
context without `x`.

```agda
⊑-subst≡ : ∀ (Δ : Ctx) {Γ v t} x
         → fv v ⊑ dom Γ → fv t ⊑ dom (Δ ++ (x , eqv , v) ∷ Γ)
         → fv (t [ x := v ]) ⊑ dom (substCtx x v Δ ++ Γ)
⊑-subst≡ Δ {Γ} {v} {t} x fvv fvt h with fv-subst x v t h
... | inj₁ (p , y≢x) = ∈-dom-sub Δ (dom-drop Δ y≢x (fvt p))
... | inj₂ p         = ∈-dom-sub Δ (subst (_ ∈_) (sym (dom-++ Δ Γ)) (∈-++⁺ʳ (dom Δ) (fvv p)))
```

Prevalidity.

```agda
prevalid-ctx-subst≡ : ∀ (Δ : Ctx) {Γ x v}
                    → LC v → fv v ⊑ dom Γ
                    → (Δ ++ (x , eqv , v) ∷ Γ) prevalid
                    → (substCtx x v Δ ++ Γ) prevalid
prevalid-ctx-subst≡ [] lv fvv pv = tail-prevalid pv
prevalid-ctx-subst≡ ((z , sub , t) ∷ Δ) {Γ} {x} {v} lv fvv (Pv-Ctx pv z∉ lt ft) =
  Pv-Ctx (prevalid-ctx-subst≡ Δ lv fvv pv)
         (λ h → z∉ (dom-⊑ Δ ((x , eqv , v) ∷ []) (subst (_ ∈_) (dom-sub Δ) h)))
         (subst-lc lt lv) (⊑-subst≡ Δ {t = t} x fvv ft)
prevalid-ctx-subst≡ ((z , eqv , t) ∷ Δ) {Γ} {x} {v} lv fvv (Pv-EqA pv z∉ lt ft) =
  Pv-EqA (prevalid-ctx-subst≡ Δ lv fvv pv)
         (λ h → z∉ (dom-⊑ Δ ((x , eqv , v) ∷ []) (subst (_ ∈_) (dom-sub Δ) h)))
         (subst-lc lt lv) (⊑-subst≡ Δ {t = t} x fvv ft)

prevalid-subst≡ : ∀ (Δ : Ctx) {Γ s x v}
                → LC v → fv v ⊑ dom Γ
                → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s prevalid
                → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) prevalid
prevalid-subst≡ Δ lv fvv (Pv-Nil pv) = Pv-Nil (prevalid-ctx-subst≡ Δ lv fvv pv)
prevalid-subst≡ Δ {x = x} lv fvv (Pv-Sta {α = α} pv lα fα) =
  Pv-Sta (prevalid-subst≡ Δ lv fvv pv) (subst-lc lα lv) (⊑-subst≡ Δ {t = α} x fvv fα)
```

Lookups. The entry for `x` is the one in the middle, since prevalidity binds a name once; any
other entry transfers with its bound substituted, which is the identity on `Γ`'s entries.

```agda
∈-mid : ∀ (Δ : Ctx) {Γ x a w b α}
      → (Δ ++ (x , a , w) ∷ Γ) prevalid
      → (x , b , α) ∈ (Δ ++ (x , a , w) ∷ Γ)
      → (b ≡ a) × (α ≡ w)
∈-mid Δ pv m with ∈-++⁻ Δ m
... | inj₁ p           = ⊥-elim (x∉-domΔ Δ pv (∈-dom p))
... | inj₂ (here refl) = refl , refl
... | inj₂ (there p)   = ⊥-elim (x∉-domΓ Δ pv (∈-dom p))

∈-sub≡ : ∀ (Δ : Ctx) {Γ x v y b t}
       → (Δ ++ (x , eqv , v) ∷ Γ) prevalid → y ≢ x
       → (y , b , t) ∈ (Δ ++ (x , eqv , v) ∷ Γ)
       → (y , b , t [ x := v ]) ∈ (substCtx x v Δ ++ Γ)
∈-sub≡ Δ {Γ} {x} {v} {t = t} pv y≢x m with ∈-++⁻ Δ m
... | inj₁ p           = ∈-++⁺ˡ (∈-substCtx x v Δ p)
... | inj₂ (here refl) = ⊥-elim (y≢x refl)
... | inj₂ (there p)   =
  subst (λ w → (_ , _ , w) ∈ (substCtx x v Δ ++ Γ))
        (sym (subst-fresh {t} x v (x∉-boundΓ Δ pv p)))
        (∈-++⁺ʳ (substCtx x v Δ) p)
```

## The lemma

```agda
⟶ᵉ-subst≡ : ∀ (Δ : Ctx) {Γ s t t′ v v′} x
          → LC v → LC v′ → fv v ⊑ dom Γ
          → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ t ⟶ᵉ t′
          → Γ ∣ [] ⊢ v ⟶ᵉ v′
          → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) ⟶ᵉ (t′ [ x := v′ ])
```

`Me-Var` on `x` is the substituted step itself, weakened into the substituted context and
pushed under the stack.

```agda
⟶ᵉ-subst≡ Δ {Γ} {s} {v = v} {v′ = v′} x lv lv′ fvv (Me-Var {x = y} pv) sv = go
  where
    pv′ = prevalid-subst≡ Δ lv fvv pv
    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
           ⊢ ((fvar y) [ x := v ]) ⟶ᵉ ((fvar y) [ x := v′ ])
    go with x ≟ y
    ... | yes _ = pushᵉ {s = []} {s′ = substStack x v s}
                        (⟶ᵉ-weaken [] (substCtx x v Δ) (Pv-Nil (prevalid-ctx pv′)) sv) pv′
    ... | no  _ = Me-Var pv′

⟶ᵉ-subst≡ Δ x lv lv′ fvv (Me-Top pv) sv = Me-Top (prevalid-subst≡ Δ lv fvv pv)
⟶ᵉ-subst≡ Δ x lv lv′ fvv (Me-TAp pv) sv = Me-TAp (prevalid-subst≡ Δ lv fvv pv)
```

`Me-Pro` on `x` reads `v` and reduces it; the induction hypothesis substitutes into that, and
the substitution is the identity on `v`.

```agda
⟶ᵉ-subst≡ Δ {Γ} {s} {v = v} {v′ = v′} x lv lv′ fvv
          (Me-Pro {x = y} {α = α} {α' = β} pv m d) sv = go
  where
    pv′ = prevalid-subst≡ Δ lv fvv pv

    inner : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
              ⊢ (α [ x := v ]) ⟶ᵉ (β [ x := v′ ])
    inner = ⟶ᵉ-subst≡ Δ x lv lv′ fvv d sv

    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
           ⊢ ((fvar y) [ x := v ]) ⟶ᵉ (β [ x := v′ ])
    go with x ≟ y
    ... | yes refl with ∈-mid Δ (prevalid-ctx pv) m
    ...   | refl , refl = subst (λ w → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ w ⟶ᵉ (β [ x := v′ ]))
                                (subst-fresh {v} x v (x∉-w Δ (prevalid-ctx pv))) inner
    go | no x≢y = Me-Pro pv′ (∈-sub≡ Δ (prevalid-ctx pv) (λ eq → x≢y (sym eq)) m) inner

⟶ᵉ-subst≡ Δ x lv lv′ fvv (Me-App d e) sv =
  Me-App (⟶ᵉ-subst≡ Δ x lv lv′ fvv d sv) (⟶ᵉ-subst≡ Δ x lv lv′ fvv e sv)
```

The binder cases extend `Δ` with the substituted annotation.

```agda
⟶ᵉ-subst≡ Δ {Γ} {v = v} {v′ = v′} x lv lv′ fvv
          (Me-Fun {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv =
  Me-Fun (x ∷ L) (⟶ᵉ-subst≡ Δ x lv lv′ fvv d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-subst≡ ((z , sub , t) ∷ Δ) x lv lv′ fvv (F (∉-tail z∉)) sv)
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

⟶ᵉ-subst≡ Δ {Γ} {v = v} {v′ = v′} x lv lv′ fvv
          (Me-FOp {s = s} {α = α} {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv =
  Me-FOp (x ∷ L) (⟶ᵉ-subst≡ Δ x lv lv′ fvv d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-subst≡ ((z , eqv , α) ∷ Δ) x lv lv′ fvv (F (∉-tail z∉)) sv)
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h
```

The β case, as in `MPSS/Subst`.

```agda
⟶ᵉ-subst≡ Δ {Γ} {s} {v = v} {v′ = v′} x lv lv′ fvv
          (Me-Bet {t = t} {u = u} {u' = u′} {v = w} {v' = w′} L F e) sv =
  transport (Me-Bet {t = t [ x := v ]} {u [ x := v ]} {u′ [ x := v′ ]}
                    {w [ x := v ]} {w′ [ x := v′ ]}
                    (x ∷ L) body
                    (⟶ᵉ-subst≡ Δ x lv lv′ fvv e sv))
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = go (⟶ᵉ-subst≡ Δ x lv lv′ fvv (F (∉-tail z∉)) sv)
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
               ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ ((u′ ^ fvar z) [ x := v′ ])
           → (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
               ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
        go h rewrite sym eq | sym eq′ = h

    eqβ : ((u′ ^ w′) [ x := v′ ]) ≡ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
    eqβ = subst-open lv′ 0 w′ u′ x

    transport : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                  ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶ᵉ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
              → (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                  ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶ᵉ ((u′ ^ w′) [ x := v′ ])
    transport h rewrite eqβ = h
```

## At the head

The form the diamond's `Me-App`/`Me-Bet` case uses: the split is trivial, the stack does not
mention `x`, and the body is in opened form.

```agda
⟶ᵉ-subst≡-head : ∀ {Γ s u u′ v v′} x
               → x ∉ fv u → x ∉ fv u′ → x ∉ fvStack s → LC v → LC v′ → fv v ⊑ dom Γ
               → ((x , eqv , v) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ᵉ (u′ ^ fvar x)
               → Γ ∣ [] ⊢ v ⟶ᵉ v′
               → Γ ∣ s ⊢ (u ^ v) ⟶ᵉ (u′ ^ v′)
⟶ᵉ-subst≡-head {Γ} {s} {u} {u′} {v} {v′} x x∉u x∉u′ x∉s lv lv′ fvv d sv
  rewrite subst-intro {u} lv x x∉u | subst-intro {u′} lv′ x x∉u′
  = transport (⟶ᵉ-subst≡ [] x lv lv′ fvv d sv)
  where
    transport : Γ ∣ (substStack x v s) ⊢ ((u ^ fvar x) [ x := v ]) ⟶ᵉ ((u′ ^ fvar x) [ x := v′ ])
              → Γ ∣ s ⊢ ((u ^ fvar x) [ x := v ]) ⟶ᵉ ((u′ ^ fvar x) [ x := v′ ])
    transport h rewrite substStack-id x v s x∉s = h
```

## What this establishes

`⟶ᵉ-subst≡`: v2's Lemma 32 in its printed, equivalence-bound form, over a context split, with
the substituted term reduced on the right as the simultaneous rules need. `⟶ᵉ-subst≡-head` is
the instance at the head of the context in opened form — the shape the `Me-App`/`Me-Bet` case of
the diamond consumes on the `Me-Bet` side.

The relation to `MPSS/Subst`: that module's `⟶ᵉ-subst` substitutes for a name the context does
not bind, which is what `Me-Bet`'s unbound body premise calls for; `STATUS.md` records it as
Lemmas 31 and 32, but neither printed lemma is that statement. Lemma 31 binds the name by `≤`
and Lemma 32 by `≡`. This module supplies 32; 31 in its printed form is not needed by the
diamond and is not proved here.
