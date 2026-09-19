# MPSS: promotion and machine subtyping under substitution for an equivalence-bound variable

`MPSS/SubstEqv` proves v2's Lemma 32: equivalence reduction `⟶ᵉ` survives substituting away a
name bound by an equivalence entry `x ≡ v`. This module proves the same for the promotion
relation `⟶ˢ` and for the machine relation `⊲` in both of its modes:

> If `Γ, x ≡ v, Γ′; s ⊢ a ⟶≤ b`, then `Γ, Γ′[x\v]; s[x\v] ⊢ a[x\v] ⟶≤ b[x\v]`.
>
> If `Γ, x ≡ v, Γ′; s ⊢ a ⊲ b`, then `Γ, Γ′[x\v]; s[x\v] ⊢ a[x\v] ⊲ b[x\v]`.

Each step maps to a single step; no chain is needed. The contrast is with `MPSS/Lemma2930`, where
the removed name is bound by `≤` and `Ms-Pro` on that name is the case that does not transfer.
Here `Ms-Pro` cannot fire on `x` at all: it reads a subtype entry, and prevalidity binds `x` once,
by `≡`. `Ms-Pro` on any other name reads an entry whose bound is substituted along with everything
else. `Ms-Equ` is `MPSS/SubstEqv`'s lemma taken at the reflexive step `v ⟶ᵉ v`, so the same `v`
is substituted on both sides.

The side conditions `LC v` and `fv v ⊑ dom Γ` of `⟶ᵉ-subst≡` are not hypotheses here: both are
read off the prevalidity of the context, which every derivation carries.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.SubstEqvS where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Rename using (substCtx; substStack; prevalid-suffix; substStack-id)
open import MPSS.SubstEqv using (prevalid-subst≡; ∈-mid; ∈-sub≡; ⟶ᵉ-subst≡)
open import PSS.Syntax using (subst-open; subst-fvar-≢; subst-intro; ∉-tail)
```

## What prevalidity says about the removed entry

```agda
mid-lc : ∀ (Δ : Ctx) {Γ s x v} → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s prevalid → LC v
mid-lc Δ pv = head-lc (prevalid-suffix Δ (prevalid-ctx pv))

mid-fv : ∀ (Δ : Ctx) {Γ s x v} → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s prevalid → fv v ⊑ dom Γ
mid-fv Δ pv = head-fv (prevalid-suffix Δ (prevalid-ctx pv))

mid-refl : ∀ (Δ : Ctx) {Γ s x v} → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s prevalid → Γ ∣ [] ⊢ v ⟶ᵉ v
mid-refl Δ pv =
  ⟶ᵉ-refl (Pv-Nil (tail-prevalid (prevalid-suffix Δ (prevalid-ctx pv)))) (mid-lc Δ pv) (mid-fv Δ pv)
```

## Equivalence reduction, with the same term substituted on both sides

`⟶ᵉ-subst≡` substitutes `v` on the left and a reduct `v′` on the right. Taking the reflexive
step for `v` gives the form `Ms-Equ`, `As-Left-2` and `As-Right` need.

```agda
⟶ᵉ-subst≡-same : ∀ (Δ : Ctx) {Γ s t t′ v} x
               → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ t ⟶ᵉ t′
               → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) ⟶ᵉ (t′ [ x := v ])
⟶ᵉ-subst≡-same Δ x d =
  ⟶ᵉ-subst≡ Δ x (mid-lc Δ pv) (mid-lc Δ pv) (mid-fv Δ pv) d (mid-refl Δ pv)
  where pv = ⟶ᵉ-prevalid d
```

## Promotion

```agda
⟶ˢ-subst≡ : ∀ (Δ : Ctx) {Γ s a b v} x
          → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ a ⟶ˢ b
          → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (a [ x := v ]) ⟶ˢ (b [ x := v ])
```

`Ms-Pro` on `x` is impossible: the one entry for `x` is the equivalence entry. On another name
the entry transfers with its bound substituted.

```agda
⟶ˢ-subst≡ Δ {Γ} {s} {v = v} x (Ms-Pro {x = y} {t = t} pv m) = go (x ≟ y)
  where
    pv′ = prevalid-subst≡ Δ (mid-lc Δ pv) (mid-fv Δ pv) pv

    absurd : ∀ {A : Set} → sub ≡ eqv → A
    absurd ()

    go : Dec (x ≡ y)
       → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ ((fvar y) [ x := v ]) ⟶ˢ (t [ x := v ])
    go (yes refl) = absurd (proj₁ (∈-mid Δ (prevalid-ctx pv) m))
    go (no q) rewrite subst-fvar-≢ {x} {y} v q =
      Ms-Pro pv′ (∈-sub≡ Δ (prevalid-ctx pv) (λ p → q (sym p)) m)

⟶ˢ-subst≡ Δ x (Ms-Top pv)   = Ms-Top (prevalid-subst≡ Δ (mid-lc Δ pv) (mid-fv Δ pv) pv)
⟶ˢ-subst≡ Δ x (Ms-Equ pv e) =
  Ms-Equ (prevalid-subst≡ Δ (mid-lc Δ pv) (mid-fv Δ pv) pv) (⟶ᵉ-subst≡-same Δ x e)
⟶ˢ-subst≡ Δ x (Ms-App d)    = Ms-App (⟶ˢ-subst≡ Δ x d)
```

The binder cases extend `Δ` with the entry for the binder's name, as in `MPSS/SubstEqv`.

```agda
⟶ˢ-subst≡ Δ {Γ} {v = v} x (Ms-Fun {t = t} {u = u} {u' = u′} L F) = Ms-Fun (x ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ ((u′ [ x := v ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ-subst≡ ((z , sub , t) ∷ Δ) x (F (∉-tail z∉)))
      where
        lv = mid-lc ((z , sub , t) ∷ Δ) (⟶ˢ-prevalid (F (∉-tail z∉)))

        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v ])) (subst-fvar-≢ v x≢z))

        transport : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ˢ ((u′ ^ fvar z) [ x := v ])
                  → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ ((u′ [ x := v ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

⟶ˢ-subst≡ Δ {Γ} {v = v} x (Ms-FOp {s = s} {α = α} {t = t} {u = u} {u' = u′} L F) =
  Ms-FOp (x ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ ((u′ [ x := v ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ-subst≡ ((z , eqv , α) ∷ Δ) x (F (∉-tail z∉)))
      where
        lv = mid-lc ((z , eqv , α) ∷ Δ) (⟶ˢ-prevalid (F (∉-tail z∉)))

        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v ])) (subst-fvar-≢ v x≢z))

        transport : ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ˢ ((u′ ^ fvar z) [ x := v ])
                  → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ ((u′ [ x := v ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h
```

## The machine relation

Rule for rule, in both modes.

```agda
⊲-subst≡ : ∀ (Δ : Ctx) {Γ s a b v m} x
         → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ a ⊲[ m ] b
         → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (a [ x := v ]) ⊲[ m ] (b [ x := v ])
⊲-subst≡ Δ x (As-Refl pv)     = As-Refl (prevalid-subst≡ Δ (mid-lc Δ pv) (mid-fv Δ pv) pv)
⊲-subst≡ Δ x (As-Left-1 st d) = As-Left-1 (⟶ˢ-subst≡ Δ x st) (⊲-subst≡ Δ x d)
⊲-subst≡ Δ x (As-Left-2 st d) = As-Left-2 (⟶ᵉ-subst≡-same Δ x st) (⊲-subst≡ Δ x d)
⊲-subst≡ Δ x (As-Right d st)  = As-Right (⊲-subst≡ Δ x d) (⟶ᵉ-subst≡-same Δ x st)
```

## At the head

The split is trivial, the stack does not mention `x`, and the two sides are in opened form.
Freshness of `x` for `Γ` is not a hypothesis: prevalidity of `(x , eqv , v) ∷ Γ` already gives it.

```agda
⟶ˢ-subst≡-head : ∀ {Γ s u u′ v} x
               → x ∉ fv u → x ∉ fv u′ → x ∉ fvStack s
               → ((x , eqv , v) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ˢ (u′ ^ fvar x)
               → Γ ∣ s ⊢ (u ^ v) ⟶ˢ (u′ ^ v)
⟶ˢ-subst≡-head {Γ} {s} {u} {u′} {v} x x∉u x∉u′ x∉s d
  rewrite subst-intro {u} (mid-lc [] (⟶ˢ-prevalid d)) x x∉u
        | subst-intro {u′} (mid-lc [] (⟶ˢ-prevalid d)) x x∉u′
  = transport (⟶ˢ-subst≡ [] x d)
  where
    transport : Γ ∣ (substStack x v s) ⊢ ((u ^ fvar x) [ x := v ]) ⟶ˢ ((u′ ^ fvar x) [ x := v ])
              → Γ ∣ s ⊢ ((u ^ fvar x) [ x := v ]) ⟶ˢ ((u′ ^ fvar x) [ x := v ])
    transport h rewrite substStack-id x v s x∉s = h

⊲-subst≡-head : ∀ {Γ s u u′ v m} x
              → x ∉ fv u → x ∉ fv u′ → x ∉ fvStack s
              → ((x , eqv , v) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⊲[ m ] (u′ ^ fvar x)
              → Γ ∣ s ⊢ (u ^ v) ⊲[ m ] (u′ ^ v)
⊲-subst≡-head {Γ} {s} {u} {u′} {v} {m} x x∉u x∉u′ x∉s d
  rewrite subst-intro {u} (mid-lc [] (chain-prevalid d)) x x∉u
        | subst-intro {u′} (mid-lc [] (chain-prevalid d)) x x∉u′
  = transport (⊲-subst≡ [] x d)
  where
    transport : Γ ∣ (substStack x v s) ⊢ ((u ^ fvar x) [ x := v ]) ⊲[ m ] ((u′ ^ fvar x) [ x := v ])
              → Γ ∣ s ⊢ ((u ^ fvar x) [ x := v ]) ⊲[ m ] ((u′ ^ fvar x) [ x := v ])
    transport h rewrite substStack-id x v s x∉s = h
```

## What this establishes

`⟶ˢ-subst≡` and `⊲-subst≡`: promotion and the machine relation, in both modes, are preserved
when a name bound by `x ≡ v` is replaced by `v` throughout the context to its left, the stack and
the two terms. Every step maps to one step of the same rule, so derivations keep their shape and
length. The only hypothesis is the derivation itself; local closure and scoping of `v` come from
the prevalidity it carries. `⟶ᵉ-subst≡-same` is `MPSS/SubstEqv`'s `⟶ᵉ-subst≡` at the reflexive
step for `v`.

`⟶ˢ-subst≡-head` and `⊲-subst≡-head` are the instances at the head of the context in opened
form: from a derivation between `u ^ fvar x` and `u′ ^ fvar x` under `x ≡ v`, with `x` fresh for
`u`, `u′` and the stack, a derivation between `u ^ v` and `u′ ^ v` in the context without `x`.
That is the shape the body of a β-step has after `Ms-FOp` or `Me-FOp` has bound the parameter to
the popped operand.

The relation to `MPSS/Lemma2930`: there the removed name is bound by `≤`, `Ms-Pro` on it yields
its annotation, and the statement holds only off that pattern. Here the removed name is bound by
`≡`, `Ms-Pro` does not apply to it, and the statement holds for every derivation.
