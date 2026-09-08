# MPSS: substitution for a floating name, in the variant relation

`Me-Bet` reduces its body with the parameter unbound, so a chain of variant steps built from a
derivation must, at a `Me-Bet` node, combine a body step at an unbound name `x` with an operand
step into a step of the substituted terms. `MPSS/Subst` proves that for `⟶ᵉ` with the
substituend scoped in the context. Here the substituend may mention unbound names itself — the
body of an outer `Me-Bet` supplies such operands — and the lemma still holds, for a reason
prevalidity supplies: an unbound name never occurs in a pushed operand, in a binder annotation,
or in the stack, since all of those are scoped in the context's domain. So the context and the
stack are untouched by the substitution, and there is nothing to keep prevalid.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantSubst where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax using (subst-open; subst-fvar-≢; subst-fvar-≡; subst-fresh; ∉-++ˡ; ∉-tail)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-prevalid; ⟶ᵉ′-weaken)
open import MPSS.VariantPush using (pushᵉ′)
```

## The lemma

```agda
⟶ᵉ′-subst-float : ∀ {Γ s t t′ v v′} x → x ∉ dom Γ → LC v → LC v′
                → Γ ∣ s ⊢ t ⟶ᵉ′ t′ → Γ ∣ [] ⊢ v ⟶ᵉ′ v′
                → Γ ∣ s ⊢ (t [ x := v ]) ⟶ᵉ′ (t′ [ x := v′ ])

⟶ᵉ′-subst-float {Γ} {s} {v = v} {v′} x x∉ lv lv′ (Me-Var′ {x = y} pv) sv = go
  where
    go : Γ ∣ s ⊢ ((fvar y) [ x := v ]) ⟶ᵉ′ ((fvar y) [ x := v′ ])
    go with x ≟ y
    ... | yes _ = pushᵉ′ {s = []} {s′ = s} sv pv
    ... | no  _ = Me-Var′ pv

⟶ᵉ′-subst-float x x∉ lv lv′ (Me-Top′ pv) sv = Me-Top′ pv
⟶ᵉ′-subst-float x x∉ lv lv′ (Me-TAp′ pv) sv = Me-TAp′ pv
```

A promoted variable is bound, hence not `x`, and its annotation is scoped, hence untouched.

```agda
⟶ᵉ′-subst-float {Γ} {s} {v = v} {v′} x x∉ lv lv′ (Me-Pro′ {x = y} {α = α} {α' = β} pv m d) sv = go
  where
    x≢y : x ≢ y
    x≢y refl = x∉ (∈-dom m)

    x∉α : x ∉ fv α
    x∉α h = x∉ (prevalid-bound-fv (prevalid-ctx pv) m h)

    inner : Γ ∣ [] ⊢ α ⟶ᵉ′ (β [ x := v′ ])
    inner = subst (λ q → Γ ∣ [] ⊢ q ⟶ᵉ′ (β [ x := v′ ])) (subst-fresh {α} x v x∉α)
                  (⟶ᵉ′-subst-float x x∉ lv lv′ d sv)

    go : Γ ∣ s ⊢ ((fvar y) [ x := v ]) ⟶ᵉ′ (β [ x := v′ ])
    go rewrite subst-fvar-≢ {x} {y} v x≢y = Me-Pro′ pv m inner
```

A pushed operand is scoped, hence untouched, so the operator's premise keeps its stack.

```agda
⟶ᵉ′-subst-float {Γ} {s} {v = v} {v′} x x∉ lv lv′ (Me-App′ {u = u} {u' = u′} {v = w} {v' = w′} d e) sv = go
  where
    x∉w : x ∉ fv w
    x∉w h = x∉ (prevalid-head-fv (⟶ᵉ′-prevalid d) h)

    ih-e : Γ ∣ [] ⊢ w ⟶ᵉ′ (w′ [ x := v′ ])
    ih-e = subst (λ q → Γ ∣ [] ⊢ q ⟶ᵉ′ (w′ [ x := v′ ])) (subst-fresh {w} x v x∉w)
                 (⟶ᵉ′-subst-float x x∉ lv lv′ e sv)

    go : Γ ∣ s ⊢ (app (u [ x := v ]) (w [ x := v ])) ⟶ᵉ′ (app (u′ [ x := v′ ]) (w′ [ x := v′ ]))
    go rewrite subst-fresh {w} x v x∉w = Me-App′ (⟶ᵉ′-subst-float x x∉ lv lv′ d sv) ih-e
```

The β case: the body premise is at the same context, and substitution commutes with opening
because the substituted terms are locally closed.

```agda
⟶ᵉ′-subst-float {Γ} {s} {v = v} {v′} x x∉ lv lv′
                (Me-Bet′ {t = t} {u = u} {u' = u′} {v = w} {v' = w′} L F e) sv =
  transport (Me-Bet′ {t = t [ x := v ]} {u [ x := v ]} {u′ [ x := v′ ]}
                     {w [ x := v ]} {w′ [ x := v′ ]}
                     (x ∷ L) body (⟶ᵉ′-subst-float x x∉ lv lv′ e sv))
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → Γ ∣ s ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = go (⟶ᵉ′-subst-float x x∉ lv lv′ (F (∉-tail z∉)) sv)
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        go : Γ ∣ s ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ′ ((u′ ^ fvar z) [ x := v′ ])
           → Γ ∣ s ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
        go h rewrite sym eq | sym eq′ = h

    eqβ : ((u′ ^ w′) [ x := v′ ]) ≡ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
    eqβ = subst-open lv′ 0 w′ u′ x

    transport : Γ ∣ s ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶ᵉ′ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
              → Γ ∣ s ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶ᵉ′ ((u′ ^ w′) [ x := v′ ])
    transport h rewrite eqβ = h
```

The binder cases: the annotation is scoped by the body's prevalidity, hence untouched, and the
operand's step is weakened over the new entry.

```agda
⟶ᵉ′-subst-float {Γ} {v = v} {v′} x x∉ lv lv′
                (Me-Fun′ {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv = go
  where
    z₀   = fresh (x ∷ L)
    x∉t : x ∉ fv t
    x∉t h = x∉ (head-fv (prevalid-ctx (⟶ᵉ′-prevalid (F (∉-tail (fresh-∉ (x ∷ L)))))) h)

    ih-d : Γ ∣ [] ⊢ t ⟶ᵉ′ (t′ [ x := v′ ])
    ih-d = subst (λ q → Γ ∣ [] ⊢ q ⟶ᵉ′ (t′ [ x := v′ ])) (subst-fresh {t} x v x∉t)
                 (⟶ᵉ′-subst-float x x∉ lv lv′ d sv)

    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , sub , t) ∷ Γ) ∣ [] ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ′-subst-float x x∉′ lv lv′ (F (∉-tail z∉)) sv′)
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)

        x∉′ : x ∉ dom ((z , sub , t) ∷ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        pvz : ((z , sub , t) ∷ Γ) ∣ [] prevalid
        pvz = ⟶ᵉ′-prevalid (F (∉-tail z∉))

        sv′ : ((z , sub , t) ∷ Γ) ∣ [] ⊢ v ⟶ᵉ′ v′
        sv′ = ⟶ᵉ′-weaken [] ((z , sub , t) ∷ []) pvz sv

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , sub , t) ∷ Γ) ∣ [] ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ′ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , sub , t) ∷ Γ) ∣ [] ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

    go : Γ ∣ [] ⊢ (lam (t [ x := v ]) (u [ x := v ])) ⟶ᵉ′ (lam (t′ [ x := v′ ]) (u′ [ x := v′ ]))
    go rewrite subst-fresh {t} x v x∉t = Me-Fun′ (x ∷ L) ih-d body

⟶ᵉ′-subst-float {Γ} {v = v} {v′} x x∉ lv lv′
                (Me-FOp′ {s = s} {α = α} {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv = go
  where
    x∉α : x ∉ fv α
    x∉α h = x∉ (head-fv (prevalid-ctx (⟶ᵉ′-prevalid (F (∉-tail (fresh-∉ (x ∷ L)))))) h)

    ih-d : Γ ∣ [] ⊢ (t [ x := v ]) ⟶ᵉ′ (t′ [ x := v′ ])
    ih-d = ⟶ᵉ′-subst-float x x∉ lv lv′ d sv

    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , eqv , α) ∷ Γ) ∣ s ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ′-subst-float x x∉′ lv lv′ (F (∉-tail z∉)) sv′)
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)

        x∉′ : x ∉ dom ((z , eqv , α) ∷ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        pvz : ((z , eqv , α) ∷ Γ) ∣ [] prevalid
        pvz = Pv-Nil (prevalid-ctx (⟶ᵉ′-prevalid (F (∉-tail z∉))))

        sv′ : ((z , eqv , α) ∷ Γ) ∣ [] ⊢ v ⟶ᵉ′ v′
        sv′ = ⟶ᵉ′-weaken [] ((z , eqv , α) ∷ []) pvz sv

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , eqv , α) ∷ Γ) ∣ s ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ′ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , eqv , α) ∷ Γ) ∣ s ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

    go : Γ ∣ (α ∷ s) ⊢ (lam (t [ x := v ]) (u [ x := v ])) ⟶ᵉ′ (lam (t′ [ x := v′ ]) (u′ [ x := v′ ]))
    go = Me-FOp′ (x ∷ L) ih-d body
```

## What this establishes

`⟶ᵉ′-subst-float`: a variant step at a term with a free unbound name `x`, together with a
variant step of a locally closed substituend at the empty stack, gives a variant step between
the substituted terms, at the same context and stack, with no scoping demand on the substituend.
