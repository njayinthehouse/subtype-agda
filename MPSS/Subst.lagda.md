# MPSS: substitution and opening for both reductions

Prerequisite for v2's Lemma 2 (`⟶ᵉ` has the diamond property) and Lemma 1 (`⟶ˢ` and `⟶ᵉ`
strongly commute): both reductions survive substituting a term for a name the ambient context
does not bind, and a body family opened at fresh names can be opened at a term instead.

The name `x` substituted for is one opened into a body, as in the β-rule `Me-Bet`, so it lies
outside `dom Γ`. But a derivation binds further names as it descends — `Me-Fun` records `z ≤ t`,
`Me-FOp` records `z ≡ α` — and those annotations *can* mention `x`, since they come from the term
rather than from `Γ`. So the lemma is stated over a context split `Δ ++ Γ`, substituting in `Δ`
and in the stack and leaving `Γ` alone: prevalidity scopes `Γ`'s bounds in `dom Γ`, which `x` is
outside of.

**Equivalence takes two reducts, promotion takes one.** `⟶ᵉ` reduces annotations (`Me-Fun` has
`t ⟶ᵉ t′`), so its substitution lemma can put `v` on the left and a reduct `v′` on the right, as
the simultaneous rules need. `⟶ˢ` leaves annotations alone (`Ms-Fun` keeps `t` on both sides), so
the same term must be substituted on both sides there, or the two annotations would disagree.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Subst where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
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
open import MPSS.StackPush using (pushᵉ; ⟶ᵉ-refl)
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.Rename using (substCtx; substStack; dom-substCtx; ∈-substCtx; substStack-id)
open import MPSS.Subst.Base
open import PSS.Syntax using (subst-open; subst-fvar-≢; subst-intro)
```

The bookkeeping — domains, scoping, lookups and prevalidity under substitution — is in
`MPSS/Subst/Base`, so that this module is the reduction cases alone.

## Substitution for equivalence reduction

```agda
⟶ᵉ-subst : ∀ (Δ : Ctx) {Γ s t t′ v v′} x
         → x ∉ dom (Δ ++ Γ) → LC v → LC v′ → fv v ⊑ dom Γ
         → (Δ ++ Γ) ∣ s ⊢ t ⟶ᵉ t′
         → (substCtx x v Δ ++ Γ) ∣ [] ⊢ v ⟶ᵉ v′
         → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) ⟶ᵉ (t′ [ x := v′ ])

⟶ᵉ-subst Δ {Γ} {s} {v = v} {v′ = v′} x x∉ lv lv′ fvv (Me-Var {x = y} pv) sv = go
  where
    pv′ = prevalid-subst Δ lv fvv x∉ pv
    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
           ⊢ ((fvar y) [ x := v ]) ⟶ᵉ ((fvar y) [ x := v′ ])
    go with x ≟ y
    ... | yes _ = pushᵉ {s = []} {s′ = substStack x v s} sv pv′
    ... | no  _ = Me-Var pv′

⟶ᵉ-subst Δ x x∉ lv lv′ fvv (Me-Top pv) sv = Me-Top (prevalid-subst Δ lv fvv x∉ pv)
⟶ᵉ-subst Δ x x∉ lv lv′ fvv (Me-TAp pv) sv = Me-TAp (prevalid-subst Δ lv fvv x∉ pv)
```

`Me-Pro` reads an annotation. If it is in `Δ` the substituted entry is looked up; if it is in `Γ`
the entry is unchanged, and either way `∈-sub` produces the substituted membership.

```agda
⟶ᵉ-subst Δ {Γ} {s} {v = v} {v′ = v′} x x∉ lv lv′ fvv
         (Me-Pro {x = y} {α = α} {α' = β} pv m d) sv = go
  where
    x≢y : x ≢ y
    x≢y refl = x∉ (∈-dom m)

    pv′ = prevalid-subst Δ lv fvv x∉ pv
    m′  = ∈-sub Δ (prevalid-ctx pv) x∉ m

    inner : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
              ⊢ (α [ x := v ]) ⟶ᵉ (β [ x := v′ ])
    inner = ⟶ᵉ-subst Δ x x∉ lv lv′ fvv d sv

    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
           ⊢ ((fvar y) [ x := v ]) ⟶ᵉ (β [ x := v′ ])
    go rewrite subst-fvar-≢ {x} {y} v x≢y = Me-Pro pv′ m′ inner

⟶ᵉ-subst Δ x x∉ lv lv′ fvv (Me-App d e) sv =
  Me-App (⟶ᵉ-subst Δ x x∉ lv lv′ fvv d sv) (⟶ᵉ-subst Δ x x∉ lv lv′ fvv e sv)
```

The binder cases extend `Δ` with the substituted annotation and lift the operand's step over the
new entry.

```agda
⟶ᵉ-subst Δ {Γ} {v = v} {v′ = v′} x x∉ lv lv′ fvv
         (Me-Fun {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv =
  Me-Fun (x ∷ L ++ fv v ++ fv v′ ++ dom (Δ ++ Γ))
         (⟶ᵉ-subst Δ x x∉ lv lv′ fvv d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ fv v′ ++ dom (Δ ++ Γ))
         → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-subst ((z , sub , t) ∷ Δ) x x∉′ lv lv′ fvv (F z∉L) sv′)
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail z∉)
        z∉Γ : z ∉ dom (Δ ++ Γ)
        z∉Γ = ∉-++ʳ (fv v′) (∉-++ʳ (fv v) (∉-++ʳ L (∉-tail z∉)))

        x∉′ : x ∉ dom (((z , sub , t) ∷ Δ) ++ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        pvz : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ [] prevalid
        pvz = prevalid-subst ((z , sub , t) ∷ Δ) lv fvv x∉′ (⟶ᵉ-prevalid (F z∉L))

        sv′ : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ [] ⊢ v ⟶ᵉ v′
        sv′ = ⟶ᵉ-weaken [] ((z , sub , t [ x := v ]) ∷ []) pvz sv

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

⟶ᵉ-subst Δ {Γ} {v = v} {v′ = v′} x x∉ lv lv′ fvv
         (Me-FOp {s = s} {α = α} {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv =
  Me-FOp (x ∷ L ++ fv v ++ fv v′ ++ dom (Δ ++ Γ))
         (⟶ᵉ-subst Δ x x∉ lv lv′ fvv d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ fv v′ ++ dom (Δ ++ Γ))
         → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-subst ((z , eqv , α) ∷ Δ) x x∉′ lv lv′ fvv (F z∉L) sv′)
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail z∉)

        x∉′ : x ∉ dom (((z , eqv , α) ∷ Δ) ++ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        pvz : ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s) prevalid
        pvz = prevalid-subst ((z , eqv , α) ∷ Δ) lv fvv x∉′ (⟶ᵉ-prevalid (F z∉L))

        sv′ : ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ [] ⊢ v ⟶ᵉ v′
        sv′ = ⟶ᵉ-weaken [] ((z , eqv , α [ x := v ]) ∷ []) (Pv-Nil (prevalid-ctx pvz)) sv

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

The β case. Its body premise is at the *same* context, so no entry is added; the conclusion
opens the reduced body with the reduced operand, and substitution commutes with that opening
because the substituted term is locally closed.

```agda
⟶ᵉ-subst Δ {Γ} {s} {v = v} {v′ = v′} x x∉ lv lv′ fvv
         (Me-Bet {t = t} {u = u} {u' = u′} {v = w} {v' = w′} L F e) sv =
  transport (Me-Bet {t = t [ x := v ]} {u [ x := v ]} {u′ [ x := v′ ]}
                    {w [ x := v ]} {w′ [ x := v′ ]}
                    (x ∷ L ++ fv v ++ fv v′) body
                    (⟶ᵉ-subst Δ x x∉ lv lv′ fvv e sv))
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ fv v′)
         → (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = go (⟶ᵉ-subst Δ x x∉ lv lv′ fvv (F z∉L) sv)
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail z∉)

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

## Opening

At the top level the split is trivial and the stack is untouched, because a name outside
`dom Γ` cannot occur in a stack that prevalidity scopes there.

```agda
⟶ᵉ-open : ∀ {Γ s u u′ v v′} (L : List Name)
        → LC v → LC v′ → fv v ⊑ dom Γ
        → (∀ {z} → z ∉ L → Γ ∣ s ⊢ (u ^ fvar z) ⟶ᵉ (u′ ^ fvar z))
        → Γ ∣ [] ⊢ v ⟶ᵉ v′
        → Γ ∣ s ⊢ (u ^ v) ⟶ᵉ (u′ ^ v′)
⟶ᵉ-open {Γ} {s} {u} {u′} {v} {v′} L lv lv′ fvv F sv = result
  where
    A    = L ++ dom Γ ++ fv u ++ fv u′
    x    = fresh A
    a∉   = fresh-∉ A
    x∉L  = ∉-++ˡ a∉
    r₁   = ∉-++ʳ L a∉
    x∉Γ  : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ r₁
    r₂   = ∉-++ʳ (dom Γ) r₁
    x∉u  : x ∉ fv u
    x∉u  = ∉-++ˡ r₂
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ (fv u) r₂

    x∉s : x ∉ fvStack s
    x∉s = ∉-stack (⟶ᵉ-prevalid (F x∉L)) x∉Γ

    step : Γ ∣ (substStack x v s) ⊢ ((u ^ fvar x) [ x := v ]) ⟶ᵉ ((u′ ^ fvar x) [ x := v′ ])
    step = ⟶ᵉ-subst [] x x∉Γ lv lv′ fvv (F x∉L) sv

    step′ : Γ ∣ s ⊢ ((u ^ fvar x) [ x := v ]) ⟶ᵉ ((u′ ^ fvar x) [ x := v′ ])
    step′ = subst (λ σ → Γ ∣ σ ⊢ ((u ^ fvar x) [ x := v ]) ⟶ᵉ ((u′ ^ fvar x) [ x := v′ ]))
                  (substStack-id x v s x∉s) step

    result : Γ ∣ s ⊢ (u ^ v) ⟶ᵉ (u′ ^ v′)
    result rewrite subst-intro {u} lv x x∉u | subst-intro {u′} lv′ x x∉u′ = step′
```

## Substitution for promotion

One term on both sides, for the reason given at the head of the module. The equivalence step it
hands to `Ms-Equ` is the reflexive one.

```agda
⟶ˢ-subst : ∀ (Δ : Ctx) {Γ s t t′ v} x
         → x ∉ dom (Δ ++ Γ) → LC v → fv v ⊑ dom Γ
         → (Δ ++ Γ) ∣ s ⊢ t ⟶ˢ t′
         → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) ⟶ˢ (t′ [ x := v ])

⟶ˢ-subst Δ {Γ} {s} {v = v} x x∉ lv fvv (Ms-Pro {x = y} {t = t} pv m) = go
  where
    x≢y : x ≢ y
    x≢y refl = x∉ (∈-dom m)

    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
           ⊢ ((fvar y) [ x := v ]) ⟶ˢ (t [ x := v ])
    go rewrite subst-fvar-≢ {x} {y} v x≢y =
      Ms-Pro (prevalid-subst Δ lv fvv x∉ pv) (∈-sub Δ (prevalid-ctx pv) x∉ m)

⟶ˢ-subst Δ x x∉ lv fvv (Ms-Top pv) = Ms-Top (prevalid-subst Δ lv fvv x∉ pv)

⟶ˢ-subst Δ {Γ} {v = v} x x∉ lv fvv (Ms-Equ pv e) =
  Ms-Equ pv′ (⟶ᵉ-subst Δ x x∉ lv lv fvv e (⟶ᵉ-refl (Pv-Nil (prevalid-ctx pv′)) lv fvv′))
  where
    pv′ = prevalid-subst Δ lv fvv x∉ pv
    fvv′ : fv v ⊑ dom (substCtx x v Δ ++ Γ)
    fvv′ h = ∈-dom-sub Δ (subst (_ ∈_) (sym (dom-++ Δ Γ)) (∈-++⁺ʳ (dom Δ) (fvv h)))

⟶ˢ-subst Δ x x∉ lv fvv (Ms-App d) = Ms-App (⟶ˢ-subst Δ x x∉ lv fvv d)

⟶ˢ-subst Δ {Γ} {v = v} x x∉ lv fvv (Ms-Fun {t = t} {u = u} {u' = u′} L F) =
  Ms-Fun (x ∷ L ++ fv v ++ dom (Δ ++ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ dom (Δ ++ Γ))
         → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ ((u′ [ x := v ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ-subst ((z , sub , t) ∷ Δ) x x∉′ lv fvv (F z∉L))
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail z∉)
        x∉′ : x ∉ dom (((z , sub , t) ∷ Δ) ++ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v ])) (subst-fvar-≢ v x≢z))

        transport : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ˢ ((u′ ^ fvar z) [ x := v ])
                  → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ ((u′ [ x := v ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

⟶ˢ-subst Δ {Γ} {v = v} x x∉ lv fvv
         (Ms-FOp {s = s} {α = α} {t = t} {u = u} {u' = u′} L F) =
  Ms-FOp (x ∷ L ++ fv v ++ dom (Δ ++ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ dom (Δ ++ Γ))
         → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ ((u′ [ x := v ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ-subst ((z , eqv , α) ∷ Δ) x x∉′ lv fvv (F z∉L))
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail z∉)
        x∉′ : x ∉ dom (((z , eqv , α) ∷ Δ) ++ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

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

## What this establishes

Substitution for both reductions, over a context split, and the opening lemma that turns a
cofinitely quantified body family into a single derivation at an arbitrary locally closed
operand. These are v2's Lemmas 31 and 32 in the shape the locally nameless encoding needs, and
they are what the β cases of the diamond consume.
