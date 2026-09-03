# MPSS: substitution and opening, without a scoping hypothesis

`MPSS/Subst` proves substitution with the substituted term scoped in the context, `fv v ⊑ dom Γ`,
and threads a context split so that annotations bound during the descent get substituted too.
The diamond cannot use that form: its β case recurses on a body opened at a name the context does
not bind (`MPSS/BetaScope`), so the scoping invariant is not available there.

This module proves the same lemma **without any scoping hypothesis**, and with no context split.
The observation that makes it work: in a derivation that *exists*, prevalidity has already forced
every context annotation and every stack entry to be scoped in the relevant domain. Since `x` is
outside `dom Γ` and the binder rules add only fresh names, `x` occurs in none of them. So the
substitution is the identity on the context and on the stack, and only the subject moves.

That also explains the shape of the `Me-Bet` defect from the other side: a body that uses its
parameter in operand position has *no* derivation at all, because `Me-App` would push an unscoped
term. Whatever derivations do exist are exactly the ones substitution is safe for.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Open where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.StackPush using (pushᵉ)
open import MPSS.Subst.Base using (∉-stack)
open import PSS.Syntax
  using (subst-open; subst-fresh; subst-fvar-≢; subst-intro; subst-lc)
```

## A name outside the domain occurs in no annotation

```agda
∉-ann : ∀ {Γ x y a t} → Γ prevalid → x ∉ dom Γ → (y , a , t) ∈ Γ → x ∉ fv t
∉-ann pv x∉ m h = x∉ (prevalid-bound-fv pv m h)

∉-head : ∀ {Γ s x α} → Γ ∣ (α ∷ s) prevalid → x ∉ dom Γ → x ∉ fv α
∉-head (Pv-Sta _ _ fα) x∉ h = x∉ (fα h)
```

## Substitution

```agda
⟶ᵉ-subst₀ : ∀ {Γ s t t′ v v′} x
          → x ∉ dom Γ → LC v → LC v′
          → Γ ∣ s ⊢ t ⟶ᵉ t′
          → Γ ∣ [] ⊢ v ⟶ᵉ v′
          → Γ ∣ s ⊢ (t [ x := v ]) ⟶ᵉ (t′ [ x := v′ ])

⟶ᵉ-subst₀ {Γ} {s} {v = v} {v′ = v′} x x∉ lv lv′ (Me-Var {x = y} pv) sv = go
  where
    go : Γ ∣ s ⊢ ((fvar y) [ x := v ]) ⟶ᵉ ((fvar y) [ x := v′ ])
    go with x ≟ y
    ... | yes _ = pushᵉ {s = []} {s′ = s} sv pv
    ... | no  _ = Me-Var pv

⟶ᵉ-subst₀ x x∉ lv lv′ (Me-Top pv) sv = Me-Top pv
⟶ᵉ-subst₀ x x∉ lv lv′ (Me-TAp pv) sv = Me-TAp pv
```

`Me-Pro`'s variable is in the domain, so it differs from `x`, and its annotation is scoped, so
the substitution leaves it alone.

```agda
⟶ᵉ-subst₀ {Γ} {s} {v = v} {v′ = v′} x x∉ lv lv′
          (Me-Pro {x = y} {α = α} {α' = β} pv m d) sv = go
  where
    x≢y : x ≢ y
    x≢y refl = x∉ (∈-dom m)

    inner : Γ ∣ s ⊢ (α [ x := v ]) ⟶ᵉ (β [ x := v′ ])
    inner = ⟶ᵉ-subst₀ x x∉ lv lv′ d sv

    inner′ : Γ ∣ s ⊢ α ⟶ᵉ (β [ x := v′ ])
    inner′ = subst (λ z → Γ ∣ s ⊢ z ⟶ᵉ (β [ x := v′ ]))
                   (subst-fresh {α} x v (∉-ann (prevalid-ctx pv) x∉ m)) inner

    go : Γ ∣ s ⊢ ((fvar y) [ x := v ]) ⟶ᵉ (β [ x := v′ ])
    go rewrite subst-fvar-≢ {x} {y} v x≢y = Me-Pro pv m inner′
```

`Me-App` pushes the operand, which prevalidity of the premise's extended context scopes, so the
operand is unchanged by the substitution and the rule applies at the same stack.

```agda
⟶ᵉ-subst₀ {Γ} {s} {v = v} {v′ = v′} x x∉ lv lv′ (Me-App {v = w} {v' = w′} d e) sv = go
  where
    x∉w : x ∉ fv w
    x∉w = ∉-head (⟶ᵉ-prevalid d) x∉

    inner : Γ ∣ (w ∷ s) ⊢ _ ⟶ᵉ _
    inner = ⟶ᵉ-subst₀ x x∉ lv lv′ d sv

    inner′ : Γ ∣ ((w [ x := v ]) ∷ s) ⊢ _ ⟶ᵉ _
    inner′ = subst (λ z → Γ ∣ (z ∷ s) ⊢ _ ⟶ᵉ _) (sym (subst-fresh {w} x v x∉w)) inner

    go : Γ ∣ s ⊢ (app _ (w [ x := v ])) ⟶ᵉ (app _ (w′ [ x := v′ ]))
    go = Me-App inner′ (⟶ᵉ-subst₀ x x∉ lv lv′ e sv)
```

The binder cases. The annotation an entry records is scoped, hence untouched, and the fresh name
is chosen away from `x`.

```agda
⟶ᵉ-subst₀ {Γ} {v = v} {v′ = v′} x x∉ lv lv′
          (Me-Fun {t = a} {t' = a′} {u = u} {u' = u′} L d F) sv =
  Me-Fun (x ∷ L ++ fv v ++ fv v′ ++ dom Γ) (⟶ᵉ-subst₀ x x∉ lv lv′ d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ fv v′ ++ dom Γ)
         → ((z , sub , a [ x := v ]) ∷ Γ) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-subst₀ x x∉′ lv lv′ (F z∉L) sv′)
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail z∉)

        pvz = ⟶ᵉ-prevalid (F z∉L)

        x∉′ : x ∉ dom ((z , sub , a) ∷ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        x∉a : x ∉ fv a
        x∉a = ∉-ann (prevalid-ctx pvz) x∉′ (here refl)

        sv′ : ((z , sub , a) ∷ Γ) ∣ [] ⊢ v ⟶ᵉ v′
        sv′ = weaken sv
          where
            open import MPSS.Weakening using (⟶ᵉ-weaken)
            weaken : Γ ∣ [] ⊢ v ⟶ᵉ v′ → ((z , sub , a) ∷ Γ) ∣ [] ⊢ v ⟶ᵉ v′
            weaken h = ⟶ᵉ-weaken [] ((z , sub , a) ∷ []) (Pv-Nil (prevalid-ctx pvz)) h

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , sub , a) ∷ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , sub , a [ x := v ]) ∷ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite subst-fresh {a} x v x∉a | sym eq | sym eq′ = h

⟶ᵉ-subst₀ {Γ} {v = v} {v′ = v′} x x∉ lv lv′
          (Me-FOp {s = s} {α = α} {t = a} {t' = a′} {u = u} {u' = u′} L d F) sv =
  Me-FOp (x ∷ L ++ fv v ++ fv v′ ++ dom Γ) (⟶ᵉ-subst₀ x x∉ lv lv′ d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ fv v′ ++ dom Γ)
         → ((z , eqv , α) ∷ Γ) ∣ s
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-subst₀ x x∉′ lv lv′ (F z∉L) sv′)
      where
        z≢x : z ≢ x
        z≢x refl = z∉ (here refl)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)
        z∉L : z ∉ L
        z∉L = ∉-++ˡ (∉-tail z∉)

        pvz = ⟶ᵉ-prevalid (F z∉L)

        x∉′ : x ∉ dom ((z , eqv , α) ∷ Γ)
        x∉′ (here p)  = z≢x (sym p)
        x∉′ (there h) = x∉ h

        sv′ : ((z , eqv , α) ∷ Γ) ∣ [] ⊢ v ⟶ᵉ v′
        sv′ = weaken sv
          where
            open import MPSS.Weakening using (⟶ᵉ-weaken)
            weaken : Γ ∣ [] ⊢ v ⟶ᵉ v′ → ((z , eqv , α) ∷ Γ) ∣ [] ⊢ v ⟶ᵉ v′
            weaken h = ⟶ᵉ-weaken [] ((z , eqv , α) ∷ []) (Pv-Nil (prevalid-ctx pvz)) h

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , eqv , α) ∷ Γ) ∣ s
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , eqv , α) ∷ Γ) ∣ s
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h
```

The β case.

```agda
⟶ᵉ-subst₀ {Γ} {s} {v = v} {v′ = v′} x x∉ lv lv′
          (Me-Bet {t = a} {u = u} {u' = u′} {v = w} {v' = w′} L F e) sv =
  transport (Me-Bet {t = a [ x := v ]} {u [ x := v ]} {u′ [ x := v′ ]}
                    {w [ x := v ]} {w′ [ x := v′ ]}
                    (x ∷ L ++ fv v ++ fv v′) body (⟶ᵉ-subst₀ x x∉ lv lv′ e sv))
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v ++ fv v′)
         → Γ ∣ s ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = go (⟶ᵉ-subst₀ x x∉ lv lv′ (F z∉L) sv)
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

        go : Γ ∣ s ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ ((u′ ^ fvar z) [ x := v′ ])
           → Γ ∣ s ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ ((u′ [ x := v′ ]) ^ fvar z)
        go h rewrite sym eq | sym eq′ = h

    eqβ : ((u′ ^ w′) [ x := v′ ]) ≡ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
    eqβ = subst-open lv′ 0 w′ u′ x

    transport : Γ ∣ s ⊢ (app (lam (a [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                      ⟶ᵉ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
              → Γ ∣ s ⊢ (app (lam (a [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                      ⟶ᵉ ((u′ ^ w′) [ x := v′ ])
    transport h rewrite eqβ = h
```

## Opening

```agda
⟶ᵉ-open₀ : ∀ {Γ s u u′ v v′} (L : List Name)
         → LC v → LC v′
         → (∀ {z} → z ∉ L → Γ ∣ s ⊢ (u ^ fvar z) ⟶ᵉ (u′ ^ fvar z))
         → Γ ∣ [] ⊢ v ⟶ᵉ v′
         → Γ ∣ s ⊢ (u ^ v) ⟶ᵉ (u′ ^ v′)
⟶ᵉ-open₀ {Γ} {s} {u} {u′} {v} {v′} L lv lv′ F sv = result
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

    result : Γ ∣ s ⊢ (u ^ v) ⟶ᵉ (u′ ^ v′)
    result rewrite subst-intro {u} lv x x∉u | subst-intro {u′} lv′ x x∉u′ =
      ⟶ᵉ-subst₀ x x∉Γ lv lv′ (F x∉L) sv
```

## What this establishes

Substitution and opening for equivalence reduction with **no scoping hypothesis on the
substituted term** and no context split, because a derivation's own prevalidity already keeps the
substituted name out of every context annotation and every stack entry. This is the form the
diamond's β cases need, where the body is opened at a name the context does not bind.
