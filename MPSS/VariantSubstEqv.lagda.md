# MPSS: Lemma 32 in its bound form, for the variant; opening at an unbound name

`MPSS/SubstEqv` transcribed: substituting a definition `x ≡ v` away from a variant derivation,
with `Me-Pro′` on `x` becoming the substituted step of `v`. Then two small consequences of the
floating substitution (`MPSS/VariantSubst`): opening a cofinite family at a term, and closing a
body over one name and reopening it at another — the two shapes the diamond's β cases use.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantSubstEqv where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax using (subst-open; subst-fvar-≢; subst-fresh; subst-intro; ∉-tail; ∉-++ˡ; ∉-++ʳ; fresh; fresh-∉; closeRec)
open import PSS.Close using (open-close; fv-close)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-weaken; ⟶ᵉ′-prevalid)
open import MPSS.VariantPush using (pushᵉ′)
open import MPSS.VariantSubst using (⟶ᵉ′-subst-float)
open import MPSS.Rename using (substCtx; substStack; substStack-id; x∉-w)
open import MPSS.SubstEqv using (prevalid-subst≡; ∈-mid; ∈-sub≡)
```

## The lemma

```agda
⟶ᵉ′-subst≡ : ∀ (Δ : Ctx) {Γ s t t′ v v′} x
           → LC v → LC v′ → fv v ⊑ dom Γ
           → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ t ⟶ᵉ′ t′
           → Γ ∣ [] ⊢ v ⟶ᵉ′ v′
           → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) ⟶ᵉ′ (t′ [ x := v′ ])

⟶ᵉ′-subst≡ Δ {Γ} {s} {v = v} {v′ = v′} x lv lv′ fvv (Me-Var′ {x = y} pv) sv = go
  where
    pv′ = prevalid-subst≡ Δ lv fvv pv
    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
           ⊢ ((fvar y) [ x := v ]) ⟶ᵉ′ ((fvar y) [ x := v′ ])
    go with x ≟ y
    ... | yes _ = pushᵉ′ {s = []} {s′ = substStack x v s}
                         (⟶ᵉ′-weaken [] (substCtx x v Δ) (Pv-Nil (prevalid-ctx pv′)) sv) pv′
    ... | no  _ = Me-Var′ pv′

⟶ᵉ′-subst≡ Δ x lv lv′ fvv (Me-Top′ pv) sv = Me-Top′ (prevalid-subst≡ Δ lv fvv pv)
⟶ᵉ′-subst≡ Δ x lv lv′ fvv (Me-TAp′ pv) sv = Me-TAp′ (prevalid-subst≡ Δ lv fvv pv)

⟶ᵉ′-subst≡ Δ {Γ} {s} {v = v} {v′ = v′} x lv lv′ fvv
           (Me-Pro′ {x = y} {α = α} {α' = β} pv m d) sv = go
  where
    pv′ = prevalid-subst≡ Δ lv fvv pv

    inner : (substCtx x v Δ ++ Γ) ∣ [] ⊢ (α [ x := v ]) ⟶ᵉ′ (β [ x := v′ ])
    inner = ⟶ᵉ′-subst≡ Δ x lv lv′ fvv d sv

    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
           ⊢ ((fvar y) [ x := v ]) ⟶ᵉ′ (β [ x := v′ ])
    go with x ≟ y
    ... | yes refl with ∈-mid Δ (prevalid-ctx pv) m
    ...   | refl , refl =
      pushᵉ′ {s = []} {s′ = substStack x v s}
             (subst (λ w → (substCtx x v Δ ++ Γ) ∣ [] ⊢ w ⟶ᵉ′ (β [ x := v′ ]))
                    (subst-fresh {v} x v (x∉-w Δ (prevalid-ctx pv))) inner)
             pv′
    go | no x≢y = Me-Pro′ pv′ (∈-sub≡ Δ (prevalid-ctx pv) (λ eq → x≢y (sym eq)) m) inner

⟶ᵉ′-subst≡ Δ x lv lv′ fvv (Me-App′ d e) sv =
  Me-App′ (⟶ᵉ′-subst≡ Δ x lv lv′ fvv d sv) (⟶ᵉ′-subst≡ Δ x lv lv′ fvv e sv)

⟶ᵉ′-subst≡ Δ {Γ} {v = v} {v′ = v′} x lv lv′ fvv
           (Me-Fun′ {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv =
  Me-Fun′ (x ∷ L) (⟶ᵉ′-subst≡ Δ x lv lv′ fvv d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ′-subst≡ ((z , sub , t) ∷ Δ) x lv lv′ fvv (F (∉-tail z∉)) sv)
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ′ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

⟶ᵉ′-subst≡ Δ {Γ} {v = v} {v′ = v′} x lv lv′ fvv
           (Me-FOp′ {s = s} {α = α} {t = t} {t' = t′} {u = u} {u' = u′} L d F) sv =
  Me-FOp′ (x ∷ L) (⟶ᵉ′-subst≡ Δ x lv lv′ fvv d sv) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ′-subst≡ ((z , eqv , α) ∷ Δ) x lv lv′ fvv (F (∉-tail z∉)) sv)
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        transport : ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ′ ((u′ ^ fvar z) [ x := v′ ])
                  → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

⟶ᵉ′-subst≡ Δ {Γ} {s} {v = v} {v′ = v′} x lv lv′ fvv
           (Me-Bet′ {t = t} {u = u} {u' = u′} {v = w} {v' = w′} L F e) sv =
  transport (Me-Bet′ {t = t [ x := v ]} {u [ x := v ]} {u′ [ x := v′ ]}
                     {w [ x := v ]} {w′ [ x := v′ ]}
                     (x ∷ L) body
                     (⟶ᵉ′-subst≡ Δ x lv lv′ fvv e sv))
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
    body {z} z∉ = go (⟶ᵉ′-subst≡ Δ x lv lv′ fvv (F (∉-tail z∉)) sv)
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv′ 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := v′ ])) (subst-fvar-≢ v′ x≢z))

        go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
               ⊢ ((u ^ fvar z) [ x := v ]) ⟶ᵉ′ ((u′ ^ fvar z) [ x := v′ ])
           → (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
               ⊢ ((u [ x := v ]) ^ fvar z) ⟶ᵉ′ ((u′ [ x := v′ ]) ^ fvar z)
        go h rewrite sym eq | sym eq′ = h

    eqβ : ((u′ ^ w′) [ x := v′ ]) ≡ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
    eqβ = subst-open lv′ 0 w′ u′ x

    transport : (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                  ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶ᵉ′ ((u′ [ x := v′ ]) ^ (w′ [ x := v′ ]))
              → (substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                  ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶ᵉ′ ((u′ ^ w′) [ x := v′ ])
    transport h rewrite eqβ = h
```

## The head form

```agda
⟶ᵉ′-subst≡-head : ∀ {Γ s u u′ v v′} x
                → x ∉ fv u → x ∉ fv u′ → x ∉ fvStack s → LC v → LC v′ → fv v ⊑ dom Γ
                → ((x , eqv , v) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ (u′ ^ fvar x)
                → Γ ∣ [] ⊢ v ⟶ᵉ′ v′
                → Γ ∣ s ⊢ (u ^ v) ⟶ᵉ′ (u′ ^ v′)
⟶ᵉ′-subst≡-head {Γ} {s} {u} {u′} {v} {v′} x x∉u x∉u′ x∉s lv lv′ fvv d sv
  rewrite subst-intro {u} lv x x∉u | subst-intro {u′} lv′ x x∉u′
  = subst (λ σ → Γ ∣ σ ⊢ ((u ^ fvar x) [ x := v ]) ⟶ᵉ′ ((u′ ^ fvar x) [ x := v′ ]))
          (substStack-id x v s x∉s)
          (⟶ᵉ′-subst≡ [] x lv lv′ fvv d sv)
```

## Opening at an unbound name, and closing over one

```agda
⟶ᵉ′-open₀ : ∀ {Γ s u u′ v v′} (L : List Name)
          → LC v → LC v′
          → (∀ {z} → z ∉ L → Γ ∣ s ⊢ (u ^ fvar z) ⟶ᵉ′ (u′ ^ fvar z))
          → Γ ∣ [] ⊢ v ⟶ᵉ′ v′
          → Γ ∣ s ⊢ (u ^ v) ⟶ᵉ′ (u′ ^ v′)
⟶ᵉ′-open₀ {Γ} {s} {u} {u′} {v} {v′} L lv lv′ F sv = result
  where
    A    = L ++ dom Γ ++ fv u ++ fv u′
    x    = fresh A
    x∉L  : x ∉ L
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉Γ  : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    x∉u  : x ∉ fv u
    x∉u  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L (fresh-∉ A)))
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L (fresh-∉ A)))

    result : Γ ∣ s ⊢ (u ^ v) ⟶ᵉ′ (u′ ^ v′)
    result rewrite subst-intro {u} lv x x∉u | subst-intro {u′} lv′ x x∉u′ =
      ⟶ᵉ′-subst-float x x∉Γ lv lv′ (F x∉L) sv

close-rename₀′ : ∀ {Γ s u w} x y → x ∉ dom Γ → x ∉ fv u → LC w
               → Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ w
               → Γ ∣ s ⊢ (u ^ fvar y) ⟶ᵉ′ ((closeRec 0 x w) ^ fvar y)
close-rename₀′ {Γ} {s} {u} {w} x y x∉Γ x∉u lw d
  rewrite subst-intro {u} (lc-fvar {y}) x x∉u
        | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
  = ⟶ᵉ′-subst-float x x∉Γ lc-fvar lc-fvar d′ (Me-Var′ (prevalid-nil (⟶ᵉ′-prevalid d)))
  where
    d′ : Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ ((closeRec 0 x w) ^ fvar x)
    d′ rewrite open-close lw 0 x = d
```

## What this establishes

`⟶ᵉ′-subst≡` and its head form, `⟶ᵉ′-open₀`, `close-rename₀′`: the substitution and opening
facts the variant's diamond needs at its β cases.
