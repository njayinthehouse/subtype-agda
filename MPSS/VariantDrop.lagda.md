# MPSS: four helpers for the variant's commutation lemma

What `MPSS/VariantCommutation` needs beyond what the variant's diamond already built:

- `⟶ᵉ′-drop`: a variant step that avoids a closed set of names is derivable with those names
  removed from the context;
- `↣′-sub` and `avoids-sub′`: reading a subtype annotation's reduct off a variant context
  reduction, and that the piece avoids what the reduction's pieces avoid;
- `⟶ˢ′-subst≡` and its head form: substituting an equivalence-bound name by its bound in a
  subtyping reduction. Unlike the equivalence version (`MPSS/VariantSubstEqv`) the bound is not
  reduced, since `Ms-Pro′` has no premise through which a reduct could enter.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantDrop where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-prevalid; ⟶ᵉ′-weaken; ⟶ᵉ′-refl)
open import MPSS.VariantCtx
open import MPSS.VariantSub
open import MPSS.VariantAvoids using (Avoids′; Avoids*′; stack-free′; avoids-weaken′; avoids-refl′)
open import MPSS.VariantSubstEqv using (⟶ᵉ′-subst≡)
open import MPSS.VariantDiamond using (Pieces′)
open import MPSS.Closed
open import MPSS.Drop
open import MPSS.Rename using (substCtx; substStack; substStack-id; x∉-w; open-rename)
open import MPSS.SubstEqv using (prevalid-subst≡; ∈-mid; ∈-sub≡)
open import PSS.Close using (open-close; fv-close)
```

## Dropping a closed set from the context

```agda
⟶ᵉ′-drop : ∀ {Γ s u v B} → Closed Γ B → (d : Γ ∣ s ⊢ u ⟶ᵉ′ v) → Avoids*′ B d
         → (Γ ∖ B) ∣ s ⊢ u ⟶ᵉ′ v
⟶ᵉ′-drop cl (Me-Var′ {x = x} pv) av = Me-Var′ (prevalid-∖-ext cl (stack-free′ (Me-Var′ {x = x} pv) av) pv)
⟶ᵉ′-drop cl (Me-Top′ pv) av = Me-Top′ (prevalid-∖-ext cl (stack-free′ (Me-Top′ pv) av) pv)
⟶ᵉ′-drop cl (Me-TAp′ {u = u} pv) av = Me-TAp′ (prevalid-∖-ext cl (stack-free′ (Me-TAp′ {u = u} pv) av) pv)
⟶ᵉ′-drop cl (Me-Pro′ pv m d) av =
  Me-Pro′ (prevalid-∖-ext cl (stack-free′ (Me-Pro′ pv m d) av) pv)
          (∈-∖ (λ x∈B → proj₁ (av x∈B) refl) m)
          (⟶ᵉ′-drop cl d (λ b∈ → proj₂ (proj₂ (av b∈))))
⟶ᵉ′-drop cl (Me-App′ d e) av =
  Me-App′ (⟶ᵉ′-drop cl d (λ b∈ → proj₁ (av b∈))) (⟶ᵉ′-drop cl e (λ b∈ → proj₂ (av b∈)))
⟶ᵉ′-drop {B = B} cl (Me-Bet′ {u' = u'} L F e) av =
  Me-Bet′ {u' = u'} L (λ x∉ → ⟶ᵉ′-drop cl (F x∉) (λ b∈ → proj₁ (av b∈) x∉))
          (⟶ᵉ′-drop cl e (λ b∈ → proj₂ (av b∈)))
⟶ᵉ′-drop {Γ} {B = B} cl (Me-Fun′ {t = t} {u = u} {u' = u'} L d F) av =
  Me-Fun′ {u' = u'} (L ++ B) (⟶ᵉ′-drop cl d (λ b∈ → proj₁ (proj₂ (av b∈)))) body
  where
    body : ∀ {y} → y ∉ (L ++ B) → ((y , sub , t) ∷ (Γ ∖ B)) ∣ [] ⊢ (u ^ fvar y) ⟶ᵉ′ (u' ^ fvar y)
    body {y} y∉ rewrite sym (∖-∉ {Γ} {B} {y} {sub} {t} (∉-++ʳ L y∉)) =
      ⟶ᵉ′-drop (closed-sub cl (λ b∈ → proj₁ (av b∈))) (F (∉-++ˡ y∉))
               (λ b∈ → proj₂ (proj₂ (av b∈)) (∉-++ˡ y∉) (λ eq → ∉-++ʳ L y∉ (subst (_∈ B) (sym eq) b∈)))
⟶ᵉ′-drop {Γ} {B = B} cl (Me-FOp′ {s = s} {α = α} {u = u} {u' = u'} L d F) av =
  Me-FOp′ {u' = u'} (L ++ B) (⟶ᵉ′-drop cl d (λ b∈ → proj₁ (proj₂ (av b∈)))) body
  where
    body : ∀ {y} → y ∉ (L ++ B) → ((y , eqv , α) ∷ (Γ ∖ B)) ∣ s ⊢ (u ^ fvar y) ⟶ᵉ′ (u' ^ fvar y)
    body {y} y∉ rewrite sym (∖-∉ {Γ} {B} {y} {eqv} {α} (∉-++ʳ L y∉)) =
      ⟶ᵉ′-drop (closed-eqv cl (λ b∈ → proj₁ (av b∈))) (F (∉-++ˡ y∉))
               (λ b∈ → proj₂ (proj₂ (av b∈)) (∉-++ˡ y∉) (λ eq → ∉-++ʳ L y∉ (subst (_∈ B) (sym eq) b∈)))
```

## A subtype annotation's reduct

```agda
↣′-sub : ∀ {Γ s Γ' s' x t} → Γ prevalid → Γ ∣ s ↣′ Γ' ∣ s' → x ≤ t ∈ Γ
       → ∃[ t' ] ((x ≤ t' ∈ Γ') × (Γ ∣ [] ⊢ t ⟶ᵉ′ t'))
↣′-sub {t = t} pv Ct-Refl′ m =
  t , m , ⟶ᵉ′-refl (Pv-Nil pv) (prevalid-bound-lc pv m) (prevalid-bound-fv pv m)
↣′-sub pv (Ct-Stk′ d _) m = ↣′-sub pv d m
↣′-sub pv (Ct-Ann′ {x = y} {c = c} {t = t₀} d e) (here refl) =
  _ , here refl , ⟶ᵉ′-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e
↣′-sub pv (Ct-Ann′ {x = y} {c = c} {t = t₀} d e) (there m)
  with ↣′-sub (tail-prevalid pv) d m
... | t' , m' , e' = t' , there m' , ⟶ᵉ′-weaken [] ((y , c , t₀) ∷ []) (Pv-Nil pv) e'

avoids-sub′ : ∀ {b Γ s Γ' s' x t} (pv : Γ prevalid) (c : Γ ∣ s ↣′ Γ' ∣ s') (m : x ≤ t ∈ Γ)
            → Pieces′ b c → Avoids′ b (proj₂ (proj₂ (↣′-sub pv c m)))
avoids-sub′ pv Ct-Refl′ m b∉ =
  avoids-refl′ _ _ _ (λ ()) (λ h → b∉ (prevalid-bound-fv pv m h))
avoids-sub′ pv (Ct-Stk′ c _) m (pc , _) = avoids-sub′ pv c m pc
avoids-sub′ pv (Ct-Ann′ c e) (here refl) (pc , av) = avoids-weaken′ [] _ _ e av
avoids-sub′ pv (Ct-Ann′ c e) (there m) (pc , av)
  with ↣′-sub (tail-prevalid pv) c m | avoids-sub′ (tail-prevalid pv) c m pc
... | t' , m' , e' | av' = avoids-weaken′ [] _ _ e' av'
```

## Substituting an equivalence-bound name in a subtyping reduction

```agda
⟶ˢ′-subst≡ : ∀ (Δ : Ctx) {Γ s t t′ v} x
           → LC v → fv v ⊑ dom Γ
           → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ t ⟶ˢ′ t′
           → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) ⟶ˢ′ (t′ [ x := v ])

⟶ˢ′-subst≡ Δ {Γ} {s} {v = v} x lv fvv (Ms-Pro′ {x = y} {t = t} pv m) = go
  where
    pv′ = prevalid-subst≡ Δ lv fvv pv
    go : (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ ((fvar y) [ x := v ]) ⟶ˢ′ (t [ x := v ])
    go with x ≟ y
    ... | yes refl with ∈-mid Δ (prevalid-ctx pv) m
    ...   | () , _
    go | no x≢y = Ms-Pro′ pv′ (∈-sub≡ Δ (prevalid-ctx pv) (λ eq → x≢y (sym eq)) m)

⟶ˢ′-subst≡ Δ x lv fvv (Ms-Top′ pv) = Ms-Top′ (prevalid-subst≡ Δ lv fvv pv)

⟶ˢ′-subst≡ Δ {Γ} x lv fvv (Ms-Equ′ pv e) =
  Ms-Equ′ (prevalid-subst≡ Δ lv fvv pv)
          (⟶ᵉ′-subst≡ Δ x lv lv fvv e (⟶ᵉ′-refl (Pv-Nil pvΓ) lv fvv))
  where
    pvΓ : Γ prevalid
    pvΓ = suffix Δ (prevalid-ctx pv)
      where
        suffix : ∀ (Δ : Ctx) {Γ e} → (Δ ++ e ∷ Γ) prevalid → Γ prevalid
        suffix []      pv = tail-prevalid pv
        suffix (_ ∷ Δ) pv = suffix Δ (tail-prevalid pv)

⟶ˢ′-subst≡ Δ x lv fvv (Ms-App′ d) = Ms-App′ (⟶ˢ′-subst≡ Δ x lv fvv d)

⟶ˢ′-subst≡ Δ {Γ} {v = v} x lv fvv (Ms-Fun′ {t = t} {u = u} {u' = u′} L F) =
  Ms-Fun′ (x ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ′ ((u′ [ x := v ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ′-subst≡ ((z , sub , t) ∷ Δ) x lv fvv (F (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v ])) (subst-fvar-≢ v x≢z))
        transport : ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ˢ′ ((u′ ^ fvar z) [ x := v ])
                  → ((z , sub , t [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ′ ((u′ [ x := v ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h

⟶ˢ′-subst≡ Δ {Γ} {v = v} x lv fvv (Ms-FOp′ {s = s} {α = α} {t = t} {u = u} {u' = u′} L F) =
  Ms-FOp′ (x ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ′ ((u′ [ x := v ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ′-subst≡ ((z , eqv , α) ∷ Δ) x lv fvv (F (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        eq′ = trans (subst-open lv 0 (fvar z) u′ x)
                    (cong (λ w → openRec 0 w (u′ [ x := v ])) (subst-fvar-≢ v x≢z))
        transport : ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u ^ fvar z) [ x := v ]) ⟶ˢ′ ((u′ ^ fvar z) [ x := v ])
                  → ((z , eqv , α [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u [ x := v ]) ^ fvar z) ⟶ˢ′ ((u′ [ x := v ]) ^ fvar z)
        transport h rewrite sym eq | sym eq′ = h
```

The head form: the bound name is the head of the context, and the stack does not mention it.

```agda
⟶ˢ′-subst≡-head : ∀ {Γ s u u′ v} x
                → x ∉ fv u → x ∉ fv u′ → x ∉ fvStack s → LC v → fv v ⊑ dom Γ
                → ((x , eqv , v) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ˢ′ (u′ ^ fvar x)
                → Γ ∣ s ⊢ (u ^ v) ⟶ˢ′ (u′ ^ v)
⟶ˢ′-subst≡-head {Γ} {s} {u} {u′} {v} x x∉u x∉u′ x∉s lv fvv d
  rewrite subst-intro {u} lv x x∉u | subst-intro {u′} lv x x∉u′
  = subst (λ σ → Γ ∣ σ ⊢ ((u ^ fvar x) [ x := v ]) ⟶ˢ′ ((u′ ^ fvar x) [ x := v ]))
          (substStack-id x v s x∉s)
          (⟶ˢ′-subst≡ [] x lv fvv d)
```

## What this establishes

The four facts `MPSS/VariantCommutation` spends: dropping avoided names, the subtype lookup
along a variant context reduction with its avoidance, and substitution of an equivalence-bound
name in a subtyping reduction.
