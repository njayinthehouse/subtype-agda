# MPSS: subtyping reduction over the variant, and its chains

`⟶ˢ′` is `⟶ˢ` with `Ms-Equ` embedding the variant `⟶ᵉ′` instead of `⟶ᵉ`; the other rules are
unchanged. A `⟶ˢ′` step is a `⟶ˢ` step, and a `⟶ˢ` step is a chain of `⟶ˢ′` steps: the embedded
equivalence step becomes its chain (`MPSS/Peel`), and the congruences carry chains under an
application and under a binder. As for the equivalence relation, building a chain under a binder
needs renaming of the fresh name, transcribed from `MPSS/Rename` and `MPSS/Wrap`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantSub where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import PSS.Syntax
open import PSS.Close using (open-close; close-open; fv-close)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-rename; ⟶ᵉ′-prevalid; ⟶ᵉ′-lc)
open import MPSS.VariantChain using (_∣_⊢_⟶ᵉ′*_; ε′; _◅′_)
open import MPSS.Peel using (⟶ᵉ⊆⟶ᵉ′*)
open import MPSS.Rename using (prevalid-rename; ∈-substCtx; substCtx; substStack; substStack-id;
                               x∉-w; x∉-domΔ; x∉-domΓ; x∉-boundΓ; open-rename)
open import MPSS.Scope using (⟶ˢ-lc)
```

## The relation

```agda
infix 3 _∣_⊢_⟶ˢ′_
data _∣_⊢_⟶ˢ′_ : Ctx → Stack → Tm → Tm → Set where

  Ms-Pro′ : ∀ {Γ s x t}
          → Γ ∣ s prevalid
          → x ≤ t ∈ Γ
          → Γ ∣ s ⊢ fvar x ⟶ˢ′ t

  Ms-Top′ : ∀ {Γ s u}
          → Γ ∣ s prevalid
          → Γ ∣ s ⊢ u ⟶ˢ′ Top

  Ms-Equ′ : ∀ {Γ s u v}
          → Γ ∣ s prevalid
          → Γ ∣ s ⊢ u ⟶ᵉ′ v
          → Γ ∣ s ⊢ u ⟶ˢ′ v

  Ms-App′ : ∀ {Γ s u u' v}
          → Γ ∣ (v ∷ s) ⊢ u ⟶ˢ′ u'
          → Γ ∣ s ⊢ app u v ⟶ˢ′ app u' v

  Ms-Fun′ : ∀ {Γ t u u'} (L : List Name)
          → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶ˢ′ (u' ^ fvar x))
          → Γ ∣ [] ⊢ lam t u ⟶ˢ′ lam t u'

  Ms-FOp′ : ∀ {Γ s α t u u'} (L : List Name)
          → (∀ {x} → x ∉ L → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (u ^ fvar x) ⟶ˢ′ (u' ^ fvar x))
          → Γ ∣ (α ∷ s) ⊢ lam t u ⟶ˢ′ lam t u'

⟶ˢ′⊆⟶ˢ : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ˢ′ v → Γ ∣ s ⊢ u ⟶ˢ v
⟶ˢ′⊆⟶ˢ (Ms-Pro′ pv m)   = Ms-Pro pv m
⟶ˢ′⊆⟶ˢ (Ms-Top′ pv)     = Ms-Top pv
⟶ˢ′⊆⟶ˢ (Ms-Equ′ pv e)   = Ms-Equ pv (⟶ᵉ′⊆⟶ᵉ e)
⟶ˢ′⊆⟶ˢ (Ms-App′ d)      = Ms-App (⟶ˢ′⊆⟶ˢ d)
⟶ˢ′⊆⟶ˢ (Ms-Fun′ {u' = u'} L F) = Ms-Fun {u' = u'} L (λ x∉ → ⟶ˢ′⊆⟶ˢ (F x∉))
⟶ˢ′⊆⟶ˢ (Ms-FOp′ {u' = u'} L F) = Ms-FOp {u' = u'} L (λ x∉ → ⟶ˢ′⊆⟶ˢ (F x∉))

⟶ˢ′-prevalid : ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ˢ′ v → Γ ∣ s prevalid
⟶ˢ′-prevalid d = ⟶ˢ-prevalid (⟶ˢ′⊆⟶ˢ d)

⟶ˢ′-lc : ∀ {Γ s u v} → LC u → Γ ∣ s ⊢ u ⟶ˢ′ v → LC v
⟶ˢ′-lc lu d = ⟶ˢ-lc lu (⟶ˢ′⊆⟶ˢ d)
```

## Renaming

```agda
⟶ˢ′-rename : ∀ (Δ : Ctx) {Γ x y a w s u v}
           → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
           → (Δ ++ (x , a , w) ∷ Γ) ∣ s ⊢ u ⟶ˢ′ v
           → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
               ⊢ (u [ x := fvar y ]) ⟶ˢ′ (v [ x := fvar y ])

⟶ˢ′-rename Δ {Γ} {x} {y} {a} {w} {s} y∉ (Ms-Pro′ {_} {_} {z} {t} pv mem)
  with ∈-++⁻ Δ mem
... | inj₁ m = pro-Δ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ (prevalid-ctx pv) (subst (_∈ dom Δ) (sym p) (∈-dom m))

    pro-Δ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ˢ′ (t [ x := fvar y ])
    pro-Δ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Ms-Pro′ (prevalid-rename Δ y∉ pv) (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m))
... | inj₂ (here refl) = pro-self
  where
    pro-self : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                 ⊢ ((fvar x) [ x := fvar y ]) ⟶ˢ′ (w [ x := fvar y ])
    pro-self rewrite subst-fvar-≡ {x} (fvar y)
                   | subst-fresh {w} x (fvar y) (x∉-w Δ (prevalid-ctx pv)) =
      Ms-Pro′ (prevalid-rename Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl))
... | inj₂ (there m) = pro-Γ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ (prevalid-ctx pv) (subst (_∈ dom Γ) (sym p) (∈-dom m))

    pro-Γ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ˢ′ (t [ x := fvar y ])
    pro-Γ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z
                | subst-fresh {t} x (fvar y) (x∉-boundΓ Δ (prevalid-ctx pv) m) =
      Ms-Pro′ (prevalid-rename Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m))

⟶ˢ′-rename Δ y∉ (Ms-Top′ pv) = Ms-Top′ (prevalid-rename Δ y∉ pv)

⟶ˢ′-rename Δ y∉ (Ms-Equ′ pv e) = Ms-Equ′ (prevalid-rename Δ y∉ pv) (⟶ᵉ′-rename Δ y∉ e)

⟶ˢ′-rename Δ y∉ (Ms-App′ d) = Ms-App′ (⟶ˢ′-rename Δ y∉ d)

⟶ˢ′-rename Δ {Γ} {x} {y} {a} {w} y∉ (Ms-Fun′ {_} {t} {u} {u'} L F) =
  Ms-Fun′ (x ∷ y ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ′ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ′-rename ((z , sub , t) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , sub , t) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        transport : ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ˢ′ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ′ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h

⟶ˢ′-rename Δ {Γ} {x} {y} {a} {w} y∉ (Ms-FOp′ {_} {s} {β} {t} {u} {u'} L F) =
  Ms-FOp′ (x ∷ y ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
             ∣ substStack x (fvar y) s
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ′ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ′-rename ((z , eqv , β) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , eqv , β) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        transport : ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ˢ′ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ′ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h

⟶ˢ′-rename-head : ∀ {Γ s b w a α} x y
                → x ∉ dom Γ → y ∉ dom Γ → x ∉ fv α → x ∉ fv b → x ∉ fvStack s → LC w
                → ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ′ w
                → ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ˢ′ ((closeRec 0 x w) ^ fvar y)
⟶ˢ′-rename-head {Γ} {s} {b} {w} {a} {α} x y x∉Γ y∉Γ x∉α x∉b x∉s lw d with x ≟ y
... | yes refl = d'
  where
    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ′ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d
... | no x≢y = result
  where
    y∉ : y ∉ dom ([] ++ (x , a , α) ∷ Γ)
    y∉ (here p)  = x≢y (sym p)
    y∉ (there h) = y∉Γ h

    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ′ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d

    renamed : ((y , a , α) ∷ Γ) ∣ substStack x (fvar y) s
                ⊢ ((b ^ fvar x) [ x := fvar y ]) ⟶ˢ′ (((closeRec 0 x w) ^ fvar x) [ x := fvar y ])
    renamed = ⟶ˢ′-rename [] y∉ d'

    result : ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ˢ′ ((closeRec 0 x w) ^ fvar y)
    result rewrite sym (substStack-id x (fvar y) s x∉s)
                 | subst-intro {b} (lc-fvar {y}) x x∉b
                 | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
                 = renamed
```

## Wrapping a single step under a binder

```agda
wrapˢ′-fun : ∀ {Γ w a a′} x → x ∉ dom Γ → LC a → LC a′
           → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ˢ′ a′
           → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ˢ′ lam w (closeRec 0 x a′)
wrapˢ′-fun {Γ} {w} {a} {a′} x x∉Γ la la′ d = Ms-Fun′ (dom Γ) fam
  where
    pv = prevalid-ctx (⟶ˢ′-prevalid d)

    d′ : ((x , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ˢ′ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , sub , w) ∷ Γ) ∣ [] ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ˢ′ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ˢ′-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) (λ ()) la′ d′

wrapˢ′-fop : ∀ {Γ s w α a a′} x → x ∉ dom Γ → x ∉ fvStack s → LC a → LC a′
           → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ˢ′ a′
           → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ˢ′ lam w (closeRec 0 x a′)
wrapˢ′-fop {Γ} {s} {w} {α} {a} {a′} x x∉Γ x∉s la la′ d = Ms-FOp′ (dom Γ) fam
  where
    pv = prevalid-ctx (⟶ˢ′-prevalid d)

    d′ : ((x , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ˢ′ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ˢ′ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ˢ′-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) x∉s la′ d′
```

## Chains, and their congruences

```agda
infixr 5 _◅ˢ′_
infix 3 _∣_⊢_⟶ˢ′*_
data _∣_⊢_⟶ˢ′*_ : Ctx → Stack → Tm → Tm → Set where
  εˢ′   : ∀ {Γ s a} → Γ ∣ s prevalid → Γ ∣ s ⊢ a ⟶ˢ′* a
  _◅ˢ′_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ˢ′ b → Γ ∣ s ⊢ b ⟶ˢ′* c → Γ ∣ s ⊢ a ⟶ˢ′* c

_++ˢ′_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ˢ′* b → Γ ∣ s ⊢ b ⟶ˢ′* c → Γ ∣ s ⊢ a ⟶ˢ′* c
εˢ′ _      ++ˢ′ q = q
(d ◅ˢ′ p)  ++ˢ′ q = d ◅ˢ′ (p ++ˢ′ q)

⟶ˢ′*-prevalid : ∀ {Γ s a b} → Γ ∣ s ⊢ a ⟶ˢ′* b → Γ ∣ s prevalid
⟶ˢ′*-prevalid (εˢ′ pv)  = pv
⟶ˢ′*-prevalid (d ◅ˢ′ _) = ⟶ˢ′-prevalid d

equ-chain : ∀ {Γ s a c} → Γ ∣ s ⊢ a ⟶ᵉ′* c → Γ ∣ s ⊢ a ⟶ˢ′* c
equ-chain (ε′ pv)  = εˢ′ pv
equ-chain (d ◅′ p) = Ms-Equ′ (⟶ᵉ′-prevalid d) d ◅ˢ′ equ-chain p

⟶ˢ′*-app : ∀ {Γ s v a c} → Γ ∣ (v ∷ s) ⊢ a ⟶ˢ′* c → Γ ∣ s ⊢ app a v ⟶ˢ′* app c v
⟶ˢ′*-app (εˢ′ pv)   = εˢ′ (prevalid-pop pv)
⟶ˢ′*-app (d ◅ˢ′ p)  = Ms-App′ d ◅ˢ′ ⟶ˢ′*-app p

⟶ˢ′*-fun : ∀ {Γ w a c} x → x ∉ dom Γ → LC a
         → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ˢ′* c
         → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ˢ′* lam w (closeRec 0 x c)
⟶ˢ′*-fun x x∉ la (εˢ′ pv)   = εˢ′ (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
⟶ˢ′*-fun x x∉ la (d ◅ˢ′ p)  =
  wrapˢ′-fun x x∉ la (⟶ˢ′-lc la d) d ◅ˢ′ ⟶ˢ′*-fun x x∉ (⟶ˢ′-lc la d) p

⟶ˢ′*-fop : ∀ {Γ s w α a c} x → x ∉ dom Γ → x ∉ fvStack s → LC a
         → Γ ∣ (α ∷ s) prevalid
         → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ˢ′* c
         → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ˢ′* lam w (closeRec 0 x c)
⟶ˢ′*-fop x x∉ x∉s la pvα (εˢ′ _)   = εˢ′ pvα
⟶ˢ′*-fop x x∉ x∉s la pvα (d ◅ˢ′ p) =
  wrapˢ′-fop x x∉ x∉s la (⟶ˢ′-lc la d) d ◅ˢ′ ⟶ˢ′*-fop x x∉ x∉s (⟶ˢ′-lc la d) pvα p
```

## An original subtyping step is a chain of variant steps

```agda
⟶ˢ⊆⟶ˢ′* : ∀ {Γ s t t′} → LC t → Γ ∣ s ⊢ t ⟶ˢ t′ → Γ ∣ s ⊢ t ⟶ˢ′* t′
⟶ˢ⊆⟶ˢ′* lt (Ms-Pro pv m) = Ms-Pro′ pv m ◅ˢ′ εˢ′ pv
⟶ˢ⊆⟶ˢ′* lt (Ms-Top pv)   = Ms-Top′ pv ◅ˢ′ εˢ′ pv
⟶ˢ⊆⟶ˢ′* lt (Ms-Equ pv e) = equ-chain (⟶ᵉ⊆⟶ᵉ′* lt e)
⟶ˢ⊆⟶ˢ′* (lc-app lu lv) (Ms-App d) = ⟶ˢ′*-app (⟶ˢ⊆⟶ˢ′* lu d)
⟶ˢ⊆⟶ˢ′* {Γ} (lc-lam {t} {u} L₁ lt F₁) (Ms-Fun {u' = u′} L F) = result
  where
    A    = L ++ L₁ ++ dom Γ ++ fv u ++ fv u′
    x    = fresh A
    x∉L  : x ∉ L
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉L₁ : x ∉ L₁
    x∉L₁ = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    x∉Γ  : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))
    x∉u  : x ∉ fv u
    x∉u  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))

    chain : Γ ∣ [] ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ˢ′* lam t (closeRec 0 x (u′ ^ fvar x))
    chain = ⟶ˢ′*-fun x x∉Γ (F₁ x∉L₁) (⟶ˢ⊆⟶ˢ′* (F₁ x∉L₁) (F x∉L))

    result : Γ ∣ [] ⊢ lam t u ⟶ˢ′* lam t u′
    result = subst₂ (λ a b → Γ ∣ [] ⊢ lam t a ⟶ˢ′* lam t b)
                    (close-open 0 x u x∉u) (close-open 0 x u′ x∉u′) chain
⟶ˢ⊆⟶ˢ′* {Γ} {α ∷ s} (lc-lam {t} {u} L₁ lt F₁) (Ms-FOp {u' = u′} L F) = result
  where
    A    = L ++ L₁ ++ dom Γ ++ fv u ++ fv u′ ++ fvStack s
    x    = fresh A
    x∉L  : x ∉ L
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉L₁ : x ∉ L₁
    x∉L₁ = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    x∉Γ  : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))
    x∉u  : x ∉ fv u
    x∉u  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))))
    x∉s  : x ∉ fvStack s
    x∉s  = ∉-++ʳ (fv u′) (∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))))

    pvα : Γ ∣ (α ∷ s) prevalid
    pvα = ⟶ˢ-prevalid (Ms-FOp {Γ} {s} {α} {t} {u} {u′} L F)

    chain : Γ ∣ (α ∷ s) ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ˢ′* lam t (closeRec 0 x (u′ ^ fvar x))
    chain = ⟶ˢ′*-fop x x∉Γ x∉s (F₁ x∉L₁) pvα (⟶ˢ⊆⟶ˢ′* (F₁ x∉L₁) (F x∉L))

    result : Γ ∣ (α ∷ s) ⊢ lam t u ⟶ˢ′* lam t u′
    result = subst₂ (λ a b → Γ ∣ (α ∷ s) ⊢ lam t a ⟶ˢ′* lam t b)
                    (close-open 0 x u x∉u) (close-open 0 x u′ x∉u′) chain
```

## What this establishes

`⟶ˢ′`, with `⟶ˢ′ ⊆ ⟶ˢ` and `⟶ˢ ⊆ ⟶ˢ′*` on locally closed subjects: the two subtyping reductions
have the same reflexive-transitive closure, as the two equivalence reductions do.
