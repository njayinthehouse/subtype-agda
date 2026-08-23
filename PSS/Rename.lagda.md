# System λ⊲: renaming a bound variable in a promotion derivation

Theorem 4.5's binder cases produce a joining term at *one* fresh name and must hand back a
cofinitely quantified family. Closing recovers the body (as in `PSS.Diamond`), but transporting
the promotion derivation from the chosen name to an arbitrary one needs a renaming lemma for
`⟶≤` — the promotion analogue of `⟶≡-rename`.

It is not an instance of Lemma B.9: that substitutes a variable by its bound and *removes* the
binding, whereas renaming keeps the binding and only changes its name.

```agda
{-# OPTIONS --safe #-}

module PSS.Rename where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Close
open import PSS.Equivalence
open import PSS.Promotion
open import PSS.WellFormed using (fvStack)
```

## Re-scoping under a renaming

```agda
∈-dom-join-r : ∀ x y δ (Δ : Ctx) {Γ z} → (z ∈ dom Δ) ⊎ (z ∈ y ∷ dom Γ)
             → z ∈ dom (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ)
∈-dom-join-r x y δ Δ {Γ} {z} (inj₁ h) =
  subst (z ∈_) (sym (dom-++ (substCtx x (fvar y) Δ) ((y , δ) ∷ Γ)))
        (∈-++⁺ˡ (subst (z ∈_) (sym (dom-substCtx x (fvar y) Δ)) h))
∈-dom-join-r x y δ Δ {Γ} {z} (inj₂ h) =
  subst (z ∈_) (sym (dom-++ (substCtx x (fvar y) Δ) ((y , δ) ∷ Γ)))
        (∈-++⁺ʳ (dom (substCtx x (fvar y) Δ)) h)

⊑-rename : ∀ {Γ δ} x y (Δ : Ctx) {t}
         → fv t ⊑ dom (Δ ++ (x , δ) ∷ Γ)
         → fv (t [ x := fvar y ]) ⊑ dom (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ)
⊑-rename {Γ} {δ} x y Δ {t} fvt {z} z∈ with fv-subst x (fvar y) t z∈
... | inj₂ (here p)     = ∈-dom-join-r x y δ Δ (inj₂ (here p))
... | inj₁ (q , z≢x) with ∈-dom-split Δ (fvt q)
...   | inj₁ r          = ∈-dom-join-r x y δ Δ (inj₁ r)
...   | inj₂ (here p)   = ⊥-elim (z≢x p)
...   | inj₂ (there p)  = ∈-dom-join-r x y δ Δ (inj₂ (there p))
```

## Prevalidity under a renaming

```agda
prevalid-rename : ∀ {Γ s δ} x y (Δ : Ctx)
                → y ∉ dom (Δ ++ (x , δ) ∷ Γ)
                → (Δ ++ (x , δ) ∷ Γ) ∣ s prevalid
                → (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ) ∣ substStack x (fvar y) s prevalid
prevalid-rename x y [] y∉ (P-Ctx2 p _ lδ fvδ) =
  P-Ctx2 p (λ h → y∉ (there h)) lδ fvδ
prevalid-rename {Γ} {δ = δ} x y ((z , t) ∷ Δ) y∉ (P-Ctx2 p z∉ lt fvt) =
  P-Ctx2 (prevalid-rename x y Δ (λ h → y∉ (there h)) p)
         z∉'
         (subst-lc lt lc-fvar)
         (⊑-rename x y Δ {t} fvt)
  where
    z≢y : z ≢ y
    z≢y q = y∉ (here (sym q))

    z∉' : z ∉ dom (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ)
    z∉' h with ∈-++⁻ (dom (substCtx x (fvar y) Δ))
                     (subst (z ∈_) (dom-++ (substCtx x (fvar y) Δ) ((y , δ) ∷ Γ)) h)
    ... | inj₁ q         = z∉ (subst (z ∈_) (sym (dom-++ Δ ((x , δ) ∷ Γ)))
                                    (∈-++⁺ˡ (subst (z ∈_) (dom-substCtx x (fvar y) Δ) q)))
    ... | inj₂ (here q)  = z≢y q
    ... | inj₂ (there q) = z∉ (subst (z ∈_) (sym (dom-++ Δ ((x , δ) ∷ Γ)))
                                    (∈-++⁺ʳ (dom Δ) (there q)))
prevalid-rename x y Δ y∉ (P-Ctx3 {α = α} p lα fvα) =
  P-Ctx3 (prevalid-rename x y Δ y∉ p) (subst-lc lα lc-fvar) (⊑-rename x y Δ {α} fvα)
```

## The renaming lemma for `⟶≤`

Same six cases as Lemma B.9, but the binding survives. `Srs-Prom` on the renamed variable finds
the renamed binding, and its bound is untouched because a bound recorded before `x` cannot
mention `x`.

```agda
⟶≤-rename : ∀ {Γ s u u' δ} x y (Δ : Ctx)
          → y ∉ dom (Δ ++ (x , δ) ∷ Γ)
          → x ∉ fv δ
          → (Δ ++ (x , δ) ∷ Γ) ∣ s ⊢ u ⟶≤ u'
          → (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ (u [ x := fvar y ]) ⟶≤ (u' [ x := fvar y ])

⟶≤-rename {Γ} {s} {δ = δ} x y Δ y∉ x∉δ (Srs-Prom {_} {_} {z} {t} pv mem)
  with ∈-++⁻ Δ mem
... | inj₁ m = prom-Δ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ pv (subst (_∈ dom Δ) (sym p) (∈-dom-of m))
      where
        ∈-dom-of : ∀ {Δ' w u} → (w , u) ∈ Δ' → w ∈ dom Δ'
        ∈-dom-of (here refl) = here refl
        ∈-dom-of (there q)   = there (∈-dom-of q)

    prom-Δ : (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ) ∣ substStack x (fvar y) s
               ⊢ ((fvar z) [ x := fvar y ]) ⟶≤ (t [ x := fvar y ])
    prom-Δ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Srs-Prom (prevalid-rename x y Δ y∉ pv) (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m))

⟶≤-rename {Γ} {s} {δ = δ} x y Δ y∉ x∉δ (Srs-Prom {_} {_} {z} {t} pv mem)
    | inj₂ (here refl) = prom-self
  where
    prom-self : (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ) ∣ substStack x (fvar y) s
                  ⊢ ((fvar x) [ x := fvar y ]) ⟶≤ (δ [ x := fvar y ])
    prom-self rewrite subst-fvar-≡ {x} (fvar y) | subst-fresh {δ} x (fvar y) x∉δ =
      Srs-Prom (prevalid-rename x y Δ y∉ pv)
               (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl))

⟶≤-rename {Γ} {s} {δ = δ} x y Δ y∉ x∉δ (Srs-Prom {_} {_} {z} {t} pv mem)
    | inj₂ (there m) = prom-Γ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ pv (subst (_∈ dom Γ) (sym p) (∈-dom-of m))
      where
        ∈-dom-of : ∀ {Γ' w u} → (w , u) ∈ Γ' → w ∈ dom Γ'
        ∈-dom-of (here refl) = here refl
        ∈-dom-of (there q)   = there (∈-dom-of q)

    prom-Γ : (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ) ∣ substStack x (fvar y) s
               ⊢ ((fvar z) [ x := fvar y ]) ⟶≤ (t [ x := fvar y ])
    prom-Γ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z
                 | subst-fresh {t} x (fvar y) (x∉-boundΓ Δ pv m) =
      Srs-Prom (prevalid-rename x y Δ y∉ pv)
               (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m))

⟶≤-rename x y Δ y∉ x∉δ (Srs-Top pv) = Srs-Top (prevalid-rename x y Δ y∉ pv)

⟶≤-rename x y Δ y∉ x∉δ (Srs-Eq pv e) =
  Srs-Eq (prevalid-rename x y Δ y∉ pv) (⟶≡-subst x lc-fvar lc-fvar e Cr-Var)

⟶≤-rename x y Δ y∉ x∉δ (Srs-App d) = Srs-App (⟶≤-rename x y Δ y∉ x∉δ d)

⟶≤-rename {Γ} {δ = δ} x y Δ y∉ x∉δ (Srs-Fun {_} {t} {u} {u'} L F) =
  Srs-Fun (x ∷ y ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ)) ∣ []
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶≤ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶≤-rename x y ((z , t) ∷ Δ) y∉' x∉δ
                                       (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , t) ∷ (Δ ++ (x , δ) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        eq : ∀ w → ((w ^ fvar z) [ x := fvar y ]) ≡ ((w [ x := fvar y ]) ^ fvar z)
        eq w = trans (subst-open lc-fvar 0 (fvar z) w x)
                     (cong (λ q → openRec 0 q (w [ x := fvar y ])) (subst-fvar-≢ (fvar y) x≢z))

        transport : ((z , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ)) ∣ []
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶≤ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ)) ∣ []
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶≤ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (eq u) | sym (eq u') = h

⟶≤-rename {Γ} {δ = δ} x y Δ y∉ x∉δ (Srs-FunOp {_} {s} {α} {t} {u} {u'} L F) =
  Srs-FunOp (x ∷ y ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , α [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ))
             ∣ substStack x (fvar y) s
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶≤ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶≤-rename x y ((z , α) ∷ Δ) y∉' x∉δ
                                       (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , α) ∷ (Δ ++ (x , δ) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        eq : ∀ w → ((w ^ fvar z) [ x := fvar y ]) ≡ ((w [ x := fvar y ]) ^ fvar z)
        eq w = trans (subst-open lc-fvar 0 (fvar z) w x)
                     (cong (λ q → openRec 0 q (w [ x := fvar y ])) (subst-fvar-≢ (fvar y) x≢z))

        transport : ((z , α [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶≤ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , α [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , δ) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶≤ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (eq u) | sym (eq u') = h
```

A stack containing no free occurrence of `x` is unchanged by substituting for it.

```agda
substStack-id : ∀ x v s → x ∉ fvStack s → substStack x v s ≡ s
substStack-id x v []      x∉ = refl
substStack-id x v (α ∷ s) x∉ =
  cong₂ _∷_ (subst-fresh {α} x v (∉-++ˡ x∉))
            (substStack-id x v s (∉-++ʳ (fv α) x∉))
```

## The form Theorem 4.5 uses

At the head of the context, with the term in opened form.

```agda
⟶≤-rename-head : ∀ {Γ s b w δ} x y
               → y ∉ dom Γ → y ≢ x
               → x ∉ fv δ → x ∉ fv b
               → LC w
               → ((x , δ) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶≤ w
               → x ∉ fvStack s
               → ((y , δ) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶≤ ((closeRec 0 x w) ^ fvar y)
⟶≤-rename-head {Γ} {s} {b} {w} {δ} x y y∉Γ y≢x x∉δ x∉b lw d x∉s = result
  where
    y∉ : y ∉ dom ([] ++ (x , δ) ∷ Γ)
    y∉ (here p)  = y≢x p
    y∉ (there h) = y∉Γ h

    d' : ((x , δ) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶≤ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d

    renamed : ((y , δ) ∷ Γ) ∣ substStack x (fvar y) s
                ⊢ ((b ^ fvar x) [ x := fvar y ]) ⟶≤ (((closeRec 0 x w) ^ fvar x) [ x := fvar y ])
    renamed = ⟶≤-rename x y [] y∉ x∉δ d'

    result : ((y , δ) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶≤ ((closeRec 0 x w) ^ fvar y)
    result rewrite sym (substStack-id x (fvar y) s x∉s)
                 | subst-intro {b} (lc-fvar {y}) x x∉b
                 | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
                 = renamed
```


## What this establishes

Renaming for `⟶≤`, in the form Theorem 4.5's `Srs-Fun`, `Srs-FunOp` and `Cr-Beta` cases need:
a derivation obtained at one fresh name transports to any other.
