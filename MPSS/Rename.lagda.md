# MPSS: renaming a bound variable in a reduction derivation

Both reductions of MPSS bind their parameter cofinitely: `Me-Fun`, `Me-FOp`, `Ms-Fun` and
`Ms-FOp` quantify the body's fresh name over the complement of a finite set. Any proof that
*builds* such a derivation — a diamond, a commutation, a substitution lemma — gets the body at
one fresh name and has to hand back the whole family. The transport is a renaming lemma: a
derivation under `x` (bound anywhere in the context, with either annotation) is a derivation
under a fresh `y`, once `x` is renamed to `y` in the term, the later entries of the context, and
the stack.

This is the MPSS counterpart of `../PSS/Rename`. The differences are the ones the calculus
forces: context entries carry an annotation kind, `Me-Pro` reads `≡` entries and `Ms-Pro` reads
`≤` entries, and the renamed variable may be looked up by either — so both lookups of `x` become
lookups of `y`, with the bound unchanged because a bound recorded before `x` cannot mention `x`.

```agda
{-# OPTIONS --safe #-}

module MPSS.Rename where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import PSS.Syntax
  using (closeRec; subst-open; subst-intro; subst-fresh; subst-lc; subst-fvar-≡; subst-fvar-≢)
open import PSS.Close using (open-close; fv-close)
open import PSS.Promotion using (fv-subst)
open import MPSS.Reduction
open import MPSS.StackPush using (prevalid-cons; dom-++)
```

## Substitution on contexts and stacks

The context is `Δ ++ (x , a , w) ∷ Γ`, most recent entry first: `Δ` holds the entries bound
*after* `x`, which are the ones a substitution for `x` can touch. Names and annotation kinds are
kept; only the annotation terms change.

```agda
substCtx : Name → Tm → Ctx → Ctx
substCtx x v = map (λ p → (proj₁ p , proj₁ (proj₂ p) , (proj₂ (proj₂ p)) [ x := v ]))

substStack : Name → Tm → Stack → Stack
substStack x v = map (_[ x := v ])

dom-substCtx : ∀ x v Δ → dom (substCtx x v Δ) ≡ dom Δ
dom-substCtx x v []                = refl
dom-substCtx x v ((z , _ , _) ∷ Δ) = cong (z ∷_) (dom-substCtx x v Δ)

∈-substCtx : ∀ x v {z b t} (Δ : Ctx)
           → (z , b , t) ∈ Δ → (z , b , t [ x := v ]) ∈ substCtx x v Δ
∈-substCtx x v (_ ∷ Δ) (here refl) = here refl
∈-substCtx x v (_ ∷ Δ) (there m)   = there (∈-substCtx x v Δ m)
```

## Re-scoping under a renaming

Membership in the domain of the original context, split around the entry for `x`; and
membership in the domain of the renamed context, joined from the same pieces around `y`.

```agda
∈-dom-split : ∀ (Δ : Ctx) {Γ x a w z}
            → z ∈ dom (Δ ++ (x , a , w) ∷ Γ)
            → (z ∈ dom Δ) ⊎ (z ∈ x ∷ dom Γ)
∈-dom-split Δ {Γ} {x} {a} {w} {z} h =
  ∈-++⁻ (dom Δ) (subst (z ∈_) (dom-++ Δ ((x , a , w) ∷ Γ)) h)

∈-dom-join : ∀ (Δ : Ctx) {Γ x a w z}
           → (z ∈ dom Δ) ⊎ (z ∈ x ∷ dom Γ)
           → z ∈ dom (Δ ++ (x , a , w) ∷ Γ)
∈-dom-join Δ {Γ} {x} {a} {w} {z} (inj₁ h) =
  subst (z ∈_) (sym (dom-++ Δ ((x , a , w) ∷ Γ))) (∈-++⁺ˡ h)
∈-dom-join Δ {Γ} {x} {a} {w} {z} (inj₂ h) =
  subst (z ∈_) (sym (dom-++ Δ ((x , a , w) ∷ Γ))) (∈-++⁺ʳ (dom Δ) h)

∈-dom-split-r : ∀ x y a w (Δ : Ctx) {Γ z}
              → z ∈ dom (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)
              → (z ∈ dom Δ) ⊎ (z ∈ y ∷ dom Γ)
∈-dom-split-r x y a w Δ {Γ} {z} h
  with ∈-++⁻ (dom (substCtx x (fvar y) Δ))
             (subst (z ∈_) (dom-++ (substCtx x (fvar y) Δ) ((y , a , w) ∷ Γ)) h)
... | inj₁ q = inj₁ (subst (z ∈_) (dom-substCtx x (fvar y) Δ) q)
... | inj₂ q = inj₂ q

∈-dom-join-r : ∀ x y a w (Δ : Ctx) {Γ z}
             → (z ∈ dom Δ) ⊎ (z ∈ y ∷ dom Γ)
             → z ∈ dom (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)
∈-dom-join-r x y a w Δ {Γ} {z} (inj₁ h) =
  subst (z ∈_) (sym (dom-++ (substCtx x (fvar y) Δ) ((y , a , w) ∷ Γ)))
        (∈-++⁺ˡ (subst (z ∈_) (sym (dom-substCtx x (fvar y) Δ)) h))
∈-dom-join-r x y a w Δ {Γ} {z} (inj₂ h) =
  subst (z ∈_) (sym (dom-++ (substCtx x (fvar y) Δ) ((y , a , w) ∷ Γ)))
        (∈-++⁺ʳ (dom (substCtx x (fvar y) Δ)) h)
```

A term scoped over the original context is, after renaming, scoped over the renamed one; and a
name absent from the original domain and distinct from `y` is absent from the renamed domain.

```agda
⊑-rename : ∀ {Γ a w} x y (Δ : Ctx) {t}
         → fv t ⊑ dom (Δ ++ (x , a , w) ∷ Γ)
         → fv (t [ x := fvar y ]) ⊑ dom (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)
⊑-rename {Γ} {a} {w} x y Δ {t} fvt {z} z∈ with fv-subst x (fvar y) t z∈
... | inj₂ (here p)     = ∈-dom-join-r x y a w Δ (inj₂ (here p))
... | inj₁ (q , z≢x) with ∈-dom-split Δ (fvt q)
...   | inj₁ r          = ∈-dom-join-r x y a w Δ (inj₁ r)
...   | inj₂ (here p)   = ⊥-elim (z≢x p)
...   | inj₂ (there p)  = ∈-dom-join-r x y a w Δ (inj₂ (there p))

∉-rename : ∀ x y a w (Δ : Ctx) {Γ z}
         → z ∉ dom (Δ ++ (x , a , w) ∷ Γ) → z ≢ y
         → z ∉ dom (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)
∉-rename x y a w Δ z∉ z≢y h with ∈-dom-split-r x y a w Δ h
... | inj₁ q         = z∉ (∈-dom-join Δ (inj₁ q))
... | inj₂ (here p)  = z≢y p
... | inj₂ (there q) = z∉ (∈-dom-join Δ (inj₂ (there q)))
```

## Structural facts about prevalidity

The renamed variable is bound nowhere in `Δ`, nowhere in `Γ`, and is free in no annotation of
`Γ` — in particular not in its own bound `w`. All four follow from the head of a prevalid
context being fresh for its tail.

```agda
head-∉ : ∀ {Γ z b t} → ((z , b , t) ∷ Γ) prevalid → z ∉ dom Γ
head-∉ (Pv-Ctx _ n _ _) = n
head-∉ (Pv-EqA _ n _ _) = n

prevalid-suffix : ∀ (Δ : Ctx) {Γ} → (Δ ++ Γ) prevalid → Γ prevalid
prevalid-suffix []      p = p
prevalid-suffix (_ ∷ Δ) p = prevalid-suffix Δ (tail-prevalid p)

x∈-mid : ∀ (Δ : Ctx) {Γ x a w} → x ∈ dom (Δ ++ (x , a , w) ∷ Γ)
x∈-mid Δ = ∈-dom-join Δ (inj₂ (here refl))

x∉-domΔ : ∀ (Δ : Ctx) {Γ x a w} → (Δ ++ (x , a , w) ∷ Γ) prevalid → x ∉ dom Δ
x∉-domΔ []                p ()
x∉-domΔ ((z , b , t) ∷ Δ) {Γ} {x} {a} {w} p (here q) =
  head-∉ p (subst (_∈ dom (Δ ++ (x , a , w) ∷ Γ)) q (x∈-mid Δ))
x∉-domΔ ((z , b , t) ∷ Δ) p (there h) = x∉-domΔ Δ (tail-prevalid p) h

x∉-domΓ : ∀ (Δ : Ctx) {Γ x a w} → (Δ ++ (x , a , w) ∷ Γ) prevalid → x ∉ dom Γ
x∉-domΓ Δ p = head-∉ (prevalid-suffix Δ p)

x∉-boundΓ : ∀ (Δ : Ctx) {Γ x a w z b t}
          → (Δ ++ (x , a , w) ∷ Γ) prevalid → (z , b , t) ∈ Γ → x ∉ fv t
x∉-boundΓ Δ p m h =
  x∉-domΓ Δ p (prevalid-bound-fv (tail-prevalid (prevalid-suffix Δ p)) m h)

x∉-w : ∀ (Δ : Ctx) {Γ x a w} → (Δ ++ (x , a , w) ∷ Γ) prevalid → x ∉ fv w
x∉-w Δ p h = x∉-domΓ Δ p (head-fv (prevalid-suffix Δ p) h)
```

## Prevalidity under a renaming

First for logical contexts, then for extended ones. The entry for `x` itself keeps its bound
`w` untouched — the renaming is not applied to it — and needs only `y ∉ dom Γ`.

```agda
prevalid-rename-ctx : ∀ (Δ : Ctx) {Γ x y a w}
                    → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
                    → (Δ ++ (x , a , w) ∷ Γ) prevalid
                    → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) prevalid
prevalid-rename-ctx [] y∉ (Pv-Ctx p _ lw fw) = Pv-Ctx p (∉-tail y∉) lw fw
prevalid-rename-ctx [] y∉ (Pv-EqA p _ lw fw) = Pv-EqA p (∉-tail y∉) lw fw
prevalid-rename-ctx ((z , _ , t) ∷ Δ) {Γ} {x} {y} {a} {w} y∉ (Pv-Ctx p z∉ lt ft) =
  Pv-Ctx (prevalid-rename-ctx Δ (∉-tail y∉) p)
         (∉-rename x y a w Δ z∉ (λ q → y∉ (here (sym q))))
         (subst-lc lt lc-fvar)
         (⊑-rename x y Δ {t} ft)
prevalid-rename-ctx ((z , _ , t) ∷ Δ) {Γ} {x} {y} {a} {w} y∉ (Pv-EqA p z∉ lt ft) =
  Pv-EqA (prevalid-rename-ctx Δ (∉-tail y∉) p)
         (∉-rename x y a w Δ z∉ (λ q → y∉ (here (sym q))))
         (subst-lc lt lc-fvar)
         (⊑-rename x y Δ {t} ft)

prevalid-rename : ∀ (Δ : Ctx) {Γ x y a w s}
                → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
                → (Δ ++ (x , a , w) ∷ Γ) ∣ s prevalid
                → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s prevalid
prevalid-rename Δ y∉ (Pv-Nil p) = Pv-Nil (prevalid-rename-ctx Δ y∉ p)
prevalid-rename Δ {x = x} {y = y} y∉ (Pv-Sta {α = α} p lα fα) =
  Pv-Sta (prevalid-rename Δ y∉ p) (subst-lc lα lc-fvar) (⊑-rename x y Δ {α} fα)
```

## Two computation facts

Renaming a free variable yields a free variable; and renaming commutes with opening at a name
other than the one renamed, which is `subst-open` specialised to `fvar y`.

```agda
rename-fvar : ∀ x y z → ∃[ z' ] ((fvar z) [ x := fvar y ] ≡ fvar z')
rename-fvar x y z with x ≟ z
... | yes _ = y , refl
... | no  _ = z , refl

open-rename : ∀ {x z} y → x ≢ z → ∀ t
            → ((t ^ fvar z) [ x := fvar y ]) ≡ ((t [ x := fvar y ]) ^ fvar z)
open-rename {x} {z} y x≢z t =
  trans (subst-open (lc-fvar {y}) 0 (fvar z) t x)
        (cong (λ q → openRec 0 q (t [ x := fvar y ])) (subst-fvar-≢ (fvar y) x≢z))
```

## The renaming lemma for `⟶ᵉ`

By induction on the derivation. `Me-Pro` is the case with content: the variable looked up is
either bound in `Δ` (its bound is renamed along with it), or is `x` itself (the lookup becomes a
lookup of `y`, and the bound `w` is unchanged since `x ∉ fv w`), or is bound in `Γ` (untouched,
since `x` occurs in no annotation of `Γ`). The binder cases choose a body name avoiding `x` and
`y` and apply the induction hypothesis with the new entry prepended to `Δ`; `Me-Bet` reduces its
body at the unextended context, so `Δ` is unchanged there.

```agda
⟶ᵉ-rename : ∀ (Δ : Ctx) {Γ x y a w s u v}
          → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
          → (Δ ++ (x , a , w) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v
          → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ (u [ x := fvar y ]) ⟶ᵉ (v [ x := fvar y ])

⟶ᵉ-rename Δ {Γ} {x} {y} y∉ (Me-Var {x = z} pv)
  rewrite proj₂ (rename-fvar x y z) = Me-Var (prevalid-rename Δ y∉ pv)

⟶ᵉ-rename Δ y∉ (Me-Top pv) = Me-Top (prevalid-rename Δ y∉ pv)

⟶ᵉ-rename Δ y∉ (Me-TAp pv) = Me-TAp (prevalid-rename Δ y∉ pv)

⟶ᵉ-rename Δ {Γ} {x} {y} {a} {w} {s} y∉ (Me-Pro {_} {_} {z} {α} {α'} pv mem d)
  with ∈-++⁻ Δ mem
... | inj₁ m = pro-Δ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ (prevalid-ctx pv) (subst (_∈ dom Δ) (sym p) (∈-dom m))

    pro-Δ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ᵉ (α' [ x := fvar y ])
    pro-Δ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Me-Pro (prevalid-rename Δ y∉ pv)
             (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m))
             (⟶ᵉ-rename Δ y∉ d)
... | inj₂ (here refl) = pro-self
  where
    ih : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
           ⊢ w ⟶ᵉ (α' [ x := fvar y ])
    ih = subst (λ q → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                        ⊢ q ⟶ᵉ (α' [ x := fvar y ]))
               (subst-fresh {w} x (fvar y) (x∉-w Δ (prevalid-ctx pv)))
               (⟶ᵉ-rename Δ y∉ d)

    pro-self : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                 ⊢ ((fvar x) [ x := fvar y ]) ⟶ᵉ (α' [ x := fvar y ])
    pro-self rewrite subst-fvar-≡ {x} (fvar y) =
      Me-Pro (prevalid-rename Δ y∉ pv)
             (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl))
             ih
... | inj₂ (there m) = pro-Γ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ (prevalid-ctx pv) (subst (_∈ dom Γ) (sym p) (∈-dom m))

    ih : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
           ⊢ α ⟶ᵉ (α' [ x := fvar y ])
    ih = subst (λ q → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                        ⊢ q ⟶ᵉ (α' [ x := fvar y ]))
               (subst-fresh {α} x (fvar y) (x∉-boundΓ Δ (prevalid-ctx pv) m))
               (⟶ᵉ-rename Δ y∉ d)

    pro-Γ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ᵉ (α' [ x := fvar y ])
    pro-Γ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Me-Pro (prevalid-rename Δ y∉ pv)
             (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m))
             ih

⟶ᵉ-rename Δ y∉ (Me-App d e) = Me-App (⟶ᵉ-rename Δ y∉ d) (⟶ᵉ-rename Δ y∉ e)

⟶ᵉ-rename Δ {Γ} {x} {y} {a} {w} {s} y∉ (Me-Bet {_} {_} {t} {u} {u'} {v} {v'} L F e) = result
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-rename Δ y∉ (F (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        transport : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ᵉ ((u' ^ fvar z) [ x := fvar y ])
                  → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h

    result : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
               ⊢ ((app (lam t u) v) [ x := fvar y ]) ⟶ᵉ ((u' ^ v') [ x := fvar y ])
    result rewrite subst-open (lc-fvar {y}) 0 v' u' x =
      Me-Bet {u' = u' [ x := fvar y ]} (x ∷ L) body (⟶ᵉ-rename Δ y∉ e)

⟶ᵉ-rename Δ {Γ} {x} {y} {a} {w} y∉ (Me-Fun {_} {t} {t'} {u} {u'} L d F) =
  Me-Fun (x ∷ y ∷ L) (⟶ᵉ-rename Δ y∉ d) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-rename ((z , sub , t) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , sub , t) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        transport : ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ᵉ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h

⟶ᵉ-rename Δ {Γ} {x} {y} {a} {w} y∉ (Me-FOp {_} {s} {β} {t} {t'} {u} {u'} L d F) =
  Me-FOp (x ∷ y ∷ L) (⟶ᵉ-rename Δ y∉ d) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
             ∣ substStack x (fvar y) s
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ᵉ-rename ((z , eqv , β) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
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
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ᵉ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ᵉ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h
```

## The renaming lemma for `⟶ˢ`

The same three-way split at `Ms-Pro`, now on `≤` entries; `Ms-Equ` defers to `⟶ᵉ-rename`.

```agda
⟶ˢ-rename : ∀ (Δ : Ctx) {Γ x y a w s u v}
          → y ∉ dom (Δ ++ (x , a , w) ∷ Γ)
          → (Δ ++ (x , a , w) ∷ Γ) ∣ s ⊢ u ⟶ˢ v
          → (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ (u [ x := fvar y ]) ⟶ˢ (v [ x := fvar y ])

⟶ˢ-rename Δ {Γ} {x} {y} {a} {w} {s} y∉ (Ms-Pro {_} {_} {z} {t} pv mem)
  with ∈-++⁻ Δ mem
... | inj₁ m = pro-Δ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΔ Δ (prevalid-ctx pv) (subst (_∈ dom Δ) (sym p) (∈-dom m))

    pro-Δ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ˢ (t [ x := fvar y ])
    pro-Δ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z =
      Ms-Pro (prevalid-rename Δ y∉ pv) (∈-++⁺ˡ (∈-substCtx x (fvar y) Δ m))
... | inj₂ (here refl) = pro-self
  where
    pro-self : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
                 ⊢ ((fvar x) [ x := fvar y ]) ⟶ˢ (w [ x := fvar y ])
    pro-self rewrite subst-fvar-≡ {x} (fvar y)
                   | subst-fresh {w} x (fvar y) (x∉-w Δ (prevalid-ctx pv)) =
      Ms-Pro (prevalid-rename Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (here refl))
... | inj₂ (there m) = pro-Γ
  where
    x≢z : x ≢ z
    x≢z p = x∉-domΓ Δ (prevalid-ctx pv) (subst (_∈ dom Γ) (sym p) (∈-dom m))

    pro-Γ : (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ) ∣ substStack x (fvar y) s
              ⊢ ((fvar z) [ x := fvar y ]) ⟶ˢ (t [ x := fvar y ])
    pro-Γ rewrite subst-fvar-≢ {x} {z} (fvar y) x≢z
                | subst-fresh {t} x (fvar y) (x∉-boundΓ Δ (prevalid-ctx pv) m) =
      Ms-Pro (prevalid-rename Δ y∉ pv) (∈-++⁺ʳ (substCtx x (fvar y) Δ) (there m))

⟶ˢ-rename Δ y∉ (Ms-Top pv) = Ms-Top (prevalid-rename Δ y∉ pv)

⟶ˢ-rename Δ y∉ (Ms-Equ pv e) = Ms-Equ (prevalid-rename Δ y∉ pv) (⟶ᵉ-rename Δ y∉ e)

⟶ˢ-rename Δ y∉ (Ms-App d) = Ms-App (⟶ˢ-rename Δ y∉ d)

⟶ˢ-rename Δ {Γ} {x} {y} {a} {w} y∉ (Ms-Fun {_} {t} {u} {u'} L F) =
  Ms-Fun (x ∷ y ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ-rename ((z , sub , t) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        y≢z : y ≢ z
        y≢z p = z∉ (there (here (sym p)))

        y∉' : y ∉ dom ((z , sub , t) ∷ (Δ ++ (x , a , w) ∷ Γ))
        y∉' (here p)  = y≢z p
        y∉' (there h) = y∉ h

        transport : ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ˢ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , sub , t [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ)) ∣ []
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h

⟶ˢ-rename Δ {Γ} {x} {y} {a} {w} y∉ (Ms-FOp {_} {s} {β} {t} {u} {u'} L F) =
  Ms-FOp (x ∷ y ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ y ∷ L)
         → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
             ∣ substStack x (fvar y) s
             ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ ((u' [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (⟶ˢ-rename ((z , eqv , β) ∷ Δ) y∉' (F (∉-tail (∉-tail z∉))))
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
                      ⊢ ((u ^ fvar z) [ x := fvar y ]) ⟶ˢ ((u' ^ fvar z) [ x := fvar y ])
                  → ((z , eqv , β [ x := fvar y ]) ∷ (substCtx x (fvar y) Δ ++ (y , a , w) ∷ Γ))
                      ∣ substStack x (fvar y) s
                      ⊢ ((u [ x := fvar y ]) ^ fvar z) ⟶ˢ ((u' [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym (open-rename y x≢z u) | sym (open-rename y x≢z u') = h
```

## Substituting for an absent name

A stack, or a context, in which `x` does not occur free is unchanged by substituting for it.
The free variables of a context's annotation terms are collected like those of a stack.

```agda
substStack-id : ∀ x v s → x ∉ fvStack s → substStack x v s ≡ s
substStack-id x v []      x∉ = refl
substStack-id x v (α ∷ s) x∉ =
  cong₂ _∷_ (subst-fresh {α} x v (∉-++ˡ x∉))
            (substStack-id x v s (∉-++ʳ (fv α) x∉))

fvCtx : Ctx → List Name
fvCtx []                = []
fvCtx ((_ , _ , t) ∷ Δ) = fv t ++ fvCtx Δ

substCtx-id : ∀ x v Δ → x ∉ fvCtx Δ → substCtx x v Δ ≡ Δ
substCtx-id x v []                x∉ = refl
substCtx-id x v ((z , b , t) ∷ Δ) x∉ =
  cong₂ _∷_ (cong (λ q → (z , b , q)) (subst-fresh {t} x v (∉-++ˡ x∉)))
            (substCtx-id x v Δ (∉-++ʳ (fv t) x∉))
```

## The form the binder cases use

At the head of the context, with the term in opened form: a derivation from `b ^ fvar x` to an
arbitrary locally closed `w` becomes, at any `y` fresh for `Γ`, a derivation from `b ^ fvar y`
to the body `closeRec 0 x w` opened at `y`. When `y` is `x` itself this is `open-close`;
otherwise `b ^ fvar y` is `(b ^ fvar x) [ x := fvar y ]` by `subst-intro`, `w` is
`(closeRec 0 x w) ^ fvar x` by `open-close`, and the renaming lemma applies with `Δ = []`.

```agda
⟶ᵉ-rename-head : ∀ {Γ s b w a α} x y
               → x ∉ dom Γ → y ∉ dom Γ → x ∉ fv α → x ∉ fv b → x ∉ fvStack s → LC w
               → ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ w
               → ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ᵉ ((closeRec 0 x w) ^ fvar y)
⟶ᵉ-rename-head {Γ} {s} {b} {w} {a} {α} x y x∉Γ y∉Γ x∉α x∉b x∉s lw d with x ≟ y
... | yes refl = d'
  where
    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d
... | no x≢y = result
  where
    y∉ : y ∉ dom ([] ++ (x , a , α) ∷ Γ)
    y∉ (here p)  = x≢y (sym p)
    y∉ (there h) = y∉Γ h

    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d

    renamed : ((y , a , α) ∷ Γ) ∣ substStack x (fvar y) s
                ⊢ ((b ^ fvar x) [ x := fvar y ]) ⟶ᵉ (((closeRec 0 x w) ^ fvar x) [ x := fvar y ])
    renamed = ⟶ᵉ-rename [] y∉ d'

    result : ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ᵉ ((closeRec 0 x w) ^ fvar y)
    result rewrite sym (substStack-id x (fvar y) s x∉s)
                 | subst-intro {b} (lc-fvar {y}) x x∉b
                 | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
                 = renamed

⟶ˢ-rename-head : ∀ {Γ s b w a α} x y
               → x ∉ dom Γ → y ∉ dom Γ → x ∉ fv α → x ∉ fv b → x ∉ fvStack s → LC w
               → ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ w
               → ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ˢ ((closeRec 0 x w) ^ fvar y)
⟶ˢ-rename-head {Γ} {s} {b} {w} {a} {α} x y x∉Γ y∉Γ x∉α x∉b x∉s lw d with x ≟ y
... | yes refl = d'
  where
    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d
... | no x≢y = result
  where
    y∉ : y ∉ dom ([] ++ (x , a , α) ∷ Γ)
    y∉ (here p)  = x≢y (sym p)
    y∉ (there h) = y∉Γ h

    d' : ((x , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ ((closeRec 0 x w) ^ fvar x)
    d' rewrite open-close lw 0 x = d

    renamed : ((y , a , α) ∷ Γ) ∣ substStack x (fvar y) s
                ⊢ ((b ^ fvar x) [ x := fvar y ]) ⟶ˢ (((closeRec 0 x w) ^ fvar x) [ x := fvar y ])
    renamed = ⟶ˢ-rename [] y∉ d'

    result : ((y , a , α) ∷ Γ) ∣ s ⊢ (b ^ fvar y) ⟶ˢ ((closeRec 0 x w) ^ fvar y)
    result rewrite sym (substStack-id x (fvar y) s x∉s)
                 | subst-intro {b} (lc-fvar {y}) x x∉b
                 | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
                 = renamed
```

## What this establishes

- `substCtx`, `substStack`: substitution on MPSS contexts (annotation terms only; names and
  kinds kept) and on stacks, with `dom-substCtx` and `∈-substCtx`.
- `prevalid-rename`: prevalidity of an extended context is stable under renaming a bound
  variable, bound anywhere in the context with either annotation kind, to a name fresh for the
  whole domain.
- `⟶ᵉ-rename`, `⟶ˢ-rename`: both reductions of MPSS are stable under the same renaming, applied
  to the term, the later entries of the context, and the stack.
- `substStack-id`, `substCtx-id`: substituting for a name absent from a stack, or from a
  context's annotations (`fvCtx`), is the identity.
- `⟶ᵉ-rename-head`, `⟶ˢ-rename-head`: a derivation from a body opened at one fresh name `x`,
  with any locally closed target `w`, yields for every `y ∉ dom Γ` a derivation from the body
  opened at `y` to `closeRec 0 x w` opened at `y` — the shape needed to turn a single fresh-name
  derivation into a cofinite family under `Me-Fun`, `Me-FOp`, `Ms-Fun` and `Ms-FOp`. No
  hypothesis `x ≢ y` is needed; the case `y ≡ x` is `open-close`.
