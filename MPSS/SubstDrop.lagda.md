# MPSS: substituting away a context entry

The substitution Lemmas 29, 30 and 7 all replace a variable by a term *and remove that variable's
entry from the context*. `MPSS/Subst` has the other kind — substituting a variable that was never
in the context — so the machinery here is parallel to it rather than an instance of it.

Equivalence reduction needs no side condition at all. `Me-Pro` reads only equivalence
annotations, and the entry being removed is a subtype annotation, so no rule of `⟶≡` can consult
it. That is the same observation that makes Lemma 25 easy, and it is why only promotion needs the
covariant-context hypothesis that Lemmas 29 and 30 are split by.

One case is worth naming: `Me-Var` on the substituted variable itself becomes `α ⟶≡ α`, so this
lemma needs reflexivity. That is the repaired Proposition 18, and its scoping hypothesis is
exactly the `fv α ⊆ dom Γ` already required here.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.SubstDrop where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (_≟_)

open import MPSS.WellFormed
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Rename using (substCtx; substStack; x∉-domΓ; prevalid-suffix; ∈-substCtx)
open import MPSS.Subst.Base using (dom-++)
open import MPSS.Subst28 using (Lem-28-ctx; Lem-28-stk; into; inject)

open import PSS.Syntax
  using (subst-fresh; subst-open; subst-fvar-≡; subst-fvar-≢; ∉-++ˡ; ∉-++ʳ; ∉-tail)
```

## The removed entry is the only one with its name

```agda
x∈mid : ∀ (Δ : Ctx) {Γ x c t} → x ∈ dom (Δ ++ (x , c , t) ∷ Γ)
x∈mid Δ {Γ} {x} {c} {t} = inject Δ ((x , c , t) ∷ Γ) (inj₂ (here refl))

no-eqv-x : ∀ (Δ : Ctx) {Γ x t β}
         → (Δ ++ (x , sub , t) ∷ Γ) prevalid
         → ¬ (x ≐ β ∈ (Δ ++ (x , sub , t) ∷ Γ))
no-eqv-x [] pv (here ())
no-eqv-x [] {Γ} {x} pv (there m) = x∉-domΓ [] pv (∈-dom m)
no-eqv-x ((z , sub , w) ∷ Δ) (Pv-Ctx pv z∉ _ _) (here ())
no-eqv-x ((z , sub , w) ∷ Δ) (Pv-Ctx pv z∉ _ _) (there m) = no-eqv-x Δ pv m
no-eqv-x ((z , eqv , w) ∷ Δ) (Pv-EqA pv z∉ _ _) (here refl) = z∉ (x∈mid Δ)
no-eqv-x ((z , eqv , w) ∷ Δ) (Pv-EqA pv z∉ _ _) (there m) = no-eqv-x Δ pv m

no-sub-x : ∀ (Δ : Ctx) {Γ x t w}
         → (Δ ++ (x , sub , t) ∷ Γ) prevalid
         → x ≤ w ∈ (Δ ++ (x , sub , t) ∷ Γ)
         → w ≡ t
no-sub-x [] pv (here refl) = refl
no-sub-x [] pv (there m)   = ⊥-elim (x∉-domΓ [] pv (∈-dom m))
no-sub-x ((z , sub , _) ∷ Δ) (Pv-Ctx pv z∉ _ _) (here refl) = ⊥-elim (z∉ (x∈mid Δ))
no-sub-x ((z , sub , _) ∷ Δ) (Pv-Ctx pv z∉ _ _) (there m)   = no-sub-x Δ pv m
no-sub-x ((z , eqv , _) ∷ Δ) (Pv-EqA pv z∉ _ _) (here ())
no-sub-x ((z , eqv , _) ∷ Δ) (Pv-EqA pv z∉ _ _) (there m)   = no-sub-x Δ pv m
```

## Entries in the older part are untouched by the substitution

```agda
x∉fvΓ : ∀ (Δ : Ctx) {Γ x t z b w}
      → (Δ ++ (x , sub , t) ∷ Γ) prevalid
      → (z , b , w) ∈ Γ → x ∉ fv w
x∉fvΓ Δ {Γ} {x} pv m h =
  x∉-domΓ Δ pv (prevalid-bound-fv (tail-prevalid (prevalid-suffix Δ pv)) m h)

∈-drop : ∀ (Δ : Ctx) {Γ x t α z b w}
       → (Δ ++ (x , sub , t) ∷ Γ) prevalid
       → z ≢ x
       → (z , b , w) ∈ (Δ ++ (x , sub , t) ∷ Γ)
       → (z , b , w [ x := α ]) ∈ (substCtx x α Δ ++ Γ)
∈-drop Δ {Γ} {x} {t} {α} {z} {b} {w} pv z≢x m with ∈-++⁻ Δ m
... | inj₁ p           = ∈-++⁺ˡ (∈-substCtx x α Δ p)
... | inj₂ (here refl) = ⊥-elim (z≢x refl)
... | inj₂ (there p)   =
      subst (λ q → (z , b , q) ∈ (substCtx x α Δ ++ Γ))
            (sym (subst-fresh {w} x α (x∉fvΓ Δ pv p)))
            (∈-++⁺ʳ (substCtx x α Δ) p)
```

## Equivalence reduction

```agda
⟶ᵉ-drop : ∀ (Δ : Ctx) {Γ x t α s u v}
        → LC α → fv α ⊑ dom Γ
        → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v
        → (substCtx x α Δ ++ Γ) ∣ (substStack x α s) ⊢ (u [ x := α ]) ⟶ᵉ (v [ x := α ])

⟶ᵉ-drop Δ {Γ} {x} {t} {α} lα fα (Me-Var {x = y} pv) = go (x ≟ y)
  where
    pv′ = Lem-28-stk Δ lα fα pv
    go : Dec (x ≡ y) → (substCtx x α Δ ++ Γ) ∣ _ ⊢ ((fvar y) [ x := α ]) ⟶ᵉ ((fvar y) [ x := α ])
    go (yes refl) rewrite subst-fvar-≡ {x} α =
      ⟶ᵉ-refl pv′ lα (λ h → into x α Δ Γ (inject Δ Γ (inj₂ (fα h))))
    go (no q)     rewrite subst-fvar-≢ {x} {y} α q = Me-Var pv′

⟶ᵉ-drop Δ lα fα (Me-Top pv) = Me-Top (Lem-28-stk Δ lα fα pv)

⟶ᵉ-drop Δ {Γ} {x} {t} {α} lα fα (Me-Pro {x = y} pv m d) = go (x ≟ y)
  where
    go : Dec (x ≡ y) → (substCtx x α Δ ++ Γ) ∣ _ ⊢ ((fvar y) [ x := α ]) ⟶ᵉ _
    go (yes refl) = ⊥-elim (no-eqv-x Δ (prevalid-ctx pv) m)
    go (no q)     rewrite subst-fvar-≢ {x} {y} α q =
      Me-Pro (Lem-28-stk Δ lα fα pv)
             (∈-drop Δ (prevalid-ctx pv) (λ p → q (sym p)) m)
             (⟶ᵉ-drop Δ lα fα d)

⟶ᵉ-drop Δ lα fα (Me-App d e) = Me-App (⟶ᵉ-drop Δ lα fα d) (⟶ᵉ-drop Δ lα fα e)

⟶ᵉ-drop Δ lα fα (Me-TAp pv) = Me-TAp (Lem-28-stk Δ lα fα pv)

⟶ᵉ-drop Δ {Γ} {x} {t} {α} {s} lα fα (Me-Bet {t = w} {u = u} {u' = u′} {v = v} {v' = v′} L F e) =
  transport (Me-Bet {t = w [ x := α ]} {u = u [ x := α ]} {u' = u′ [ x := α ]}
                    {v = v [ x := α ]} {v' = v′ [ x := α ]}
                    (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ)) body
                    (⟶ᵉ-drop Δ lα fα e))
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → (substCtx x α Δ ++ Γ) ∣ (substStack x α s)
             ⊢ ((u [ x := α ]) ^ fvar z) ⟶ᵉ ((u′ [ x := α ]) ^ fvar z)
    body {z} z∉ = tr (⟶ᵉ-drop Δ lα fα (F (∉-++ˡ (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lα 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))
        eq′ = trans (subst-open lα 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := α ])) (subst-fvar-≢ α x≢z))

        tr : (substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u ^ fvar z) [ x := α ]) ⟶ᵉ ((u′ ^ fvar z) [ x := α ])
           → (substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u [ x := α ]) ^ fvar z) ⟶ᵉ ((u′ [ x := α ]) ^ fvar z)
        tr h rewrite sym eq | sym eq′ = h

    transport : (substCtx x α Δ ++ Γ) ∣ (substStack x α s)
                  ⊢ app (lam (w [ x := α ]) (u [ x := α ])) (v [ x := α ])
                      ⟶ᵉ ((u′ [ x := α ]) ^ (v′ [ x := α ]))
              → (substCtx x α Δ ++ Γ) ∣ (substStack x α s)
                  ⊢ ((app (lam w u) v) [ x := α ]) ⟶ᵉ ((u′ ^ v′) [ x := α ])
    transport h rewrite subst-open lα 0 v′ u′ x = h

⟶ᵉ-drop Δ {Γ} {x} {t} {α} lα fα (Me-Fun {t = w} {t' = w′} {u = u} {u' = u′} L d F) =
  Me-Fun (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         (⟶ᵉ-drop Δ lα fα d) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
             ⊢ ((u [ x := α ]) ^ fvar z) ⟶ᵉ ((u′ [ x := α ]) ^ fvar z)
    body {z} z∉ = tr (⟶ᵉ-drop ((z , sub , w) ∷ Δ) lα fα (F (∉-++ˡ (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lα 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))
        eq′ = trans (subst-open lα 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := α ])) (subst-fvar-≢ α x≢z))

        tr : ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
               ⊢ ((u ^ fvar z) [ x := α ]) ⟶ᵉ ((u′ ^ fvar z) [ x := α ])
           → ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
               ⊢ ((u [ x := α ]) ^ fvar z) ⟶ᵉ ((u′ [ x := α ]) ^ fvar z)
        tr h rewrite sym eq | sym eq′ = h

⟶ᵉ-drop Δ {Γ} {x} {t} {α} lα fα
        (Me-FOp {s = s} {α = β} {t = w} {t' = w′} {u = u} {u' = u′} L d F) =
  Me-FOp (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         (⟶ᵉ-drop Δ lα fα d) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
             ⊢ ((u [ x := α ]) ^ fvar z) ⟶ᵉ ((u′ [ x := α ]) ^ fvar z)
    body {z} z∉ = tr (⟶ᵉ-drop ((z , eqv , β) ∷ Δ) lα fα (F (∉-++ˡ (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq  = trans (subst-open lα 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))
        eq′ = trans (subst-open lα 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := α ])) (subst-fvar-≢ α x≢z))

        tr : ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u ^ fvar z) [ x := α ]) ⟶ᵉ ((u′ ^ fvar z) [ x := α ])
           → ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u [ x := α ]) ^ fvar z) ⟶ᵉ ((u′ [ x := α ]) ^ fvar z)
        tr h rewrite sym eq | sym eq′ = h
```

## Covariant spines

> `Co ::= □ | (λx≤t.Co) | (Co t)`

Lemma 30's side condition is that the derivation is not of the form `Co[x] ⟶≤ Co[t]`. Stated on
the derivation it would have to be an index, which does not work well in Agda and is not needed:
the structural rules of `⟶≤` are exactly `Ms-App` into an operator and `Ms-Fun`/`Ms-FOp` into a
body, so every promotion derivation runs down a covariant spine to its leaf. If the *term* has no
covariant spine ending at `x`, no derivation out of it can promote `x`, and unlike the condition
on derivations this one propagates uniformly through a cofinite family.

`CoSpine x u` says `u` is `Co[x]` for some covariant `Co`. The body of an abstraction is kept
with its dangling index rather than opened, which is exactly `plug (co-fun t C)`.

```agda
data CoSpine (x : Name) : Tm → Set where
  cs-var : CoSpine x (fvar x)
  cs-fun : ∀ {t b} → CoSpine x b → CoSpine x (lam t b)
  cs-app : ∀ {a b} → CoSpine x a → CoSpine x (app a b)

coSpine? : ∀ x u → Dec (CoSpine x u)
coSpine? x (bvar i) = no (λ ())
coSpine? x (fvar y) with x ≟ y
... | yes refl = yes cs-var
... | no  q    = no (λ { cs-var → q refl })
coSpine? x Top      = no (λ ())
coSpine? x (lam t b) with coSpine? x b
... | yes c = yes (cs-fun c)
... | no  q = no (λ { (cs-fun c) → q c })
coSpine? x (app a b) with coSpine? x a
... | yes c = yes (cs-app c)
... | no  q = no (λ { (cs-app c) → q c })
```

Opening at a name other than `x` neither creates nor destroys a spine ending at `x`.

```agda
cs-open : ∀ {x} k z b → z ≢ x → CoSpine x (openRec k (fvar z) b) → CoSpine x b
cs-open {x} k z (bvar i) z≢x c with k ≟ i
cs-open {x} k z (bvar i) z≢x cs-var | yes _ = ⊥-elim (z≢x refl)
cs-open {x} k z (bvar i) z≢x ()     | no  _
cs-open k z (fvar y) z≢x c            = c
cs-open k z Top      z≢x ()
cs-open k z (lam t b) z≢x (cs-fun c)  = cs-fun (cs-open (suc k) z b z≢x c)
cs-open k z (app a b) z≢x (cs-app c)  = cs-app (cs-open k z a z≢x c)
```

## Lemma 30 — promotion under substitution, off the covariant spine

> **Lemma 30 (Promotion under substitution inside of covariant contexts).** If
> `Γ, x≤t, Γ′; s ⊢ u ⟶≤ v` and this derivation is not of the form `Γ, x≤t, Γ′; s ⊢ Co[x] ⟶≤ Co[t]`,
> then `Γ, Γ′[x\α]; s[x\α] ⊢ u[x\α] ⟶≤ v[x\α]`.

```agda
⟶ˢ-drop : ∀ (Δ : Ctx) {Γ x t α s u v}
        → LC α → fv α ⊑ dom Γ
        → ¬ CoSpine x u
        → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ˢ v
        → (substCtx x α Δ ++ Γ) ∣ (substStack x α s) ⊢ (u [ x := α ]) ⟶ˢ (v [ x := α ])

⟶ˢ-drop Δ {Γ} {x} {t} {α} lα fα ns (Ms-Pro {x = y} pv m) = go (x ≟ y)
  where
    go : Dec (x ≡ y) → (substCtx x α Δ ++ Γ) ∣ _ ⊢ ((fvar y) [ x := α ]) ⟶ˢ _
    go (yes refl) = ⊥-elim (ns cs-var)
    go (no q) rewrite subst-fvar-≢ {x} {y} α q =
      Ms-Pro (Lem-28-stk Δ lα fα pv) (∈-drop Δ (prevalid-ctx pv) (λ p → q (sym p)) m)

⟶ˢ-drop Δ lα fα ns (Ms-Top pv)   = Ms-Top (Lem-28-stk Δ lα fα pv)
⟶ˢ-drop Δ lα fα ns (Ms-Equ pv e) = Ms-Equ (Lem-28-stk Δ lα fα pv) (⟶ᵉ-drop Δ lα fα e)
⟶ˢ-drop Δ lα fα ns (Ms-App st)   = Ms-App (⟶ˢ-drop Δ lα fα (λ c → ns (cs-app c)) st)

⟶ˢ-drop Δ {Γ} {x} {t} {α} lα fα ns (Ms-Fun {t = w} {u = u} {u' = u′} L F) =
  Ms-Fun (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
             ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
    body {z} z∉ =
      tr (⟶ˢ-drop ((z , sub , w) ∷ Δ) lα fα
                  (λ c → ns (cs-fun (cs-open 0 z u z≢x c)))
                  (F (∉-++ˡ (∉-tail z∉))))
      where
        z≢x : z ≢ x
        z≢x p = z∉ (here p)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)

        eq  = trans (subst-open lα 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))
        eq′ = trans (subst-open lα 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := α ])) (subst-fvar-≢ α x≢z))

        tr : ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
               ⊢ ((u ^ fvar z) [ x := α ]) ⟶ˢ ((u′ ^ fvar z) [ x := α ])
           → ((z , sub , w [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ []
               ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
        tr h rewrite sym eq | sym eq′ = h

⟶ˢ-drop Δ {Γ} {x} {t} {α} lα fα ns
        (Ms-FOp {s = s} {α = β} {t = w} {u = u} {u' = u′} L F) =
  Ms-FOp (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv α ++ dom (Δ ++ (x , sub , t) ∷ Γ))
         → ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
             ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
    body {z} z∉ =
      tr (⟶ˢ-drop ((z , eqv , β) ∷ Δ) lα fα
                  (λ c → ns (cs-fun (cs-open 0 z u z≢x c)))
                  (F (∉-++ˡ (∉-tail z∉))))
      where
        z≢x : z ≢ x
        z≢x p = z∉ (here p)
        x≢z : x ≢ z
        x≢z p = z≢x (sym p)

        eq  = trans (subst-open lα 0 (fvar z) u x)
                    (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ α x≢z))
        eq′ = trans (subst-open lα 0 (fvar z) u′ x)
                    (cong (λ q → openRec 0 q (u′ [ x := α ])) (subst-fvar-≢ α x≢z))

        tr : ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u ^ fvar z) [ x := α ]) ⟶ˢ ((u′ ^ fvar z) [ x := α ])
           → ((z , eqv , β [ x := α ]) ∷ substCtx x α Δ ++ Γ) ∣ (substStack x α s)
               ⊢ ((u [ x := α ]) ^ fvar z) ⟶ˢ ((u′ [ x := α ]) ^ fvar z)
        tr h rewrite sym eq | sym eq′ = h
```

## What this establishes

`⟶ᵉ-drop`: equivalence reduction survives the removal of a subtype entry, unconditionally, since
no rule of `⟶≡` reads a subtype annotation.

`⟶ˢ-drop`: Lemma 30, with the side condition moved from the derivation to the term. The move is
what makes the abstraction cases go through: a condition on a derivation cannot be propagated
into a cofinite family, since different witnesses could in principle take different rules, while
`¬ CoSpine x u` is a property of `u` alone and `cs-open` carries it under the binder unchanged.
It is also the stronger hypothesis, so the lemma proved is weaker than the printed one — and it
is the form Lemma 9's case split actually supplies, since `coSpine?` decides it.
