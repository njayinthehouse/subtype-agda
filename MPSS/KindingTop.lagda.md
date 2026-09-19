# MPSS: the five kinds with `⊤` at every kind, preserved by promotion; a term of kind `S` is below no abstraction, at any stack

`MPSS/Kinding` kinds the proof-level skeleton of a term with five kinds `O, F, T, G, S`, proves
that `⟶ᵉ` preserves them, and that no abstraction has kind `S`. `MPSS/PromotionNoWhnf` then shows
that no chain of promotions takes Hurkens' paradox `H` to an abstraction — at the empty stack.
Candidate C's `Wc-App` (`MPSS/StackWf`) asks for the operator to be below an abstraction at the
stack *holding the operand*, so what is needed for `H ⊤` is the same fact at the stack `⊤ ∷ []`.
It does not follow from the fact at the empty stack by wrapping in an application.

This module proves it at every stack, directly: the kinds are also preserved by **promotion**
`⟶ˢ`, once `⊤` is given every kind.

- The relation `_⊢ᵏ⁺_∶_` is `MPSS/Kinding`'s with one more rule, `k-top : Φ ⊢ᵏ⁺ Top ∶ κ`. `Ms-Top`
  replaces a subterm on the head path by `⊤`; with `k-top` the result keeps its kind. It is still
  the case that no abstraction has kind `S` (`S-lam⁺`).
- Two conditions on the stack. `Compat⁺` is `MPSS/Kinding`'s `Compat`, except that at the kinds
  `O` and `S` nothing is asked of the stack: a term of kind `S` may sit under further operands.
  `Compatˢ` is the same without the clause that lets an arrow kind (`F`, `T`, `G`) sit at the
  empty stack: there the stack is non-empty, its head has kind `dm κ` and its tail is `Compatˢ`
  at `cd κ`. So under `Compatˢ` an abstraction of arrow kind is never at the empty stack, and
  `Ms-Fun` — which would bind the parameter by `≤` — does not apply to it.
- `sr⁺`: `⟶ᵉ` preserves kinds under `Compat⁺` (`MPSS/Kinding`'s `sr` with the cases for `k-top`).
- `srˢ`: `⟶ˢ` preserves kinds under `Compatˢ`, in a context without `≤` entries.
- `S-not-below-lam`: a locally closed term of kind `S` is not below an abstraction in the machine
  relation, at any stack, in any context without `≤` entries.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.KindingTop where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

open import MPSS.Subtyping
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
open import MPSS.AppClass using (NoSub; ns-eqv)
open import MPSS.Kinding
  using (Kind; O; F; T; G; S; Arr; aF; aT; aG; dm; cd; ext;
         _⊢ᵏ_∶_; k-any; k-var; k-lam; k-app;
         _⊆ⁿ_; ext-⊆; ⊆-ext; ext-split; ext-∈)
open import PSS.Syntax
```

## The kinding, with `⊤` at every kind

```agda
infix 3 _⊢ᵏ⁺_∶_
data _⊢ᵏ⁺_∶_ (Φ : List Name) : Tm → Kind → Set where
  k-any : ∀ {t} → Φ ⊢ᵏ⁺ t ∶ O
  k-top : ∀ {κ} → Φ ⊢ᵏ⁺ Top ∶ κ
  k-var : ∀ {x} → x ∈ Φ → Φ ⊢ᵏ⁺ fvar x ∶ F
  k-lam : ∀ {κ a b} (L : List Name) → Arr κ
        → (∀ {x} → x ∉ L → ext (dm κ) x Φ ⊢ᵏ⁺ (b ^ fvar x) ∶ cd κ)
        → Φ ⊢ᵏ⁺ lam a b ∶ κ
  k-app : ∀ {κ t v} → Arr κ
        → Φ ⊢ᵏ⁺ t ∶ κ → Φ ⊢ᵏ⁺ v ∶ dm κ
        → Φ ⊢ᵏ⁺ app t v ∶ cd κ

-- MPSS/Kinding's relation is included
embed : ∀ {Φ t κ} → Φ ⊢ᵏ t ∶ κ → Φ ⊢ᵏ⁺ t ∶ κ
embed k-any          = k-any
embed (k-var m)      = k-var m
embed (k-lam L ar B) = k-lam L ar (λ x∉ → embed (B x∉))
embed (k-app ar d e) = k-app ar (embed d) (embed e)

-- no abstraction has kind S
S-lam⁺ : ∀ {Φ a b} → ¬ (Φ ⊢ᵏ⁺ lam a b ∶ S)
S-lam⁺ (k-lam _ () _)
```

## Weakening and substitution

As in `MPSS/Kinding`; `k-top` adds one trivial case to each.

```agda
weaken⁺ : ∀ {Φ Ψ t κ} → Φ ⊆ⁿ Ψ → Φ ⊢ᵏ⁺ t ∶ κ → Ψ ⊢ᵏ⁺ t ∶ κ
weaken⁺ i k-any                  = k-any
weaken⁺ i k-top                  = k-top
weaken⁺ i (k-var m)              = k-var (i m)
weaken⁺ i (k-lam {κ = κ} L ar B) = k-lam L ar (λ {x} x∉ → weaken⁺ (ext-⊆ (dm κ) x i) (B x∉))
weaken⁺ i (k-app ar d e)         = k-app ar (weaken⁺ i d) (weaken⁺ i e)

subst-k⁺ : ∀ {Φ′ Φ t κ x v} → LC v
         → (∀ {y} → y ∈ Φ′ → (y ≡ x) ⊎ (y ∈ Φ))
         → (x ∈ Φ′ → Φ ⊢ᵏ⁺ v ∶ F)
         → Φ′ ⊢ᵏ⁺ t ∶ κ → Φ ⊢ᵏ⁺ (t [ x := v ]) ∶ κ
subst-k⁺ lv sp hv k-any = k-any
subst-k⁺ lv sp hv k-top = k-top
subst-k⁺ {x = x} {v = v} lv sp hv (k-var {x = y} m) with sp m
... | inj₁ refl = subst (λ q → _ ⊢ᵏ⁺ q ∶ F) (sym (subst-fvar-≡ v)) (hv m)
... | inj₂ n    = go (x ≟ y)
  where
    go : Dec (x ≡ y) → _ ⊢ᵏ⁺ ((fvar y) [ x := v ]) ∶ F
    go (yes refl) = subst (λ q → _ ⊢ᵏ⁺ q ∶ F) (sym (subst-fvar-≡ v)) (hv m)
    go (no ne)    = subst (λ q → _ ⊢ᵏ⁺ q ∶ F) (sym (subst-fvar-≢ v ne)) (k-var n)
subst-k⁺ {Φ′} {Φ} {x = x} {v = v} lv sp hv (k-lam {κ = κ} {b = b} L ar B) =
  k-lam (x ∷ L) ar body
  where
    body : ∀ {z} → z ∉ (x ∷ L) → ext (dm κ) z Φ ⊢ᵏ⁺ ((b [ x := v ]) ^ fvar z) ∶ cd κ
    body {z} z∉ =
      subst (λ q → ext (dm κ) z Φ ⊢ᵏ⁺ q ∶ cd κ) eq
            (subst-k⁺ lv (ext-split (dm κ) z sp)
                      (λ m → weaken⁺ (⊆-ext (dm κ) z) (hv (ext-∈ (dm κ) z x≢z m)))
                      (B (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq : (b ^ fvar z) [ x := v ] ≡ (b [ x := v ]) ^ fvar z
        eq = trans (subst-open lv 0 (fvar z) b x)
                   (cong (λ q → openRec 0 q (b [ x := v ])) (subst-fvar-≢ v x≢z))
subst-k⁺ lv sp hv (k-app ar d e) = k-app ar (subst-k⁺ lv sp hv d) (subst-k⁺ lv sp hv e)

-- instantiating a body: from the body at cofinitely many names to the body at a term
inst⁺ : ∀ {Φ κ b v} (L : List Name) → Arr κ → LC v
      → (∀ {x} → x ∉ L → ext (dm κ) x Φ ⊢ᵏ⁺ (b ^ fvar x) ∶ cd κ)
      → Φ ⊢ᵏ⁺ v ∶ dm κ
      → Φ ⊢ᵏ⁺ (b ^ v) ∶ cd κ
inst⁺ {Φ} {κ} {b} {v} L ar lv B hv =
  subst (λ q → Φ ⊢ᵏ⁺ q ∶ cd κ) (sym (subst-intro {b} lv x x∉b))
        (subst-k⁺ lv (sp ar) (hF ar) (B x∉L))
  where
    A   = L ++ fv b ++ Φ
    x   = fresh A
    x∉L = ∉-++ˡ (fresh-∉ A)
    x∉b = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    x∉Φ = ∉-++ʳ (fv b) (∉-++ʳ L (fresh-∉ A))
    sp : Arr κ → ∀ {y} → y ∈ ext (dm κ) x Φ → (y ≡ x) ⊎ (y ∈ Φ)
    sp aF m         = inj₂ m
    sp aT (here p)  = inj₁ p
    sp aT (there m) = inj₂ m
    sp aG (here p)  = inj₁ p
    sp aG (there m) = inj₂ m
    hF : Arr κ → x ∈ ext (dm κ) x Φ → Φ ⊢ᵏ⁺ v ∶ F
    hF aF m = ⊥-elim (x∉Φ m)
    hF aT _ = hv
    hF aG _ = hv
```

## The two conditions on the stack

`Compat⁺ Φ s κ`: the subject has kind `κ` and sits at the stack `s`. At `O` and at `S` nothing is
asked. At an arrow kind the stack is either empty (`c-nil`: the subject is an operand, or the
body of an abstraction met at the empty stack), or its head has kind `dm κ` and its tail is
compatible with `cd κ`.

`Compatˢ` is `Compat⁺` without `c-nil`.

```agda
data Compat⁺ (Φ : List Name) : Stack → Kind → Set where
  c-O   : ∀ {s} → Compat⁺ Φ s O
  c-S   : ∀ {s} → Compat⁺ Φ s S
  c-nil : ∀ {κ} → Compat⁺ Φ [] κ
  c-∷   : ∀ {α s κ} → Arr κ → Φ ⊢ᵏ⁺ α ∶ dm κ → Compat⁺ Φ s (cd κ) → Compat⁺ Φ (α ∷ s) κ

data Compatˢ (Φ : List Name) : Stack → Kind → Set where
  c-O : ∀ {s} → Compatˢ Φ s O
  c-S : ∀ {s} → Compatˢ Φ s S
  c-∷ : ∀ {α s κ} → Arr κ → Φ ⊢ᵏ⁺ α ∶ dm κ → Compatˢ Φ s (cd κ) → Compatˢ Φ (α ∷ s) κ

lax : ∀ {Φ s κ} → Compatˢ Φ s κ → Compat⁺ Φ s κ
lax c-O          = c-O
lax c-S          = c-S
lax (c-∷ ar d c) = c-∷ ar d (lax c)

-- under Compatˢ, a subject of arrow kind is not at the empty stack
¬arr-nil : ∀ {Φ κ} → Arr κ → ¬ Compatˢ Φ [] κ
¬arr-nil () c-O
¬arr-nil () c-S

Compat⁺-weaken : ∀ {Φ Ψ s κ} → Φ ⊆ⁿ Ψ → Compat⁺ Φ s κ → Compat⁺ Ψ s κ
Compat⁺-weaken i c-O          = c-O
Compat⁺-weaken i c-S          = c-S
Compat⁺-weaken i c-nil        = c-nil
Compat⁺-weaken i (c-∷ ar d c) = c-∷ ar (weaken⁺ i d) (Compat⁺-weaken i c)

Compatˢ-weaken : ∀ {Φ Ψ s κ} → Φ ⊆ⁿ Ψ → Compatˢ Φ s κ → Compatˢ Ψ s κ
Compatˢ-weaken i c-O          = c-O
Compatˢ-weaken i c-S          = c-S
Compatˢ-weaken i (c-∷ ar d c) = c-∷ ar (weaken⁺ i d) (Compatˢ-weaken i c)
```

## The `≡`-definitions of the context

As `MPSS/Kinding`'s `Inv`: a name that the context defines by `≡` and that is in `Φ` is defined as
a term of kind `F`.

```agda
Inv⁺ : Ctx → List Name → Set
Inv⁺ Γ Φ = ∀ {x α} → x ≐ α ∈ Γ → x ∈ Φ → Φ ⊢ᵏ⁺ α ∶ F

Inv⁺-ext : ∀ {Γ Φ} κ x → x ∉ dom Γ → Inv⁺ Γ Φ → Inv⁺ Γ (ext κ x Φ)
Inv⁺-ext {Γ} κ x x∉ inv {y} m y∈ = weaken⁺ (⊆-ext κ x) (inv m (ext-∈ κ x y≢x y∈))
  where
    y≢x : y ≢ x
    y≢x p = x∉ (subst (_∈ dom Γ) p (∈-dom m))

Inv⁺-sub : ∀ {Γ Φ t} κ x → x ∉ dom Γ → Inv⁺ Γ Φ → Inv⁺ ((x , sub , t) ∷ Γ) (ext κ x Φ)
Inv⁺-sub κ x x∉ inv (there m) y∈ = Inv⁺-ext κ x x∉ inv m y∈

Inv⁺-eqv : ∀ {Γ Φ α} κ x → x ∉ dom Γ → x ∉ Φ → Arr κ → Φ ⊢ᵏ⁺ α ∶ dm κ → Inv⁺ Γ Φ
         → Inv⁺ ((x , eqv , α) ∷ Γ) (ext (dm κ) x Φ)
Inv⁺-eqv κ x x∉ x∉Φ aF d inv (here refl) y∈ = ⊥-elim (x∉Φ y∈)
Inv⁺-eqv κ x x∉ x∉Φ aT d inv (here refl) y∈ = weaken⁺ there d
Inv⁺-eqv κ x x∉ x∉Φ aG d inv (here refl) y∈ = weaken⁺ there d
Inv⁺-eqv κ x x∉ x∉Φ ar d inv (there m)   y∈ = Inv⁺-ext (dm κ) x x∉ inv m y∈
```

## Subject reduction for `⟶ᵉ`

`MPSS/Kinding`'s `sr`. The new cases: `⊤` reduces only to `⊤`; an application reduced by `Me-TAp`
gives `⊤`, which has every kind.

```agda
sr⁺ : ∀ {Γ s Φ u u′ κ} → LC u
    → Φ ⊢ᵏ⁺ u ∶ κ → Compat⁺ Φ s κ → Inv⁺ Γ Φ
    → Γ ∣ s ⊢ u ⟶ᵉ u′ → Φ ⊢ᵏ⁺ u′ ∶ κ
sr⁺ lu k-any c inv d = k-any
sr⁺ lu k-top c inv (Me-Top _) = k-top
sr⁺ lu (k-var m) c inv (Me-Var _) = k-var m
sr⁺ lu (k-var m) c inv (Me-Pro pv mem d) =
  sr⁺ (prevalid-bound-lc (prevalid-ctx pv) mem) (inv mem m) c inv d
sr⁺ {Γ} {Φ = Φ} (lc-lam L₀ lt F₀) (k-lam {κ = κ} L ar B) c inv (Me-Fun {u' = u′} L′ d Fr) =
  k-lam (L ++ L′ ++ L₀ ++ dom Γ) ar body
  where
    body : ∀ {x} → x ∉ (L ++ L′ ++ L₀ ++ dom Γ) → ext (dm κ) x Φ ⊢ᵏ⁺ (u′ ^ fvar x) ∶ cd κ
    body {x} x∉ =
      sr⁺ (F₀ (∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L x∉)))) (B (∉-++ˡ x∉)) c-nil
          (Inv⁺-sub (dm κ) x (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉))) inv)
          (Fr (∉-++ˡ (∉-++ʳ L x∉)))
sr⁺ {Γ} {α ∷ s} {Φ} (lc-lam L₀ lt F₀) (k-lam {κ = κ} L ar B) (c-∷ _ dα c) inv
    (Me-FOp {u' = u′} L′ d Fr) =
  k-lam (L ++ L′ ++ L₀ ++ dom Γ ++ Φ) ar body
  where
    body : ∀ {x} → x ∉ (L ++ L′ ++ L₀ ++ dom Γ ++ Φ) → ext (dm κ) x Φ ⊢ᵏ⁺ (u′ ^ fvar x) ∶ cd κ
    body {x} x∉ =
      sr⁺ (F₀ (∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L x∉)))) (B (∉-++ˡ x∉))
          (Compat⁺-weaken (⊆-ext (dm κ) x) c)
          (Inv⁺-eqv κ x (∉-++ˡ (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉))))
                        (∉-++ʳ (dom Γ) (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉)))) ar dα inv)
          (Fr (∉-++ˡ (∉-++ʳ L x∉)))
sr⁺ (lc-lam L₀ lt F₀) (k-lam L () B) c-O inv (Me-FOp L′ d Fr)
sr⁺ (lc-lam L₀ lt F₀) (k-lam L () B) c-S inv (Me-FOp L′ d Fr)
sr⁺ (lc-app lu lv) (k-app ar dt dv) c inv (Me-App d e) =
  k-app ar (sr⁺ lu dt (c-∷ ar dv c) inv d) (sr⁺ lv dv c-nil inv e)
sr⁺ (lc-app lu lv) (k-app ar dt dv) c inv (Me-TAp _) = k-top
sr⁺ {Γ} {s} {Φ} (lc-app (lc-lam L₀ lt F₀) lv) (k-app {κ = κ} ar (k-lam L _ B) dv) c inv
    (Me-Bet {u' = u′} {v' = v′} L′ Fr e) =
  inst⁺ {b = u′} (L ++ L′ ++ L₀ ++ dom Γ) ar (⟶ᵉ-lc lv e) body (sr⁺ lv dv c-nil inv e)
  where
    body : ∀ {x} → x ∉ (L ++ L′ ++ L₀ ++ dom Γ) → ext (dm κ) x Φ ⊢ᵏ⁺ (u′ ^ fvar x) ∶ cd κ
    body {x} x∉ =
      sr⁺ (F₀ (∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L x∉)))) (B (∉-++ˡ x∉))
          (Compat⁺-weaken (⊆-ext (dm κ) x) c)
          (Inv⁺-ext (dm κ) x (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉))) inv)
          (Fr (∉-++ˡ (∉-++ʳ L x∉)))
```

## Subject reduction for `⟶ˢ`

In a context without `≤` entries, under `Compatˢ`. `Ms-Pro` needs a `≤` entry. `Ms-Top` gives `⊤`,
which has every kind. `Ms-Equ` is `sr⁺`. `Ms-App` pushes the operand, whose kind is `dm κ`.
`Ms-FOp` binds the parameter by `≡`, as `Me-FOp` does, and the context still has no `≤` entry.
`Ms-Fun` applies to an abstraction at the empty stack: at kind `O` the result has kind `O`; an
arrow kind is not at the empty stack under `Compatˢ`; and no abstraction has kind `S`.

```agda
srˢ : ∀ {Γ s Φ u u′ κ} → NoSub Γ → LC u
    → Φ ⊢ᵏ⁺ u ∶ κ → Compatˢ Φ s κ → Inv⁺ Γ Φ
    → Γ ∣ s ⊢ u ⟶ˢ u′ → Φ ⊢ᵏ⁺ u′ ∶ κ
srˢ ns lu k c inv (Ms-Pro _ m) = ⊥-elim (ns m)
srˢ ns lu k c inv (Ms-Top _)   = k-top
srˢ ns lu k c inv (Ms-Equ _ e) = sr⁺ lu k (lax c) inv e
srˢ ns lu k-any c inv (Ms-App d)   = k-any
srˢ ns lu k-any c inv (Ms-Fun _ _) = k-any
srˢ ns lu k-any c inv (Ms-FOp _ _) = k-any
srˢ ns (lc-app lu lv) (k-app ar dt dv) c inv (Ms-App d) =
  k-app ar (srˢ ns lu dt (c-∷ ar dv c) inv d) dv
srˢ ns lu (k-lam L ar B) c inv (Ms-Fun L′ Fr) = ⊥-elim (¬arr-nil ar c)
srˢ {Γ} {α ∷ s} {Φ} ns (lc-lam L₀ lt F₀) (k-lam {κ = κ} L ar B) (c-∷ _ dα c) inv
    (Ms-FOp {u' = u′} L′ Fr) =
  k-lam (L ++ L′ ++ L₀ ++ dom Γ ++ Φ) ar body
  where
    body : ∀ {x} → x ∉ (L ++ L′ ++ L₀ ++ dom Γ ++ Φ) → ext (dm κ) x Φ ⊢ᵏ⁺ (u′ ^ fvar x) ∶ cd κ
    body {x} x∉ =
      srˢ (ns-eqv ns) (F₀ (∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L x∉)))) (B (∉-++ˡ x∉))
          (Compatˢ-weaken (⊆-ext (dm κ) x) c)
          (Inv⁺-eqv κ x (∉-++ˡ (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉))))
                        (∉-++ʳ (dom Γ) (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉)))) ar dα inv)
          (Fr (∉-++ˡ (∉-++ʳ L x∉)))
srˢ ns (lc-lam L₀ lt F₀) (k-lam L () B) c-O inv (Ms-FOp L′ Fr)
srˢ ns (lc-lam L₀ lt F₀) (k-lam L () B) c-S inv (Ms-FOp L′ Fr)
```

## A term of kind `S` is below no abstraction

By induction on the derivation of the machine relation. `As-Refl`: the term would be an
abstraction of kind `S`. `As-Left-1`: the promoted term is locally closed (`⟶ˢ-lc`) and has kind
`S` (`srˢ`; at kind `S` the stack is unconstrained). `As-Right`: an abstraction `⟶ᵉ`-reduces only
to an abstraction (`Me-Fun`, `Me-FOp`).

```agda
data IsLam : Tm → Set where
  is-lam : ∀ {a b} → IsLam (lam a b)

⟶ᵉ-lam : ∀ {Γ s u u′} → IsLam u → Γ ∣ s ⊢ u ⟶ᵉ u′ → IsLam u′
⟶ᵉ-lam is-lam (Me-Fun _ _ _) = is-lam
⟶ᵉ-lam is-lam (Me-FOp _ _ _) = is-lam

S-not-below : ∀ {Γ s t u} → NoSub Γ → LC t → [] ⊢ᵏ⁺ t ∶ S → IsLam u
            → ¬ (Γ ∣ s ⊢ t ≤ u)
S-not-below ns lt k is-lam (As-Refl _)      = S-lam⁺ k
S-not-below ns lt k il     (As-Left-1 st d) =
  S-not-below ns (⟶ˢ-lc lt st) (srˢ ns lt k c-S (λ _ ()) st) il d
S-not-below ns lt k il     (As-Right d e)   = S-not-below ns lt k (⟶ᵉ-lam il e) d

S-not-below-lam : ∀ {Γ s t a b} → NoSub Γ → LC t → [] ⊢ᵏ⁺ t ∶ S
                → ¬ (Γ ∣ s ⊢ t ≤ lam a b)
S-not-below-lam ns lt k = S-not-below ns lt k is-lam

no-sub[] : NoSub []
no-sub[] ()

-- in the empty context, at any stack
S-not-below-lam[] : ∀ {s t a b} → LC t → [] ⊢ᵏ⁺ t ∶ S → ¬ ([] ∣ s ⊢ t ≤ lam a b)
S-not-below-lam[] = S-not-below-lam no-sub[]
```

## What this establishes

- `_⊢ᵏ⁺_∶_`: `MPSS/Kinding`'s kinds with `⊤` at every kind; `embed` includes the old relation, and
  no abstraction has kind `S` (`S-lam⁺`).
- `sr⁺`: `⟶ᵉ` preserves the kinds at every configuration whose stack is `Compat⁺` with the kind —
  in particular at any stack at all when the kind is `S`.
- `srˢ`: in a context without `≤` entries, `⟶ˢ` preserves the kinds at every configuration whose
  stack is `Compatˢ` with the kind.
- `S-not-below-lam`: in a context without `≤` entries, at any stack, a locally closed term that
  has kind `S` with no names of kind `F` in scope is not below an abstraction in the machine
  relation. Neither closedness of the term nor prevalidity of the stack is used (a derivation of
  the machine relation carries prevalidity itself).
