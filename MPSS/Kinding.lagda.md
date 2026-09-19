# MPSS: five kinds, preserved by equivalence reduction, the last of which no abstraction has

For `MPSS/PromotionNoWhnf`'s hypothesis `NR t` — no `⟶ᵉ*`-reduct of `t` is an abstraction — at
Hurkens' paradox (`MPSS/CONJ8.md` §21). Hurkens remarks that his proof never uses *ex falso*, so
`⊥` can be replaced by a variable of type `*`; a closed term whose type is a variable has no weak
head normal form, by subject reduction. Subject reduction for the source calculus is not
available for MPSS (it is what Conjecture 8 was for). But the argument needs very little of the
source typing: only the *proof-level skeleton* of the term, with every object and every
annotation left unexamined. That skeleton is simply kinded, with one recursive equation:

    O                 anything at all
    F = O → T         a proof abstracted over an object      (R₀, M₀, `let p. …`)
    T = F → G         … then over a proof
    G = F → S         … then over another proof              (L₀)
    S                 a finished proof: only ever an application

`F` occurs in its own definition, so nothing is normalizing here, and nothing needs to be. What is
needed: the kinds are preserved by `⟶ᵉ` at every configuration (`sr`), and no abstraction has
kind `S`.

A binder of kind `F` puts its name in the list `Φ`; a binder of kind `O` does not, and its
variable is only ever kinded by `k-any`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Kinding where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

open import MPSS.Reduction
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_)
open import PSS.Syntax
```

## Kinds

```agda
data Kind : Set where
  O F T G S : Kind

data Arr : Kind → Set where
  aF : Arr F
  aT : Arr T
  aG : Arr G

dm cd : Kind → Kind
dm F = O
dm T = F
dm G = F
dm _ = O
cd F = T
cd T = G
cd G = S
cd _ = O

-- the names of kind F in scope, extended at a binder
ext : Kind → Name → List Name → List Name
ext F x Φ = x ∷ Φ
ext _ x Φ = Φ

infix 3 _⊢ᵏ_∶_
data _⊢ᵏ_∶_ (Φ : List Name) : Tm → Kind → Set where
  k-any : ∀ {t} → Φ ⊢ᵏ t ∶ O
  k-var : ∀ {x} → x ∈ Φ → Φ ⊢ᵏ fvar x ∶ F
  k-lam : ∀ {κ a b} (L : List Name) → Arr κ
        → (∀ {x} → x ∉ L → ext (dm κ) x Φ ⊢ᵏ (b ^ fvar x) ∶ cd κ)
        → Φ ⊢ᵏ lam a b ∶ κ
  k-app : ∀ {κ t v} → Arr κ
        → Φ ⊢ᵏ t ∶ κ → Φ ⊢ᵏ v ∶ dm κ
        → Φ ⊢ᵏ app t v ∶ cd κ

-- no abstraction has kind S
S-lam : ∀ {Φ a b} → ¬ (Φ ⊢ᵏ lam a b ∶ S)
S-lam (k-lam _ () _)
```

## Weakening

```agda
_⊆ⁿ_ : List Name → List Name → Set
Φ ⊆ⁿ Ψ = ∀ {y} → y ∈ Φ → y ∈ Ψ

ext-⊆ : ∀ κ x {Φ Ψ} → Φ ⊆ⁿ Ψ → ext κ x Φ ⊆ⁿ ext κ x Ψ
ext-⊆ O x i = i
ext-⊆ T x i = i
ext-⊆ G x i = i
ext-⊆ S x i = i
ext-⊆ F x i (here p)  = here p
ext-⊆ F x i (there m) = there (i m)

⊆-ext : ∀ κ x {Φ} → Φ ⊆ⁿ ext κ x Φ
⊆-ext O x m = m
⊆-ext T x m = m
⊆-ext G x m = m
⊆-ext S x m = m
⊆-ext F x m = there m

weaken : ∀ {Φ Ψ t κ} → Φ ⊆ⁿ Ψ → Φ ⊢ᵏ t ∶ κ → Ψ ⊢ᵏ t ∶ κ
weaken i k-any                  = k-any
weaken i (k-var m)              = k-var (i m)
weaken i (k-lam {κ = κ} L ar B) = k-lam L ar (λ {x} x∉ → weaken (ext-⊆ (dm κ) x i) (B x∉))
weaken i (k-app ar d e)         = k-app ar (weaken i d) (weaken i e)
```

## Substitution

`Φ′` is `Φ` with possibly `x` added; if `x` is there, the term substituted for it has kind `F`.

```agda
ext-split : ∀ κ z {Φ′ Φ x} → (∀ {y} → y ∈ Φ′ → (y ≡ x) ⊎ (y ∈ Φ))
          → ∀ {y} → y ∈ ext κ z Φ′ → (y ≡ x) ⊎ (y ∈ ext κ z Φ)
ext-split O z sp m = sp m
ext-split T z sp m = sp m
ext-split G z sp m = sp m
ext-split S z sp m = sp m
ext-split F z sp (here p)  = inj₂ (here p)
ext-split F z sp (there m) with sp m
... | inj₁ e = inj₁ e
... | inj₂ n = inj₂ (there n)

ext-∈ : ∀ κ z {Φ x} → x ≢ z → x ∈ ext κ z Φ → x ∈ Φ
ext-∈ O z ne m = m
ext-∈ T z ne m = m
ext-∈ G z ne m = m
ext-∈ S z ne m = m
ext-∈ F z ne (here p)  = ⊥-elim (ne p)
ext-∈ F z ne (there m) = m

subst-k : ∀ {Φ′ Φ t κ x v} → LC v
        → (∀ {y} → y ∈ Φ′ → (y ≡ x) ⊎ (y ∈ Φ))
        → (x ∈ Φ′ → Φ ⊢ᵏ v ∶ F)
        → Φ′ ⊢ᵏ t ∶ κ → Φ ⊢ᵏ (t [ x := v ]) ∶ κ
subst-k lv sp hv k-any = k-any
subst-k {x = x} {v = v} lv sp hv (k-var {x = y} m) with sp m
... | inj₁ refl = subst (λ q → _ ⊢ᵏ q ∶ F) (sym (subst-fvar-≡ v)) (hv m)
... | inj₂ n    = go (x ≟ y)
  where
    go : Dec (x ≡ y) → _ ⊢ᵏ ((fvar y) [ x := v ]) ∶ F
    go (yes refl) = subst (λ q → _ ⊢ᵏ q ∶ F) (sym (subst-fvar-≡ v)) (hv m)
    go (no ne)    = subst (λ q → _ ⊢ᵏ q ∶ F) (sym (subst-fvar-≢ v ne)) (k-var n)
subst-k {Φ′} {Φ} {x = x} {v = v} lv sp hv (k-lam {κ = κ} {b = b} L ar B) =
  k-lam (x ∷ L) ar body
  where
    body : ∀ {z} → z ∉ (x ∷ L) → ext (dm κ) z Φ ⊢ᵏ ((b [ x := v ]) ^ fvar z) ∶ cd κ
    body {z} z∉ =
      subst (λ q → ext (dm κ) z Φ ⊢ᵏ q ∶ cd κ) eq
            (subst-k lv (ext-split (dm κ) z sp)
                     (λ m → weaken (⊆-ext (dm κ) z) (hv (ext-∈ (dm κ) z x≢z m)))
                     (B (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq : (b ^ fvar z) [ x := v ] ≡ (b [ x := v ]) ^ fvar z
        eq = trans (subst-open lv 0 (fvar z) b x)
                   (cong (λ q → openRec 0 q (b [ x := v ])) (subst-fvar-≢ v x≢z))
subst-k lv sp hv (k-app ar d e) = k-app ar (subst-k lv sp hv d) (subst-k lv sp hv e)

-- instantiating a body: from the body at cofinitely many names to the body at a term
inst : ∀ {Φ κ b v} (L : List Name) → Arr κ → LC v
     → (∀ {x} → x ∉ L → ext (dm κ) x Φ ⊢ᵏ (b ^ fvar x) ∶ cd κ)
     → Φ ⊢ᵏ v ∶ dm κ
     → Φ ⊢ᵏ (b ^ v) ∶ cd κ
inst {Φ} {κ} {b} {v} L ar lv B hv =
  subst (λ q → Φ ⊢ᵏ q ∶ cd κ) (sym (subst-intro {b} lv x x∉b))
        (subst-k lv (sp ar) (hF ar) (B x∉L))
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
    hF : Arr κ → x ∈ ext (dm κ) x Φ → Φ ⊢ᵏ v ∶ F
    hF aF m = ⊥-elim (x∉Φ m)
    hF aT _ = hv
    hF aG _ = hv
```

## Subject reduction for `⟶ᵉ`

The reduction is at a configuration. The kinds of the operands on the stack are what the kind of
the subject says they are (`Compat`), and a name that the context defines by `≡` and that is in
`Φ` is defined as a term of kind `F` (`Inv`).

```agda
Compat : List Name → Stack → Kind → Set
Compat Φ []      κ = ⊤
Compat Φ (α ∷ s) κ = Arr κ × (Φ ⊢ᵏ α ∶ dm κ) × Compat Φ s (cd κ)

Compat-weaken : ∀ {Φ Ψ} s {κ} → Φ ⊆ⁿ Ψ → Compat Φ s κ → Compat Ψ s κ
Compat-weaken []      i _             = tt
Compat-weaken (α ∷ s) i (ar , d , c) = ar , weaken i d , Compat-weaken s i c

Inv : Ctx → List Name → Set
Inv Γ Φ = ∀ {x α} → x ≐ α ∈ Γ → x ∈ Φ → Φ ⊢ᵏ α ∶ F

-- a new name, bound or not, of any kind: the old definitions are unaffected
Inv-ext : ∀ {Γ Φ} κ x → x ∉ dom Γ → Inv Γ Φ → Inv Γ (ext κ x Φ)
Inv-ext {Γ} κ x x∉ inv {y} m y∈ = weaken (⊆-ext κ x) (inv m (ext-∈ κ x y≢x y∈))
  where
    y≢x : y ≢ x
    y≢x p = x∉ (subst (_∈ dom Γ) p (∈-dom m))

Inv-sub : ∀ {Γ Φ t} κ x → x ∉ dom Γ → Inv Γ Φ → Inv ((x , sub , t) ∷ Γ) (ext κ x Φ)
Inv-sub κ x x∉ inv (there m) y∈ = Inv-ext κ x x∉ inv m y∈

Inv-eqv : ∀ {Γ Φ α} κ x → x ∉ dom Γ → x ∉ Φ → Arr κ → Φ ⊢ᵏ α ∶ dm κ → Inv Γ Φ
        → Inv ((x , eqv , α) ∷ Γ) (ext (dm κ) x Φ)
Inv-eqv κ x x∉ x∉Φ aF d inv (here refl) y∈ = ⊥-elim (x∉Φ y∈)
Inv-eqv κ x x∉ x∉Φ aT d inv (here refl) y∈ = weaken there d
Inv-eqv κ x x∉ x∉Φ aG d inv (here refl) y∈ = weaken there d
Inv-eqv κ x x∉ x∉Φ ar d inv (there m)   y∈ = Inv-ext (dm κ) x x∉ inv m y∈

sr : ∀ {Γ s Φ u u′ κ} → LC u
   → Φ ⊢ᵏ u ∶ κ → Compat Φ s κ → Inv Γ Φ
   → Γ ∣ s ⊢ u ⟶ᵉ u′ → Φ ⊢ᵏ u′ ∶ κ
sr lu k-any c inv d = k-any
sr lu (k-var m) c inv (Me-Var _) = k-var m
sr lu (k-var m) c inv (Me-Pro pv mem d) =
  sr (prevalid-bound-lc (prevalid-ctx pv) mem) (inv mem m) c inv d
sr {Γ} {Φ = Φ} (lc-lam L₀ lt F₀) (k-lam {κ = κ} L ar B) c inv (Me-Fun {u' = u′} L′ d Fr) =
  k-lam (L ++ L′ ++ L₀ ++ dom Γ) ar body
  where
    body : ∀ {x} → x ∉ (L ++ L′ ++ L₀ ++ dom Γ) → ext (dm κ) x Φ ⊢ᵏ (u′ ^ fvar x) ∶ cd κ
    body {x} x∉ =
      sr (F₀ (∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L x∉)))) (B (∉-++ˡ x∉)) tt
         (Inv-sub (dm κ) x (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉))) inv)
         (Fr (∉-++ˡ (∉-++ʳ L x∉)))
sr {Γ} {α ∷ s} {Φ} (lc-lam L₀ lt F₀) (k-lam {κ = κ} L ar B) (_ , dα , c) inv
   (Me-FOp {u' = u′} L′ d Fr) =
  k-lam (L ++ L′ ++ L₀ ++ dom Γ ++ Φ) ar body
  where
    body : ∀ {x} → x ∉ (L ++ L′ ++ L₀ ++ dom Γ ++ Φ) → ext (dm κ) x Φ ⊢ᵏ (u′ ^ fvar x) ∶ cd κ
    body {x} x∉ =
      sr (F₀ (∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L x∉)))) (B (∉-++ˡ x∉))
         (Compat-weaken s (⊆-ext (dm κ) x) c)
         (Inv-eqv κ x (∉-++ˡ (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉))))
                      (∉-++ʳ (dom Γ) (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉)))) ar dα inv)
         (Fr (∉-++ˡ (∉-++ʳ L x∉)))
sr (lc-app lu lv) (k-app ar dt dv) c inv (Me-App d e) =
  k-app ar (sr lu dt (ar , dv , c) inv d) (sr lv dv tt inv e)
sr (lc-app lu lv) (k-app () k-any dv) c inv (Me-TAp _)
sr {Γ} {s} {Φ} (lc-app (lc-lam L₀ lt F₀) lv) (k-app {κ = κ} ar (k-lam L _ B) dv) c inv
   (Me-Bet {u' = u′} {v' = v′} L′ Fr e) =
  inst {b = u′} (L ++ L′ ++ L₀ ++ dom Γ) ar (⟶ᵉ-lc lv e) body (sr lv dv tt inv e)
  where
    body : ∀ {x} → x ∉ (L ++ L′ ++ L₀ ++ dom Γ) → ext (dm κ) x Φ ⊢ᵏ (u′ ^ fvar x) ∶ cd κ
    body {x} x∉ =
      sr (F₀ (∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L x∉)))) (B (∉-++ˡ x∉))
         (Compat-weaken s (⊆-ext (dm κ) x) c)
         (Inv-ext (dm κ) x (∉-++ʳ L₀ (∉-++ʳ L′ (∉-++ʳ L x∉))) inv)
         (Fr (∉-++ˡ (∉-++ʳ L x∉)))
```

## A closed term of kind `S` reduces to no abstraction

```agda
sr* : ∀ {u u′ κ} → LC u → [] ⊢ᵏ u ∶ κ → [] ∣ [] ⊢ u ⟶ᵉ* u′ → [] ⊢ᵏ u′ ∶ κ
sr* lu k (ε _)   = k
sr* lu k (d ◅ p) = sr* (⟶ᵉ-lc lu d) (sr lu k tt (λ ()) d) p

S⇒NR : ∀ {t} → LC t → [] ⊢ᵏ t ∶ S → ∀ {w b} → ¬ ([] ∣ [] ⊢ t ⟶ᵉ* lam w b)
S⇒NR lt k p = S-lam (sr* lt k p)
```

## What this establishes

- `sr`: the kinds are preserved by `⟶ᵉ` at every configuration whose stack and `≡`-definitions
  are kinded as the subject's kind says.
- `S⇒NR`: a locally closed term of kind `S` in the empty context has no `⟶ᵉ*`-reduct that is an
  abstraction — `MPSS/PromotionNoWhnf`'s `NR`.
