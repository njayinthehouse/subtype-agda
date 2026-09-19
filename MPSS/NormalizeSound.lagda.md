# MPSS: the normalizer of the checker takes equivalence steps

`MPSS/CheckerFns` reduces terms by `hred`, `whnf`, `nf` and compares normal forms (`conv`). Here:
each of them, run on a locally closed term scoped in `Γ`, produces a `⟶ᵉ*`-reduct of it. Nothing
is claimed about the result being normal, and nothing needs to be: fuel that runs out returns a
reduct all the same.

β at a stack is `β₁` then `β₂` of `MPSS/PromotionNoWhnf`. Under an abstraction the body is reduced
at one fresh name and the chain is closed up step by step (`wrapᵉ-fun` of `MPSS/Wrap`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.NormalizeSound where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import MPSS.Reduction
open import MPSS.StackPush
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ)
open import MPSS.Wrap using (wrapᵉ-fun)
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_; ⟶ᵉ*-lc) renaming (_++_ to _++ᵉ_)
open import MPSS.PromotionNoWhnf using (β₁; β₂; fv-open⊑)
open import MPSS.CoPair using (_≟Tm_)
open import MPSS.CheckerFns
open import PSS.Syntax
open import PSS.Close using (close-open)
```

## Chains: scoping and congruences

```agda
Scoped : Ctx → Tm → Set
Scoped Γ t = fv t ⊑ dom Γ

⟶ᵉ*-fv : ∀ {Γ s a b} → Scoped Γ a → Γ ∣ s ⊢ a ⟶ᵉ* b → Scoped Γ b
⟶ᵉ*-fv fa (ε _)   = fa
⟶ᵉ*-fv fa (d ◅ p) = ⟶ᵉ*-fv (fv-⟶ᵉ (λ h → h) d fa) p

⟶ᵉ*-prevalid : ∀ {Γ s a b} → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s prevalid
⟶ᵉ*-prevalid (ε pv)  = pv
⟶ᵉ*-prevalid (d ◅ _) = ⟶ᵉ-prevalid d

-- in the operator, under the operand on the stack
app-l* : ∀ {Γ s a a′ v} → Γ ∣ (v ∷ s) ⊢ a ⟶ᵉ* a′ → Γ ∣ s ⊢ app a v ⟶ᵉ* app a′ v
app-l* (ε pv)  = ε (prevalid-pop pv)
app-l* (d ◅ p) =
  Me-App d (⟶ᵉ-refl (prevalid-nil pv) (prevalid-head-lc pv) (prevalid-head-fv pv)) ◅ app-l* p
  where pv = ⟶ᵉ-prevalid d

-- in the operand
app-r* : ∀ {Γ s f v v′} → Γ ∣ s prevalid → LC f → Scoped Γ f → LC v → Scoped Γ v
       → Γ ∣ [] ⊢ v ⟶ᵉ* v′ → Γ ∣ s ⊢ app f v ⟶ᵉ* app f v′
app-r* pv lf ff lv fv′ (ε _)   = ε pv
app-r* pv lf ff lv fv′ (d ◅ p) =
  Me-App (⟶ᵉ-refl (Pv-Sta pv lv fv′) lf ff) d
  ◅ app-r* pv lf ff (⟶ᵉ-lc lv d) (fv-⟶ᵉ (λ h → h) d fv′) p

-- in the annotation of an abstraction
lam-ann* : ∀ {Γ a a′ b} → LC (lam a b) → Scoped Γ (lam a b)
         → Γ ∣ [] ⊢ a ⟶ᵉ* a′ → Γ ∣ [] ⊢ lam a b ⟶ᵉ* lam a′ b
lam-ann* ll fl (ε pv) = ε pv
lam-ann* {Γ} {a} {a′} {b} ll@(lc-lam L la F) fl (d ◅ p) =
  Me-Fun {u = b} {u' = b} (L ++ dom Γ) d body ◅ lam-ann* ll′ fl′ p
  where
    pv = ⟶ᵉ-prevalid d
    fa = fv-lam-ann {a} {b} fl
    fb = fv-lam-body {a} {b} fl
    body : ∀ {x} → x ∉ (L ++ dom Γ) → ((x , sub , a) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ (b ^ fvar x)
    body {x} x∉ = ⟶ᵉ-refl (prevalid-cons pv (∉-++ʳ L x∉) la fa) (F (∉-++ˡ x∉)) (fv-open-cons {b} x fb)
    ll′ = lc-lam L (⟶ᵉ-lc la d) F
    fl′ = fv-⟶ᵉ {t = lam a b} (λ h → h) (Me-Fun {u = b} {u' = b} (L ++ dom Γ) d body) fl

-- in the body of an abstraction, the chain given at one fresh name
lam-body* : ∀ {Γ a p q} x → x ∉ dom Γ → LC p
          → ((x , sub , a) ∷ Γ) ∣ [] ⊢ p ⟶ᵉ* q
          → Γ ∣ [] ⊢ lam a (closeRec 0 x p) ⟶ᵉ* lam a (closeRec 0 x q)
lam-body* x x∉ lp (ε pv)  = ε (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
lam-body* x x∉ lp (d ◅ r) =
  wrapᵉ-fun x x∉ lp (⟶ᵉ-lc lp d) d ◅ lam-body* x x∉ (⟶ᵉ-lc lp d) r
```

## Head reduction

```agda
hred-sound : ∀ {Γ s} t {t′} → Γ ∣ s prevalid → LC t → Scoped Γ t
           → hred t ≡ just t′ → Γ ∣ s ⊢ t ⟶ᵉ* t′
hred-sound (app (lam a b) v) pv (lc-app ll lv) ft refl =
  β₁ pv ll (fv-app-op {lam a b} {v} ft) lv (fv-app-arg {lam a b} {v} ft)
  ◅ (β₂ pv ll (fv-app-op {lam a b} {v} ft) lv (fv-app-arg {lam a b} {v} ft) ◅ ε pv)
hred-sound (app Top v) pv lt ft refl = Me-TAp pv ◅ ε pv
hred-sound (app (app f u) v) pv (lc-app lfu lv) ft e with hred (app f u) in eq
hred-sound (app (app f u) v) pv (lc-app lfu lv) ft refl | just r =
  app-l* (hred-sound (app f u) (Pv-Sta pv lv (fv-app-arg {app f u} {v} ft)) lfu
                     (fv-app-op {app f u} {v} ft) eq)
hred-sound (app (app f u) v) pv (lc-app lfu lv) ft () | nothing
hred-sound (app (bvar _) v) pv lt ft ()
hred-sound (app (fvar _) v) pv lt ft ()
hred-sound (bvar _)  pv lt ft ()
hred-sound (fvar _)  pv lt ft ()
hred-sound Top       pv lt ft ()
hred-sound (lam _ _) pv lt ft ()

whnf-sound : ∀ m {Γ s t} → Γ ∣ s prevalid → LC t → Scoped Γ t → Γ ∣ s ⊢ t ⟶ᵉ* whnf m t
whnf-sound zero    pv lt ft = ε pv
whnf-sound (suc m) {t = t} pv lt ft with hred t in eq
... | nothing = ε pv
... | just t′ = p ++ᵉ whnf-sound m pv (⟶ᵉ*-lc lt p) (⟶ᵉ*-fv ft p)
  where p = hred-sound t pv lt ft eq
```

## Normalization

```agda
nf-sound  : ∀ m {Γ t} → Γ prevalid → LC t → Scoped Γ t → Γ ∣ [] ⊢ t ⟶ᵉ* nf m (dom Γ) t
nfw-sound : ∀ m {Γ} t → Γ prevalid → LC t → Scoped Γ t → Γ ∣ [] ⊢ t ⟶ᵉ* nfw m (dom Γ) t
nfs-sound : ∀ m {Γ s} t → Γ ∣ s prevalid → LC t → Scoped Γ t → Γ ∣ s ⊢ t ⟶ᵉ* nfs m (dom Γ) t

nf-sound zero    pv lt ft = ε (Pv-Nil pv)
nf-sound (suc m) {t = t} pv lt ft =
  p ++ᵉ nfw-sound m (whnf m t) pv (⟶ᵉ*-lc lt p) (⟶ᵉ*-fv ft p)
  where p = whnf-sound m (Pv-Nil pv) lt ft

nfw-sound m {Γ} (lam a b) pv ll@(lc-lam L la F) fl =
  subst (λ q → Γ ∣ [] ⊢ lam a q ⟶ᵉ* lam a (closeRec 0 x nb)) (close-open 0 x b x∉b)
        (lam-body* x x∉Γ lbx body)
  ++ᵉ lam-ann* ll′ fl′ (nf-sound m pv la fa)
  where
    A   = dom Γ ++ fv b
    x   = fresh A
    x∉Γ = ∉-++ˡ (fresh-∉ A)
    x∉b = ∉-++ʳ (dom Γ) (fresh-∉ A)
    fa  = fv-lam-ann {a} {b} fl
    lbx : LC (b ^ fvar x)
    lbx = open-lc {a} {b} ll lc-fvar
    pvx : ((x , sub , a) ∷ Γ) prevalid
    pvx = Pv-Ctx pv x∉Γ la fa
    body : ((x , sub , a) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ* nf m (x ∷ dom Γ) (b ^ fvar x)
    body = nf-sound m pvx lbx (fv-open-cons {b} x (fv-lam-body {a} {b} fl))
    nb  = nf m (x ∷ dom Γ) (b ^ fvar x)
    first : Γ ∣ [] ⊢ lam a b ⟶ᵉ* lam a (closeRec 0 x nb)
    first = subst (λ q → Γ ∣ [] ⊢ lam a q ⟶ᵉ* lam a (closeRec 0 x nb)) (close-open 0 x b x∉b)
                  (lam-body* x x∉Γ lbx body)
    ll′ : LC (lam a (closeRec 0 x nb))
    ll′ = ⟶ᵉ*-lc ll first
    fl′ : Scoped Γ (lam a (closeRec 0 x nb))
    fl′ = ⟶ᵉ*-fv fl first
nfw-sound m (app f v) pv lt ft = nfs-sound m (app f v) (Pv-Nil pv) lt ft
nfw-sound m (bvar i)  pv lt ft = ε (Pv-Nil pv)
nfw-sound m (fvar x)  pv lt ft = ε (Pv-Nil pv)
nfw-sound m Top       pv lt ft = ε (Pv-Nil pv)

nfs-sound m (app f v) pv (lc-app lf lv) ft =
  app-l* pf ++ᵉ app-r* pv (⟶ᵉ*-lc lf pf) (⟶ᵉ*-fv ff pf) lv fv′ (nf-sound m (prevalid-ctx pv) lv fv′)
  where
    ff  = fv-app-op {f} {v} ft
    fv′ = fv-app-arg {f} {v} ft
    pf  = nfs-sound m f (Pv-Sta pv lv fv′) lf ff
nfs-sound m (bvar i)  pv lt ft = ε pv
nfs-sound m (fvar x)  pv lt ft = ε pv
nfs-sound m Top       pv lt ft = ε pv
nfs-sound m (lam a b) pv lt ft = ε pv
```

## Conversion

```agda
Joins : Ctx → Tm → Tm → Set
Joins Γ a b = ∃[ c ] ((Γ ∣ [] ⊢ a ⟶ᵉ* c) × (Γ ∣ [] ⊢ b ⟶ᵉ* c))

conv-sound : ∀ m {Γ a b} → Γ prevalid → LC a → Scoped Γ a → LC b → Scoped Γ b
           → conv m (dom Γ) a b ≡ true → Joins Γ a b
conv-sound m {Γ} {a} {b} pv la fa lb fb e with nf m (dom Γ) a ≟Tm nf m (dom Γ) b
conv-sound m {Γ} {a} {b} pv la fa lb fb e | yes q =
  nf m (dom Γ) b , subst (λ c → Γ ∣ [] ⊢ a ⟶ᵉ* c) q (nf-sound m pv la fa) , nf-sound m pv lb fb
conv-sound m pv la fa lb fb () | no _
```

## What this establishes

`hred-sound`, `whnf-sound`, `nf-sound`: the checker's reductions are chains of equivalence steps,
at any stack for head reduction and at the empty stack for normalization. `conv-sound`: two terms
the checker finds convertible have a common `⟶ᵉ*`-reduct.
