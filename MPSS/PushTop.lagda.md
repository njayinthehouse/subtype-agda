# MPSS: below an abstraction at `σ`, below the same abstraction with body `⊤` at a longer stack

`MPSS/CONJ8.md` §30 asks for the machine fact (M1):

> if `Γ ∣ σ ⊢ g ≤ λd.c` then `Γ ∣ σ ++ [a] ⊢ g ≤ λd.⊤`.

This module proves it, for a locally closed `g`, and for any non-empty extension `a ∷ r` of the
stack rather than `[a]` alone (`push-top`; `M1` is the instance `r = []`).

Equivalence reduction is monotone in the stack (`MPSS/StackPush`, `pushᵉ`). Promotion is not
(`MPSS/Diff`, `push-is-false`): at the empty stack an abstraction is entered by `Ms-Fun`, which
binds the parameter by `x ≤ t` and lets `Ms-Pro` promote it in the body; at a non-empty stack it
is entered by `Ms-FOp`, which binds `x ≡ α`. So a derivation at `σ` cannot be replayed step for
step at the longer stack. The steps that fail are steps inside the body of an abstraction met
when the operands of `σ` are used up. At the longer stack such a body can be sent to `⊤` instead
(`Ms-FOp` over `Ms-Top`), and the target's body is `⊤`, so nothing is lost at the end. In between,
the later terms of the original derivation contain the promoted body, and the terms built at the
longer stack contain `⊤` in its place.

**The invariant.** `R n u u°`, for `n` the length of the stack at which `u` is read: `u°` is `u`,
except that the body of an abstraction standing where the head path of `u` has used up all `n`
operands may be `⊤` in `u°`. The head path goes through the operator of an application (one more
operand) and into the body of an abstraction (one operand fewer); operands and annotations are
off the path and are equal in `u` and `u°`. The two simulation lemmas say: a step from `u` at `s`
is matched from `u°` at `s ++ a ∷ r` by one `⟶ᵉ` step (`simᵉ`), respectively by a chain of `⟶ˢ`
steps (`simˢ`), between `R`-related terms. A body replaced by `⊤` never returns to a position
where the rules at `s` read it: that would take one more operand than `s` has. In the simulation
this shows as the case `Me-Fun`/`Ms-Fun` being the only one that meets such a body, and there the
longer stack uses `Me-FOp`/`Ms-FOp` with `⊤ ⟶ ⊤`.

The binder cases get the matching body at one fresh name and hand back the cofinite family by
closing and reopening (`MPSS/Rename`, `⟶ᵉ-rename-head`; `MPSS/Push`, `⟶ˢ*-fop`); `Me-Bet` reduces
its body at a name the context does not bind, where the reopening is by `MPSS/Open`'s substitution
lemma. `R` is closed under opening and closing, which is why it is indexed by the length of the
stack and not by the stack.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.PushTop where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.Subtyping
open import MPSS.StackPush using (pushᵉ; prevalid-cons)
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
open import MPSS.Push using (_∣_⊢_⟶ˢ*_; εˢ; _◅ˢ_; ⟶ˢ*-lc; ⟶ˢ*-app; ⟶ˢ*-fop)
open import MPSS.Rename using (⟶ᵉ-rename-head)
open import MPSS.Open using (⟶ᵉ-subst₀)
open import MPSS.Strengthen using (stack-fv)
open import PSS.Syntax using (closeRec; subst-intro)
open import PSS.Close using (open-close; close-open; fv-close)
```

## The relation

`R n u u°`: `u` read at a stack of `n` operands.

```agda
data R : ℕ → Tm → Tm → Set where
  R-refl : ∀ {n u} → R n u u
  R-app  : ∀ {n f f° v} → R (suc n) f f° → R n (app f v) (app f° v)
  R-lam  : ∀ {n t b b°} → R n b b° → R (suc n) (lam t b) (lam t b°)
  R-top  : ∀ {t b} → R 0 (lam t b) (lam t Top)
```

It is closed under opening (by any term) and under closing, at every index.

```agda
R-open : ∀ {n p q} k v → R n p q → R n (openRec k v p) (openRec k v q)
R-open k v R-refl    = R-refl
R-open k v (R-app r) = R-app (R-open k v r)
R-open k v (R-lam r) = R-lam (R-open (suc k) v r)
R-open k v R-top     = R-top

R-close : ∀ {n p q} k x → R n p q → R n (closeRec k x p) (closeRec k x q)
R-close k x R-refl    = R-refl
R-close k x (R-app r) = R-app (R-close k x r)
R-close k x (R-lam r) = R-lam (R-close (suc k) x r)
R-close k x R-top     = R-top
```

From a relation between bodies opened at a fresh name to the relation between the bodies.

```agda
R-body : ∀ {n b′ W} x → x ∉ fv b′ → R n (b′ ^ fvar x) W → R n b′ (closeRec 0 x W)
R-body {n} {b′} {W} x x∉ r =
  subst (λ z → R n z (closeRec 0 x W)) (close-open 0 x b′ x∉) (R-close 0 x r)
```

Inversions, by the shape of the left term.

```agda
R-fvar-inv : ∀ {n x q} → R n (fvar x) q → q ≡ fvar x
R-fvar-inv R-refl = refl

R-Top-inv : ∀ {n q} → R n Top q → q ≡ Top
R-Top-inv R-refl = refl

R-app-inv : ∀ {n f v q} → R n (app f v) q → ∃[ f° ] (q ≡ app f° v × R (suc n) f f°)
R-app-inv R-refl    = _ , refl , R-refl
R-app-inv (R-app r) = _ , refl , r

R-lam-inv : ∀ {n t b q} → R (suc n) (lam t b) q → ∃[ b° ] (q ≡ lam t b° × R n b b°)
R-lam-inv R-refl    = _ , refl , R-refl
R-lam-inv (R-lam r) = _ , refl , r

R-lam0-inv : ∀ {t b q} → R 0 (lam t b) q → (q ≡ lam t b) ⊎ (q ≡ lam t Top)
R-lam0-inv R-refl = inj₁ refl
R-lam0-inv R-top  = inj₂ refl

R-lam-shape : ∀ n {t b q} → R n (lam t b) q → ∃[ b° ] (q ≡ lam t b°)
R-lam-shape zero r with R-lam0-inv r
... | inj₁ e = _ , e
... | inj₂ e = _ , e
R-lam-shape (suc n) r with R-lam-inv r
... | b° , e , _ = b° , e
```

## Steps at a non-empty stack that need no premise about the body

An abstraction's body goes to `⊤`, and `λd.⊤` follows a reduction of `d`.

```agda
pv-eqv : ∀ {Γ α q x} → Γ ∣ (α ∷ q) prevalid → x ∉ dom Γ → ((x , eqv , α) ∷ Γ) ∣ q prevalid
pv-eqv pv x∉ = prevalid-cons (prevalid-pop pv) x∉ (prevalid-head-lc pv) (prevalid-head-fv pv)

top-stepˢ : ∀ {Γ α q d c} → Γ ∣ (α ∷ q) prevalid → Γ ∣ (α ∷ q) ⊢ lam d c ⟶ˢ lam d Top
top-stepˢ {Γ} {c = c} pv = Ms-FOp {u = c} {u' = Top} (dom Γ) (λ x∉ → Ms-Top (pv-eqv pv x∉))

top-stepᵉ : ∀ {Γ α q d d′} → Γ ∣ (α ∷ q) prevalid → Γ ∣ [] ⊢ d ⟶ᵉ d′
          → Γ ∣ (α ∷ q) ⊢ lam d Top ⟶ᵉ lam d′ Top
top-stepᵉ {Γ} pv e = Me-FOp {u = Top} {u' = Top} (dom Γ) e (λ x∉ → Me-Top (pv-eqv pv x∉))
```

## Reopening at a name the context does not bind

`Me-Bet` reduces its body at the unextended context. A step from the body opened at one fresh
name gives the step at every name (as `close-rename₀` of `MPSS/DiamondStep`, restated here to
keep the imports small).

```agda
reopenᵉ : ∀ {Γ s u w} x y → x ∉ dom Γ → x ∉ fv u → LC w
        → Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ w
        → Γ ∣ s ⊢ (u ^ fvar y) ⟶ᵉ ((closeRec 0 x w) ^ fvar y)
reopenᵉ {Γ} {s} {u} {w} x y x∉Γ x∉u lw d
  rewrite subst-intro {u} (lc-fvar {y}) x x∉u
        | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
  = ⟶ᵉ-subst₀ x x∉Γ lc-fvar lc-fvar d′ (Me-Var (prevalid-nil (⟶ᵉ-prevalid d)))
  where
    d′ : Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ ((closeRec 0 x w) ^ fvar x)
    d′ rewrite open-close lw 0 x = d
```

## Simulation of `⟶ᵉ`

One step for one step.

```agda
simᵉ : ∀ {Γ s a r u u′ u°}
     → Γ ∣ s ⊢ u ⟶ᵉ u′
     → R (length s) u u° → LC u°
     → Γ ∣ (s ++ a ∷ r) prevalid
     → ∃[ u°′ ] (Γ ∣ (s ++ a ∷ r) ⊢ u° ⟶ᵉ u°′ × R (length s) u′ u°′)

simᵉ (Me-Var _) rel lu pv with R-fvar-inv rel
... | refl = _ , Me-Var pv , R-refl

simᵉ (Me-Top _) rel lu pv with R-Top-inv rel
... | refl = _ , Me-Top pv , R-refl

simᵉ (Me-Pro pv₀ m d) rel lu pv with R-fvar-inv rel
... | refl = _ , pushᵉ (Me-Pro pv₀ m d) pv , R-refl

simᵉ (Me-TAp _) rel lu pv with R-app-inv rel
... | f° , refl , rel′ with R-Top-inv rel′
...   | refl = _ , Me-TAp pv , R-refl

simᵉ (Me-App d e) rel lu pv with R-app-inv rel
simᵉ (Me-App d e) rel (lc-app lf lv) pv | f° , refl , rel′
  with simᵉ d rel′ lf (Pv-Sta pv (prevalid-head-lc (⟶ᵉ-prevalid d))
                                 (prevalid-head-fv (⟶ᵉ-prevalid d)))
... | f°′ , d° , rel″ = _ , Me-App d° e , R-app rel″

simᵉ (Me-Bet L F e) rel lu pv with R-app-inv rel
... | f° , refl , rel′ with R-lam-inv rel′
simᵉ {Γ} (Me-Bet {u' = b′} {v' = v′} L F e) rel (lc-app (lc-lam L₁ lt G) lv) pv
    | f° , refl , rel′ | b° , refl , rel″ = result
  where
    A     = L ++ L₁ ++ dom Γ ++ fv b° ++ fv b′
    x     = fresh A
    x∉L   : x ∉ L
    x∉L   = ∉-++ˡ (fresh-∉ A)
    q₁    = ∉-++ʳ L (fresh-∉ A)
    x∉L₁  : x ∉ L₁
    x∉L₁  = ∉-++ˡ q₁
    q₂    = ∉-++ʳ L₁ q₁
    x∉Γ   : x ∉ dom Γ
    x∉Γ   = ∉-++ˡ q₂
    q₃    = ∉-++ʳ (dom Γ) q₂
    x∉b°  : x ∉ fv b°
    x∉b°  = ∉-++ˡ q₃
    x∉b′  : x ∉ fv b′
    x∉b′  = ∉-++ʳ (fv b°) q₃

    result : ∃[ u°′ ] (_ ∣ _ ⊢ app (lam _ b°) _ ⟶ᵉ u°′ × R _ (b′ ^ v′) u°′)
    result with simᵉ (F x∉L) (R-open 0 (fvar x) rel″) (G x∉L₁) pv
    ... | W , dW , relW =
      (closeRec 0 x W) ^ v′
      , Me-Bet {u' = closeRec 0 x W} []
               (λ {y} _ → reopenᵉ {u = b°} x y x∉Γ x∉b° (⟶ᵉ-lc (G x∉L₁) dW) dW) e
      , R-open 0 v′ (R-body {b′ = b′} x x∉b′ relW)

simᵉ (Me-Fun L d F) rel lu pv with R-lam0-inv rel
... | inj₁ refl = _ , pushᵉ (Me-Fun L d F) pv , R-refl
... | inj₂ refl = _ , top-stepᵉ pv d , R-top

simᵉ (Me-FOp L d F) rel lu pv with R-lam-inv rel
simᵉ {Γ} {a = a} {r = r} (Me-FOp {s = s₀} {α = α} {t' = t′} {u' = b′} L d F) rel
     (lc-lam L₁ lt G) pv | b° , refl , rel′ = result
  where
    A     = L ++ L₁ ++ dom Γ ++ fv b° ++ fv b′
    x     = fresh A
    x∉L   : x ∉ L
    x∉L   = ∉-++ˡ (fresh-∉ A)
    q₁    = ∉-++ʳ L (fresh-∉ A)
    x∉L₁  : x ∉ L₁
    x∉L₁  = ∉-++ˡ q₁
    q₂    = ∉-++ʳ L₁ q₁
    x∉Γ   : x ∉ dom Γ
    x∉Γ   = ∉-++ˡ q₂
    q₃    = ∉-++ʳ (dom Γ) q₂
    x∉b°  : x ∉ fv b°
    x∉b°  = ∉-++ˡ q₃
    x∉b′  : x ∉ fv b′
    x∉b′  = ∉-++ʳ (fv b°) q₃

    x∉α   : x ∉ fv α
    x∉α h = x∉Γ (prevalid-head-fv pv h)
    x∉stk : x ∉ fvStack (s₀ ++ a ∷ r)
    x∉stk h = x∉Γ (stack-fv (prevalid-pop pv) h)

    result : ∃[ u°′ ] (Γ ∣ (α ∷ s₀ ++ a ∷ r) ⊢ lam _ b° ⟶ᵉ u°′ × R _ (lam t′ b′) u°′)
    result with simᵉ (F x∉L) (R-open 0 (fvar x) rel′) (G x∉L₁) (pv-eqv pv x∉Γ)
    ... | W , dW , relW =
      lam t′ (closeRec 0 x W)
      , Me-FOp {u' = closeRec 0 x W} (dom Γ) d
               (λ {y} y∉ → ⟶ᵉ-rename-head {b = b°} x y x∉Γ y∉ x∉α x∉b° x∉stk
                                          (⟶ᵉ-lc (G x∉L₁) dW) dW)
      , R-lam (R-body {b′ = b′} x x∉b′ relW)
```

## Simulation of `⟶ˢ`

One step for a chain. `Ms-Fun` is the case that cannot be replayed; the longer stack sends the
body to `⊤`, whatever the original step did in it.

```agda
simˢ : ∀ {Γ s a r u u′ u°}
     → Γ ∣ s ⊢ u ⟶ˢ u′
     → R (length s) u u° → LC u°
     → Γ ∣ (s ++ a ∷ r) prevalid
     → ∃[ u°′ ] (Γ ∣ (s ++ a ∷ r) ⊢ u° ⟶ˢ* u°′ × R (length s) u′ u°′)

simˢ (Ms-Pro _ m) rel lu pv with R-fvar-inv rel
... | refl = _ , (Ms-Pro pv m ◅ˢ εˢ pv) , R-refl

simˢ (Ms-Top _) rel lu pv = _ , (Ms-Top pv ◅ˢ εˢ pv) , R-refl

simˢ (Ms-Equ _ e) rel lu pv with simᵉ e rel lu pv
... | w , e° , rel′ = w , (Ms-Equ pv e° ◅ˢ εˢ pv) , rel′

simˢ (Ms-App d) rel lu pv with R-app-inv rel
simˢ (Ms-App d) rel (lc-app lf lv) pv | f° , refl , rel′
  with simˢ d rel′ lf (Pv-Sta pv (prevalid-head-lc (⟶ˢ-prevalid d))
                                 (prevalid-head-fv (⟶ˢ-prevalid d)))
... | f°′ , d° , rel″ = _ , ⟶ˢ*-app d° , R-app rel″

simˢ (Ms-Fun L F) rel lu pv with R-lam-shape 0 rel
... | b° , refl = _ , (top-stepˢ pv ◅ˢ εˢ pv) , R-top

simˢ (Ms-FOp L F) rel lu pv with R-lam-inv rel
simˢ {Γ} {a = a} {r = r} (Ms-FOp {s = s₀} {α = α} {t = t} {u' = b′} L F) rel
     (lc-lam L₁ lt G) pv | b° , refl , rel′ = result
  where
    A     = L ++ L₁ ++ dom Γ ++ fv b° ++ fv b′
    x     = fresh A
    x∉L   : x ∉ L
    x∉L   = ∉-++ˡ (fresh-∉ A)
    q₁    = ∉-++ʳ L (fresh-∉ A)
    x∉L₁  : x ∉ L₁
    x∉L₁  = ∉-++ˡ q₁
    q₂    = ∉-++ʳ L₁ q₁
    x∉Γ   : x ∉ dom Γ
    x∉Γ   = ∉-++ˡ q₂
    q₃    = ∉-++ʳ (dom Γ) q₂
    x∉b°  : x ∉ fv b°
    x∉b°  = ∉-++ˡ q₃
    x∉b′  : x ∉ fv b′
    x∉b′  = ∉-++ʳ (fv b°) q₃

    x∉stk : x ∉ fvStack (s₀ ++ a ∷ r)
    x∉stk h = x∉Γ (stack-fv (prevalid-pop pv) h)

    result : ∃[ u°′ ] (Γ ∣ (α ∷ s₀ ++ a ∷ r) ⊢ lam t b° ⟶ˢ* u°′ × R _ (lam t b′) u°′)
    result with simˢ (F x∉L) (R-open 0 (fvar x) rel′) (G x∉L₁) (pv-eqv pv x∉Γ)
    ... | W , dW , relW =
      lam t (closeRec 0 x W)
      , subst (λ z → Γ ∣ (α ∷ s₀ ++ a ∷ r) ⊢ lam t z ⟶ˢ* lam t (closeRec 0 x W))
              (close-open 0 x b° x∉b°)
              (⟶ˢ*-fop {w = t} x x∉Γ x∉stk (G x∉L₁) dW)
      , R-lam (R-body {b′ = b′} x x∉b′ relW)
```

## The machine relation

A chain on the left of a derivation.

```agda
prepend : ∀ {Γ s u m t} → Γ ∣ s ⊢ u ⟶ˢ* m → Γ ∣ s ⊢ m ≤ t → Γ ∣ s ⊢ u ≤ t
prepend (εˢ _)   D = D
prepend (d ◅ˢ p) D = As-Left-1 d (prepend p D)
```

By induction on the derivation at `s`, for any term related to its left end. The right end stays
an abstraction along `As-Right`, and `λd.⊤` follows it by `top-stepᵉ`. At `As-Refl` the left term
is `λd.c°` for some `c°`, one `top-stepˢ` away from the target.

```agda
belowᵀ : ∀ {Γ s a r u u° d c}
       → Γ ∣ s ⊢ u ≤ lam d c
       → R (length s) u u° → LC u°
       → Γ ∣ (s ++ a ∷ r) prevalid
       → Γ ∣ (s ++ a ∷ r) ⊢ u° ≤ lam d Top

belowᵀ {s = []} (As-Refl _) rel lu pv with R-lam-shape 0 rel
... | c° , refl = As-Left-1 (top-stepˢ pv) (As-Refl pv)
belowᵀ {s = α ∷ s₀} (As-Refl _) rel lu pv with R-lam-shape (length (α ∷ s₀)) rel
... | c° , refl = As-Left-1 (top-stepˢ pv) (As-Refl pv)

belowᵀ (As-Left-1 st D) rel lu pv with simˢ st rel lu pv
... | m° , ch , rel′ = prepend ch (belowᵀ D rel′ (⟶ˢ*-lc lu ch) pv)

belowᵀ (As-Right D (Me-Fun L e F)) rel lu pv =
  As-Right (belowᵀ D rel lu pv) (top-stepᵉ pv e)
belowᵀ (As-Right D (Me-FOp L e F)) rel lu pv =
  As-Right (belowᵀ D rel lu pv) (top-stepᵉ pv e)
```

## The statement

```agda
push-top : ∀ {Γ σ a r g d c}
         → LC g
         → Γ ∣ σ ⊢ g ≤ lam d c
         → Γ ∣ (σ ++ a ∷ r) prevalid
         → Γ ∣ (σ ++ a ∷ r) ⊢ g ≤ lam d Top
push-top lg D pv = belowᵀ D R-refl lg pv

M1 : ∀ {Γ σ a g d c}
   → LC g
   → Γ ∣ σ ⊢ g ≤ lam d c
   → Γ ∣ (σ ++ a ∷ []) prevalid
   → Γ ∣ (σ ++ a ∷ []) ⊢ g ≤ lam d Top
M1 = push-top
```

## What this establishes

- `M1`: (M1) of `MPSS/CONJ8.md` §30, for a locally closed `g`. No hypothesis on `d`, `c` or `a`
  beyond the prevalidity of the longer stack, no well-formedness hypothesis, and no restriction
  on `Γ` or `σ`. `push-top` is the same for any non-empty extension `a ∷ r` of the stack.
- `simᵉ`, `simˢ`: a step at `s` from `u` is matched at `s ++ a ∷ r` from any `u°` with
  `R (length s) u u°` — one `⟶ᵉ` step for a `⟶ᵉ` step, a chain of `⟶ˢ` steps for a `⟶ˢ` step — and
  the results are related again. `R` lets the body of an abstraction be `⊤` where the head path
  has used up the operands of `s`, and nowhere else.
- Local closure of `g` is used where a binder case closes a body at a fresh name and reopens it
  (`⟶ᵉ-rename-head`, `⟶ˢ*-fop`, `reopenᵉ` all ask for it). The machine relation does not supply
  it: `bvar 0 ⟶ˢ ⊤` by `Ms-Top`.
