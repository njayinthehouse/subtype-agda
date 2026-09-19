# MPSS: a well-formedness checker (the functions)

The goal-directed checker of `conj8-hurkens-probe.py`, as Agda functions. Every function has fuel
and returns a Boolean or a `Maybe`; nothing here is a proof. Soundness is `MPSS/CheckerSound`.

    hred t          one head step: β at the head of the spine, or ⊤ u ⟶ ⊤
    whnf m t        at most m head steps
    nf m N t        β-normal form with fuel m, binders opened with names away from N
    conv m N a b    equality of normal forms
    phead Γ t       promote the variable at the head of t to its ≤-bound
    wf? n m Γ t     Wf-PrS/Wf-PrE, Wf-Top, Wf-Fun at one fresh name, Wf-App by dom? and sub?
    dom? n m Γ k w  d with w ≤wf λx≤d.⊤ : head steps and head promotions to an abstraction
    sub? n m Γ k v t   v ≤*wf t : ⊤, syntactic equality, conversion, the abstraction rule under one
                    fresh name, a head promotion, or a head step

`k` says that the subject is already known to be well-formed, so that the two ends of a
promotion (`Ws-Lf2` asks for both) are not checked twice.

```agda
{-# OPTIONS --safe #-}

module MPSS.CheckerFns where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import MPSS.Context
open import MPSS.CoPair using (_≟Tm_)
open import PSS.Syntax
```

## Reduction

```agda
hred : Tm → Maybe Tm
hred (app (lam a b) v)  = just (b ^ v)
hred (app Top v)        = just Top
hred (app (app f u) v) with hred (app f u)
... | just r  = just (app r v)
... | nothing = nothing
hred _                  = nothing

whnf : ℕ → Tm → Tm
whnf zero    t = t
whnf (suc m) t with hred t
... | just t′ = whnf m t′
... | nothing = t

nf  : ℕ → List Name → Tm → Tm
nfw : ℕ → List Name → Tm → Tm
nfs : ℕ → List Name → Tm → Tm

nf zero    N t = t
nf (suc m) N t = nfw m N (whnf m t)

nfw m N (lam a b) = lam (nf m N a) (closeRec 0 x (nf m (x ∷ N) (b ^ fvar x)))
  where x = fresh (N ++ fv b)
nfw m N (app f v) = app (nfs m N f) (nf m N v)
nfw m N t         = t

nfs m N (app f v) = app (nfs m N f) (nf m N v)
nfs m N t         = t

conv : ℕ → List Name → Tm → Tm → Bool
conv m N a b = ⌊ nf m N a ≟Tm nf m N b ⌋
```

## Contexts and heads

```agda
lookupˢ : Ctx → Name → Maybe Tm
lookupˢ []                  x = nothing
lookupˢ ((y , sub , t) ∷ Γ) x with x ≟ y
... | yes _ = just t
... | no  _ = lookupˢ Γ x
lookupˢ ((y , eqv , t) ∷ Γ) x with x ≟ y
... | yes _ = nothing
... | no  _ = lookupˢ Γ x

bound? : Ctx → Name → Bool
bound? []              x = false
bound? ((y , _ , _) ∷ Γ) x with x ≟ y
... | yes _ = true
... | no  _ = bound? Γ x

phead : Ctx → Tm → Maybe Tm
phead Γ (fvar x)  = lookupˢ Γ x
phead Γ (app f v) with phead Γ f
... | just r  = just (app r v)
... | nothing = nothing
phead Γ _         = nothing

isTop : Tm → Bool
isTop Top = true
isTop _   = false

-- the variable at the head of a spine
headVar : Tm → Maybe Name
headVar (fvar x)  = just x
headVar (app f _) = headVar f
headVar _         = nothing

sameHead : Tm → Tm → Bool
sameHead v t with headVar v | headVar t
... | just x | just y = ⌊ x ≟ y ⌋
... | _      | _      = false
```

## The checker

```agda
lamView : Tm → Maybe (Tm × Tm)
lamView (lam a b) = just (a , b)
lamView _         = nothing

isLam : Tm → Bool
isLam (lam _ _) = true
isLam _         = false

-- when conversion is worth trying: an abstraction or ⊤ (nothing else can be done with them),
-- or two spines with the same variable at the head
guard : Tm → Tm → Bool
guard v tw = isLam v ∨ isTop v ∨ sameHead v tw

wf?  : ℕ → ℕ → Ctx → Tm → Bool
dom? : ℕ → ℕ → Ctx → Bool → Tm → Maybe Tm
sub? : ℕ → ℕ → Ctx → Bool → Tm → Tm → Bool

domV    : ℕ → ℕ → Ctx → Bool → Tm → Maybe (Tm × Tm) → Maybe Tm
domStep : ℕ → ℕ → Ctx → Bool → Tm → Maybe Tm → Maybe Tm → Maybe Tm
subV    : ℕ → ℕ → Ctx → Bool → Tm → Tm → Tm → Maybe (Tm × Tm) → Maybe (Tm × Tm) → Bool
subGen  : ℕ → ℕ → Ctx → Bool → Tm → Tm → Tm → Bool
subStep : ℕ → ℕ → Ctx → Bool → Tm → Tm → Maybe Tm → Maybe Tm → Bool
subLam  : ℕ → ℕ → Ctx → Bool → Tm → Tm → Tm → Tm → Bool
arg?    : ℕ → ℕ → Ctx → Tm → Maybe Tm → Bool

wf? zero    m Γ t         = false
wf? (suc n) m Γ (bvar i)  = false
wf? (suc n) m Γ (fvar x)  = bound? Γ x
wf? (suc n) m Γ Top       = true
wf? (suc n) m Γ (lam a b) =
  wf? n m Γ a ∧ wf? n m ((fresh (dom Γ ++ fv b) , sub , a) ∷ Γ) (b ^ fvar (fresh (dom Γ ++ fv b)))
wf? (suc n) m Γ (app f v) = wf? n m Γ f ∧ wf? n m Γ v ∧ arg? n m Γ v (dom? n m Γ true f)

arg? n m Γ v (just d) = sub? n m Γ true v d
arg? n m Γ v nothing  = false

dom? zero    m Γ k w = nothing
dom? (suc n) m Γ k w = domV n m Γ k w (lamView w)

domV n m Γ k w (just (d , b)) =
  if (k ∨ wf? n m Γ w) ∧ wf? n m Γ (lam d Top) then just d else nothing
domV n m Γ k w nothing        = domStep n m Γ k w (phead Γ w) (hred w)

domStep n m Γ k w (just p) _        =
  if (k ∨ wf? n m Γ w) ∧ wf? n m Γ p then dom? n m Γ true p else nothing
domStep n m Γ k w nothing (just w′) = dom? n m Γ false w′
domStep n m Γ k w nothing nothing   = nothing

sub? zero    m Γ k v t = false
sub? (suc n) m Γ k v t =
  if isTop (whnf m t) then k ∨ wf? n m Γ v
  else if ⌊ v ≟Tm t ⌋ then true
  else subV n m Γ k v t (whnf m t) (lamView v) (lamView (whnf m t))

subV n m Γ k v t tw (just (a , b)) (just (a′ , b′)) = subLam n m Γ k a b a′ b′
subV n m Γ k v t tw _              _                = subGen n m Γ k v t tw

subGen n m Γ k v t tw =
  if guard v tw ∧ conv m (dom Γ) v t then true
  else subStep n m Γ k v t (phead Γ v) (hred v)

subLam n m Γ k a b a′ b′ =
  (k ∨ wf? n m Γ (lam a b)) ∧ conv m (dom Γ) a a′
  ∧ wf? n m ((fresh (dom Γ ++ fv b ++ fv b′) , sub , a) ∷ Γ) (b′ ^ fvar (fresh (dom Γ ++ fv b ++ fv b′)))
  ∧ sub? n m ((fresh (dom Γ ++ fv b ++ fv b′) , sub , a) ∷ Γ) true
           (b ^ fvar (fresh (dom Γ ++ fv b ++ fv b′))) (b′ ^ fvar (fresh (dom Γ ++ fv b ++ fv b′)))

subStep n m Γ k v t (just p) _        =
  (k ∨ wf? n m Γ v) ∧ wf? n m Γ p ∧ sub? n m Γ true p t
subStep n m Γ k v t nothing (just v′) = sub? n m Γ false v′ t
subStep n m Γ k v t nothing nothing   = false
```
