# MPSS: the diamond's induction cannot be on derivation size

The first thing to try for Lemma 2 is the first thing `AUDIT.md` rules out: induct on the size of
the two derivations — their sum, their multiset, or one lexicographic order or the other. The audit
gives the reason in a sentence each. This module gives the counterexample, once, and refutes all
four from it.

The case is `Me-Var` against `Me-Pro`. The paper's own text says what the induction hypothesis is
applied to there:

> By multiple use of the rule `Ct-Ann`, we have `Γ₀′;nil ⊢ α₀ ⟶≡ α₂`. […] By induction hypothesis
> on `Γ₀;s₀ ⊢ α₀ ⟶≡ α₁` […]

So the recursive call is on the pair `(α₀ ⟶≡ α₁, α₀ ⟶≡ α₂)`, where the first is the `Me-Pro`
premise and the second is read off the context reduction — by `↣-eqv` in this development. The
inputs were `Me-Var`, of size one, and `Me-Pro` on that premise, of size one more than it. Nothing
in either input bounds the derivation the context reduction supplies.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.DerivationSize where

open import Data.Nat.Base using (ℕ; suc; _+_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-eqv)
open import PSS.Syntax using (fresh-∉)
```

## The size of a derivation

Cofinitely quantified premises are measured at one fresh name. Any choice gives a size; the
counterexample below uses no binder, so the choice does not matter to it.

```agda
size : ∀ {Γ s t u} → Γ ∣ s ⊢ t ⟶ᵉ u → ℕ
size (Me-Var _)       = 1
size (Me-Top _)       = 1
size (Me-TAp _)       = 1
size (Me-Pro _ _ d)   = suc (size d)
size (Me-App d e)     = suc (size d + size e)
size (Me-Bet L F e)   = suc (size (F (fresh-∉ L)) + size e)
size (Me-Fun L d F)   = suc (size d + size (F (fresh-∉ L)))
size (Me-FOp L d F)   = suc (size d + size (F (fresh-∉ L)))
```

## What the recursive call is measured against

Fix the shape of the case: a variable `x ≐ α ∈ Γ₀`, the `Me-Pro` premise `e : α ⟶≡ α₁`, and a
context reduction `c`. The two inputs are `Me-Var pv` and `Me-Pro pv m e`; the recursive call is on
`e` and on the derivation `↣-eqv` extracts from `c`.

```agda
extracted : ∀ {Γ₀ s₀ Γ₂ s₂ x α} → Γ₀ prevalid → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂ → x ≐ α ∈ Γ₀ → ℕ
extracted pvc c m = size (proj₂ (proj₂ (↣-eqv pvc c m)))
```

Four candidate orders, each stated as "the recursive call is smaller than the inputs".

```agda
-- the sum of the two sizes
SumDecreases : Set
SumDecreases = ∀ {Γ₀ s₀ Γ₂ s₂ x α α₁}
  (pvc : Γ₀ prevalid) (pv : Γ₀ ∣ s₀ prevalid) (m : x ≐ α ∈ Γ₀)
  (e : Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₁) (c : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
  → size e + extracted pvc c m < size (Me-Pro pv m e) + size (Me-Var {x = x} pv)

-- the multiset of the two sizes: a necessary condition for a multiset decrease is that the
-- maximum does not go up
MaxNonIncreasing : Set
MaxNonIncreasing = ∀ {Γ₀ s₀ Γ₂ s₂ x α α₁}
  (pvc : Γ₀ prevalid) (pv : Γ₀ ∣ s₀ prevalid) (m : x ≐ α ∈ Γ₀)
  (e : Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₁) (c : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
  → size e ⊔ extracted pvc c m ≤ size (Me-Pro pv m e) ⊔ size (Me-Var {x = x} pv)

Lex : ℕ × ℕ → ℕ × ℕ → Set
Lex (a , b) (c , d) = a < c ⊎ (a ≡ c × b < d)

-- lexicographic on (|d₂| , |d₁|), in the orientation where d₁ is the `Me-Var` edge:
-- the recursive call has d₁′ = extracted, d₂′ = e
LexVarPro : Set
LexVarPro = ∀ {Γ₀ s₀ Γ₂ s₂ x α α₁}
  (pvc : Γ₀ prevalid) (pv : Γ₀ ∣ s₀ prevalid) (m : x ≐ α ∈ Γ₀)
  (e : Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₁) (c : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
  → Lex (size e , extracted pvc c m) (size (Me-Pro pv m e) , size (Me-Var {x = x} pv))

-- the same order in the mirror orientation, where d₁ is the `Me-Pro` edge:
-- the recursive call has d₁′ = e, d₂′ = extracted
LexProVar : Set
LexProVar = ∀ {Γ₀ s₀ Γ₂ s₂ x α α₁}
  (pvc : Γ₀ prevalid) (pv : Γ₀ ∣ s₀ prevalid) (m : x ≐ α ∈ Γ₀)
  (e : Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₁) (c : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
  → Lex (extracted pvc c m , size e) (size (Me-Var {x = x} pv) , size (Me-Pro pv m e))
```

## The counterexample

The smallest annotation with two reducts of different sizes: `⊤ ⊤`, which `Me-TAp` sends to `⊤` in
one node and `Me-App` sends to itself in three. Bind `x ≡ ⊤ ⊤`, take the `Me-Pro` premise to be the
one-node reduction, and let the context reduction rewrite the annotation by the three-node one.

```agda
pv₀ : [] ∣ [] prevalid
pv₀ = Pv-Nil Pv-Emp

Γ₁ : Ctx
Γ₁ = (0 , eqv , app Top Top) ∷ []

pvc₁ : Γ₁ prevalid
pvc₁ = Pv-EqA Pv-Emp (λ ()) (lc-app lc-Top lc-Top) (λ ())

pv₁ : Γ₁ ∣ [] prevalid
pv₁ = Pv-Nil pvc₁

m₁ : 0 ≐ app Top Top ∈ Γ₁
m₁ = here refl

e₁ : Γ₁ ∣ [] ⊢ app Top Top ⟶ᵉ Top
e₁ = Me-TAp pv₁

big : [] ∣ [] ⊢ app Top Top ⟶ᵉ app Top Top
big = Me-App (Me-Top (Pv-Sta pv₀ lc-Top (λ ()))) (Me-Top pv₀)

c₁ : Γ₁ ∣ [] ↣ Γ₁ ∣ []
c₁ = Ct-Ann Ct-Refl big
```

The extracted derivation is `big` weakened into `Γ₁`, and weakening does not change the size.

```agda
extracted₁ : extracted pvc₁ c₁ m₁ ≡ 3
extracted₁ = refl
```

So the inputs measure `2` and `1`, and the recursive call measures `1` and `3`.

```agda
sum-false : ¬ SumDecreases
sum-false h with h pvc₁ pv₁ m₁ e₁ c₁
... | s≤s (s≤s (s≤s ()))

max-false : ¬ MaxNonIncreasing
max-false h with h pvc₁ pv₁ m₁ e₁ c₁
... | s≤s (s≤s ())

lex-pro-var-false : ¬ LexProVar
lex-pro-var-false h with h pvc₁ pv₁ m₁ e₁ c₁
... | inj₁ (s≤s ())
... | inj₂ (() , _)
```

The one order that survives this case is `LexVarPro`: with `d₁` the `Me-Var` edge, the first
component drops from `size (Me-Pro pv m e)` to `size e`, and the extracted derivation lands in the
second component where it is not compared. That is what the audit means by "works in this
orientation". It is no use, because the diamond is symmetric in its two edges and the mirror case
`Me-Pro` against `Me-Var` needs the mirror order, which is `LexProVar` — refuted above by the same
instance. An induction has to fix one order for both cases.

## What this establishes

One instance — `x ≡ ⊤ ⊤`, the premise `⊤ ⊤ ⟶≡ ⊤`, the context reduction rewriting the annotation
by `⊤ ⊤ ⟶≡ ⊤ ⊤` — on which the recursive call of the `Me-Var`/`Me-Pro` case is larger than its
inputs in the sum, larger in the maximum (so not smaller in the multiset order), and larger in the
lexicographic order oriented for the mirror case. The derivation the context reduction supplies is
of size `3` here and can be made any size; the inputs are of sizes `2` and `1` regardless.

This is the audit's first bullet under "why the obvious repairs do not work", as code. It rules out
every measure built from derivation sizes alone. It says nothing about measures on the subject term
or the configuration — those are `MPSS/Height`, `MPSS/Multiplier`, `MPSS/LexDepth` and
`MPSS/Unroll`.
