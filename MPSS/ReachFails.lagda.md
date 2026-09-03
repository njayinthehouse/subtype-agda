# The push obligation cannot be discharged for arbitrary stacks

`MPSS/Push` reduces Conjecture 8's structural content to one obligation, `Reach Γ α w`: the
operand reaches the annotation **at every stack**. This module shows that obligation is **false**
as stated, so it cannot be discharged from `Γ ⊢ α ≤*wf w` alone.

The witness is the one `MPSS/Diff` already uses for `push-is-false`, promoted from a single step
to a whole chain. With `y ≤ Top` in scope, `P = λx≤y.x` and `Q = λx≤y.y`:

- `Γ ⊢ P ≤*wf Q` holds — one `Ms-Fun` step over `Ms-Pro`, both endpoints well-formed;
- at the stack `[Top]`, `P` reaches only `P`, `λx≤y.Top` and `Top`. Never `Q`.

At that stack the parameter is bound `x ≡ Top` rather than `x ≤ y`, so it unfolds to `Top`, and
the chain of `MPSS/Push` degenerates: the operand does not reach the annotation.

**What this leaves standing.** The applied term `P Top` is *not* well-formed: `Wf-App` would
demand `Top ≤*wf y`, and `Top` promotes only to itself. So the refutation does not touch the
obligation restricted to stacks that keep the application well-formed, which is the form
Conjecture 8 actually needs. It does show that well-formedness is **load-bearing** in the
obligation, not a convenience — a stack-polymorphic lemma of the kind `PSS/NarrowPoly` proves
for λ⊲ cannot be had here.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.ReachFails where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Push using (Reach; _∣_⊢_⟶ˢ*_; εˢ; _◅ˢ_)
open import PSS.Syntax using (bvar)
open import PSS.BoundedNarrowing using (open-≡-Top; open-≡-bvar)
```

## The witness

```agda
Γ₀ : Ctx
Γ₀ = (0 , sub , Top) ∷ []

pv₀ : Γ₀ prevalid
pv₀ = Pv-Ctx Pv-Emp (λ ()) lc-Top (λ ())

fv-y : fv (fvar 0) ⊑ dom Γ₀
fv-y (here refl) = here refl

P Q : Tm
P = lam (fvar 0) (bvar 0)
Q = lam (fvar 0) (fvar 0)

pvS : Γ₀ ∣ (Top ∷ []) prevalid
pvS = Pv-Sta (Pv-Nil pv₀) lc-Top (λ ())
```

`P` is a well-subtype of `Q`.

```agda
P-wf : Γ₀ ⊢ P wf
P-wf = Wf-Fun (0 ∷ []) body (Wf-PrS pv₀ (here refl))
  where
    body : ∀ {x} → x ∉ (0 ∷ []) → ((x , sub , fvar 0) ∷ Γ₀) ⊢ (bvar 0 ^ fvar x) wf
    body {x} x∉ = Wf-PrS (Pv-Ctx pv₀ x∉ lc-fvar fv-y) (here refl)

Q-wf : Γ₀ ⊢ Q wf
Q-wf = Wf-Fun (0 ∷ []) body (Wf-PrS pv₀ (here refl))
  where
    body : ∀ {x} → x ∉ (0 ∷ []) → ((x , sub , fvar 0) ∷ Γ₀) ⊢ (fvar 0 ^ fvar x) wf
    body {x} x∉ = Wf-PrS (Pv-Ctx pv₀ x∉ lc-fvar fv-y) (there (here refl))

P⟶Q : Γ₀ ∣ [] ⊢ P ⟶ˢ Q
P⟶Q = Ms-Fun {u' = fvar 0} (0 ∷ []) body
  where
    body : ∀ {x} → x ∉ (0 ∷ [])
         → ((x , sub , fvar 0) ∷ Γ₀) ∣ [] ⊢ (bvar 0 ^ fvar x) ⟶ˢ (fvar 0 ^ fvar x)
    body {x} x∉ = Ms-Pro (Pv-Nil (Pv-Ctx pv₀ x∉ lc-fvar fv-y)) (here refl)

P≤*Q : Γ₀ ⊢ P ≤*wf Q
P≤*Q = Ws-Sub P-wf (Ws-Lf2 P-wf P⟶Q Q-wf (Ws-Rfl pv₀)) Q-wf
```

## What a parameter bound to `Top` can do

Under `x ≡ Top` at the empty stack, the parameter reduces only to itself or to `Top`, by either
relation: `Ms-Pro` is unavailable because the entry is an equivalence one, and the context's only
other entry belongs to `y`.

```agda
Γx : Name → Ctx
Γx x = (x , eqv , Top) ∷ Γ₀

Top-eqv : ∀ {x v} → Γx x ∣ [] ⊢ Top ⟶ᵉ v → v ≡ Top
Top-eqv (Me-Top _) = refl

var-eqv : ∀ {x v} → Γx x ∣ [] ⊢ fvar x ⟶ᵉ v → (v ≡ fvar x) ⊎ (v ≡ Top)
var-eqv (Me-Var _)                     = inj₁ refl
var-eqv (Me-Pro _ (here refl) d)       = inj₂ (Top-eqv d)
var-eqv (Me-Pro _ (there (here ())) _)

var-sub : ∀ {x v} → x ≢ 0 → Γx x ∣ [] ⊢ fvar x ⟶ˢ v → (v ≡ fvar x) ⊎ (v ≡ Top)
var-sub x≢0 (Ms-Pro _ (there (here refl))) = ⊥-elim (x≢0 refl)
var-sub x≢0 (Ms-Top _)                     = inj₂ refl
var-sub x≢0 (Ms-Equ _ e)                   = var-eqv e

Top-sub : ∀ {x v} → Γx x ∣ [] ⊢ Top ⟶ˢ v → v ≡ Top
Top-sub (Ms-Top _)    = refl
Top-sub (Ms-Equ _ e)  = Top-eqv e
```

## Choosing the fresh name

```agda
pick : List Name → Name
pick L = fresh (0 ∷ L)

pick∉ : ∀ L → pick L ∉ L
pick∉ L h = fresh-∉ (0 ∷ L) (there h)

pick≢0 : ∀ L → pick L ≢ 0
pick≢0 L p = fresh-∉ (0 ∷ L) (here p)
```

Classifying a body from its cofinite family. The four combinations of source (`x` or `Top`) and
relation are packaged so the step lemma below needs no `with` on an opened term.

```agda
class-var-sub : ∀ {u′} (L : List Name)
              → (∀ {x} → x ∉ L → Γx x ∣ [] ⊢ (bvar 0 ^ fvar x) ⟶ˢ (u′ ^ fvar x))
              → (u′ ≡ bvar 0) ⊎ (u′ ≡ Top)
class-var-sub {u′} L F = go (var-sub (pick≢0 A) (F (∉-++ˡ (pick∉ A))))
  where
    A = L ++ fv u′
    x∉u′ : pick A ∉ fv u′
    x∉u′ = ∉-++ʳ L (pick∉ A)

    go : ((u′ ^ fvar (pick A)) ≡ fvar (pick A)) ⊎ ((u′ ^ fvar (pick A)) ≡ Top)
       → (u′ ≡ bvar 0) ⊎ (u′ ≡ Top)
    go (inj₁ e) = inj₁ (open-≡-bvar u′ (pick A) x∉u′ e)
    go (inj₂ e) = inj₂ (open-≡-Top u′ (pick A) e)

class-var-eqv : ∀ {u′} (L : List Name)
              → (∀ {x} → x ∉ L → Γx x ∣ [] ⊢ (bvar 0 ^ fvar x) ⟶ᵉ (u′ ^ fvar x))
              → (u′ ≡ bvar 0) ⊎ (u′ ≡ Top)
class-var-eqv {u′} L F = go (var-eqv (F (∉-++ˡ (pick∉ A))))
  where
    A = L ++ fv u′
    x∉u′ : pick A ∉ fv u′
    x∉u′ = ∉-++ʳ L (pick∉ A)

    go : ((u′ ^ fvar (pick A)) ≡ fvar (pick A)) ⊎ ((u′ ^ fvar (pick A)) ≡ Top)
       → (u′ ≡ bvar 0) ⊎ (u′ ≡ Top)
    go (inj₁ e) = inj₁ (open-≡-bvar u′ (pick A) x∉u′ e)
    go (inj₂ e) = inj₂ (open-≡-Top u′ (pick A) e)

class-Top-sub : ∀ {u′} (L : List Name)
              → (∀ {x} → x ∉ L → Γx x ∣ [] ⊢ (Top ^ fvar x) ⟶ˢ (u′ ^ fvar x))
              → u′ ≡ Top
class-Top-sub {u′} L F = open-≡-Top u′ (pick A) (Top-sub (F (∉-++ˡ (pick∉ A))))
  where A = L ++ fv u′

class-Top-eqv : ∀ {u′} (L : List Name)
              → (∀ {x} → x ∉ L → Γx x ∣ [] ⊢ (Top ^ fvar x) ⟶ᵉ (u′ ^ fvar x))
              → u′ ≡ Top
class-Top-eqv {u′} L F = open-≡-Top u′ (pick A) (Top-eqv (F (∉-++ˡ (pick∉ A))))
  where A = L ++ fv u′
```

The annotation cannot move: `y` carries a subtype annotation, so `Me-Pro` cannot fire on it.

```agda
ann-fixed : ∀ {v} → Γ₀ ∣ [] ⊢ fvar 0 ⟶ᵉ v → v ≡ fvar 0
ann-fixed (Me-Var _)              = refl
ann-fixed (Me-Pro _ (here ()) _)
```

## The reachable set

```agda
data RS : Tm → Set where
  r-P   : RS P
  r-PT  : RS (lam (fvar 0) Top)
  r-Top : RS Top

Q∉RS : ¬ (RS Q)
Q∉RS ()

lam-RS : ∀ {u′} → (u′ ≡ bvar 0) ⊎ (u′ ≡ Top) → RS (lam (fvar 0) u′)
lam-RS (inj₁ refl) = r-P
lam-RS (inj₂ refl) = r-PT

step : ∀ {a b} → RS a → Γ₀ ∣ (Top ∷ []) ⊢ a ⟶ˢ b → RS b
step r         (Ms-Top _)                       = r-Top
step r-Top     (Ms-Equ _ (Me-Top _))            = r-Top
step r-P       (Ms-FOp L F)                     = lam-RS (class-var-sub L F)
step r-PT      (Ms-FOp L F)                     = lam-RS (inj₂ (class-Top-sub L F))
step r-P       (Ms-Equ _ (Me-FOp L d F))        =
  subst (λ z → RS (lam z _)) (sym (ann-fixed d)) (lam-RS (class-var-eqv L F))
step r-PT      (Ms-Equ _ (Me-FOp L d F))        =
  subst (λ z → RS (lam z _)) (sym (ann-fixed d)) (lam-RS (inj₂ (class-Top-eqv L F)))

chain : ∀ {a b} → RS a → Γ₀ ∣ (Top ∷ []) ⊢ a ⟶ˢ* b → RS b
chain r (εˢ _)    = r
chain r (d ◅ˢ c)  = chain (step r d) c
```

## The refutation

```agda
reach-fails : ¬ (Reach Γ₀ P Q)
reach-fails R = Q∉RS (chain r-P (R pvS))

Reach-from-≤*wf : Set
Reach-from-≤*wf = ∀ {Γ α w} → Γ ⊢ α ≤*wf w → Reach Γ α w

reach-from-≤*wf-false : ¬ Reach-from-≤*wf
reach-from-≤*wf-false f = reach-fails (f P≤*Q)
```

## What this establishes

**The obligation of `MPSS/Push` is false for arbitrary stacks**, so the closing sentence of that
module — that the residual is "from `Γ ⊢ α ≤*wf w` derive `Reach Γ α w`" — names a statement that
is refutable, not merely open. `P ≤*wf Q` holds while `P` cannot reach `Q` at the stack `[Top]`.

The obligation must therefore be restricted to stacks under which the application stays
well-formed, and this witness respects that restriction: `P Top` is not well-formed, because
`Wf-App` demands `Top ≤*wf y` and `Top` promotes only to itself.

So Conjecture 8, if it holds, holds **because of well-formedness of the operands**, not by any
stack-polymorphic property of promotion. That is the sharpest statement of what the conjecture
needs, and it is why well-formedness is load-bearing rather than decorative here.
