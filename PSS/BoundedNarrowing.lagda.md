# Bounded narrowing fails in λ⊲

`Embed/TypePreserving` leaves one module parameter — `t-ƛ` at a non-empty stack — and the lemma
that would discharge it is **bounded narrowing**, the standard hard lemma of F<:-style systems:

> from a derivation under `x ≤ Q` to one under `x ≤ P`, given `P ≤ Q`

This module **refutes it** for λ⊲. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module PSS.BoundedNarrowing where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.Narrowing using (_∣_⊢_⟶≤*_; εₚ; _◅ₚ_; _⟶≡*_; εₑ; _◅ₑ_; ⊲⇒diag)
open import PSS.Minimal using (Top-only)
```

## The statement

```agda
BoundedNarrowing : Set
BoundedNarrowing = ∀ {Γ x P Q s p q}
                 → Γ ∣ [] ⊢ P ≤ Q
                 → ((x , Q) ∷ Γ) ∣ s ⊢ p ≤ q
                 → ((x , P) ∷ Γ) ∣ s ⊢ p ≤ q
```

## Two inversions for opened bodies

```agda
open-≡-Top : ∀ b x → (b ^ fvar x) ≡ Top → b ≡ Top
open-≡-Top (bvar i) x e with 0 ≟ i | e
... | yes _ | ()
... | no  _ | ()
open-≡-Top (fvar y)  x ()
open-≡-Top Top       x e = refl
open-≡-Top (lam _ _) x ()
open-≡-Top (app _ _) x ()

open-≡-bvar : ∀ b x → x ∉ fv b → (b ^ fvar x) ≡ fvar x → b ≡ bvar 0
open-≡-bvar (bvar i) x x∉ e with 0 ≟ i | e
... | yes refl | _  = refl
... | no  _    | ()
open-≡-bvar (fvar y)  x x∉ refl = ⊥-elim (x∉ (here refl))
open-≡-bvar Top       x x∉ ()
open-≡-bvar (lam _ _) x x∉ ()
open-≡-bvar (app _ _) x x∉ ()
```

```agda
snd-eq : ∀ {A B : Set} {a : A} {b c : B} → (a , b) ≡ (a , c) → b ≡ c
snd-eq refl = refl

open-≡-fvar0 : ∀ b x → x ≢ 0 → (b ^ fvar x) ≡ fvar 0 → b ≡ fvar 0
open-≡-fvar0 (bvar i) x x≢0 e with 0 ≟ i | e
... | yes _ | refl = ⊥-elim (x≢0 refl)
... | no  _ | ()
open-≡-fvar0 (fvar y)  x x≢0 refl = refl
open-≡-fvar0 Top       x x≢0 ()
open-≡-fvar0 (lam _ _) x x≢0 ()
open-≡-fvar0 (app _ _) x x≢0 ()
```

## The witness

`y ≤ Top`, and the two abstractions from `push-is-false`. `P = λx≤y. x` promotes to `Q = λx≤y. y`
**at the empty stack only**, so narrowing a variable's bound from `Q` to `P` loses the fact.

```agda
Γ₀ : Ctx
Γ₀ = (0 , Top) ∷ []

P Q : Tm
P = lam (fvar 0) (bvar 0)
Q = lam (fvar 0) (fvar 0)

pv₀ : Γ₀ ∣ [] prevalid
pv₀ = P-Ctx2 P-Ctx1 (λ ()) lc-Top (λ ())

fv-y : fv (fvar 0) ⊑ dom Γ₀
fv-y (here refl) = here refl

ΓQ ΓP : Ctx
ΓQ = (1 , Q) ∷ Γ₀
ΓP = (1 , P) ∷ Γ₀

lcP : LC P
lcP = lc-lam [] lc-fvar (λ _ → lc-fvar)

lcQ : LC Q
lcQ = lc-lam [] lc-fvar (λ _ → lc-fvar)

fvP : fv P ⊑ dom Γ₀
fvP (here refl) = here refl

fvQ : fv Q ⊑ dom Γ₀
fvQ (here refl)         = here refl
fvQ (there (here refl)) = here refl

1∉ : ∀ {A : Set} → (1 ∈ dom Γ₀) → A
1∉ (here ())

pvQ : ΓQ ∣ (Top ∷ []) prevalid
pvQ = P-Ctx3 (P-Ctx2 pv₀ 1∉ lcQ fvQ) lc-Top (λ ())

pvP : ΓP ∣ (Top ∷ []) prevalid
pvP = P-Ctx3 (P-Ctx2 pv₀ 1∉ lcP fvP) lc-Top (λ ())

pvP-nil : ΓP ∣ [] prevalid
pvP-nil = P-Ctx2 pv₀ 1∉ lcP fvP
```

**The hypothesis holds.** `Srs-Fun` binds the parameter to the annotation `y`, and `Srs-Prom`
promotes it there.

```agda
hyp : Γ₀ ∣ [] ⊢ P ≤ Q
hyp = As-Left-1 step (As-Refl pv₀)
  where
    body : ∀ {x} → x ∉ (0 ∷ [])
         → ((x , fvar 0) ∷ Γ₀) ∣ [] ⊢ (bvar 0 ^ fvar x) ⟶≤ (fvar 0 ^ fvar x)
    body {x} x∉ = Srs-Prom (P-Ctx2 pv₀ x∉ lc-fvar fv-y) (here refl)

    step : Γ₀ ∣ [] ⊢ P ⟶≤ Q
    step = Srs-Fun (0 ∷ []) body
```

**The premise holds.** Under `z ≤ Q`, the variable reaches `Q` in one step, at any stack.

```agda
premise : ΓQ ∣ (Top ∷ []) ⊢ fvar 1 ≤ Q
premise = As-Left-1 (Srs-Prom pvQ (here refl)) (As-Refl pvQ)
```

## The conclusion fails

Under `z ≤ P` the variable reaches `P`, and at a non-empty stack `P` cannot reach `Q`: `Srs-Fun`
no longer applies, and `Srs-FunOp` binds the parameter to the stacked operand `Top`, from which
the body only reaches `Top`. Everything reachable therefore has body `bvar 0` or `Top` — never
`fvar 0`.

```agda
data Reach : Tm → Set where
  r-P   : Reach P
  r-Top : Reach (lam (fvar 0) Top)
  r-⊤   : Reach Top

Q∉Reach : ¬ (Reach Q)
Q∉Reach ()
```

The body of an abstraction reachable from `P` can only be `bvar 0` or `Top`; this is where the
stacked operand `Top` does its work.

```agda
body-step : ∀ {b' x v}
          → x ∉ fv b' → x ∉ dom ΓP → v ≡ (b' ^ fvar x)
          → ((x , Top) ∷ ΓP) ∣ [] ⊢ fvar x ⟶≤ v
          → (b' ≡ bvar 0) ⊎ (b' ≡ Top)
body-step {b'} {x} x∉ xd eq (Srs-Prom _ (here e)) =
  inj₂ (open-≡-Top b' x (trans (sym eq) (snd-eq e)))
body-step x∉ xd eq (Srs-Prom _ (there (here refl)))          = ⊥-elim (xd (here refl))
body-step x∉ xd eq (Srs-Prom _ (there (there (here refl))))  = ⊥-elim (xd (there (here refl)))
body-step {b'} {x} x∉ xd eq (Srs-Top _)        = inj₂ (open-≡-Top b' x (sym eq))
body-step {b'} {x} x∉ xd eq (Srs-Eq _ Cr-Var)  = inj₁ (open-≡-bvar b' x x∉ (sym eq))

body-step-Top : ∀ {b' x v}
              → v ≡ (b' ^ fvar x)
              → ((x , Top) ∷ ΓP) ∣ [] ⊢ Top ⟶≤ v
              → b' ≡ Top
body-step-Top {b'} {x} eq (Srs-Top _)       = open-≡-Top b' x (sym eq)
body-step-Top {b'} {x} eq (Srs-Eq _ Cr-Top) = open-≡-Top b' x (sym eq)
```

```agda
Reach-step : ∀ {t u} → Reach t → ΓP ∣ (Top ∷ []) ⊢ t ⟶≤ u → Reach u
Reach-step r         (Srs-Top _)          = r-⊤
Reach-step r-⊤       (Srs-Eq _ Cr-Top)    = r-⊤

Reach-step r-P   (Srs-Eq _ (Cr-Fun {t' = a'} {u' = b'} L e F)) = go (annot e) (bodyE L F)
  where
    annot : fvar 0 ⟶≡ a' → a' ≡ fvar 0
    annot Cr-Var = refl

    bodyE : ∀ L → (∀ {x} → x ∉ L → (bvar 0 ^ fvar x) ⟶≡ (b' ^ fvar x)) → b' ≡ bvar 0
    bodyE L F = inv refl (F x∉L)
      where
        A   = L ++ fv b'
        x   = fresh A
        x∉L = ∉-++ˡ (fresh-∉ A)
        x∉b : x ∉ fv b'
        x∉b = ∉-++ʳ L (fresh-∉ A)

        inv : ∀ {v} → v ≡ (b' ^ fvar x) → (fvar x) ⟶≡ v → b' ≡ bvar 0
        inv eq Cr-Var = open-≡-bvar b' x x∉b (sym eq)

    go : a' ≡ fvar 0 → b' ≡ bvar 0 → Reach (lam a' b')
    go refl refl = r-P

Reach-step r-Top (Srs-Eq _ (Cr-Fun {t' = a'} {u' = b'} L e F)) = go (annot e) (bodyE L F)
  where
    annot : fvar 0 ⟶≡ a' → a' ≡ fvar 0
    annot Cr-Var = refl

    bodyE : ∀ L → (∀ {x} → x ∉ L → (Top ^ fvar x) ⟶≡ (b' ^ fvar x)) → b' ≡ Top
    bodyE L F = inv refl (F (fresh-∉ L))
      where
        inv : ∀ {v} → v ≡ (b' ^ fvar (fresh L)) → Top ⟶≡ v → b' ≡ Top
        inv eq Cr-Top = open-≡-Top b' (fresh L) (sym eq)

    go : a' ≡ fvar 0 → b' ≡ Top → Reach (lam a' b')
    go refl refl = r-Top

Reach-step r-P   (Srs-FunOp {u' = b'} L F) = go (bodyS L F)
  where
    bodyS : ∀ L → (∀ {x} → x ∉ L → ((x , Top) ∷ ΓP) ∣ [] ⊢ (bvar 0 ^ fvar x) ⟶≤ (b' ^ fvar x))
          → (b' ≡ bvar 0) ⊎ (b' ≡ Top)
    bodyS L F = body-step x∉b x∉d refl (F x∉L)
      where
        A   = L ++ fv b' ++ dom ΓP
        a∉  = fresh-∉ A
        x   = fresh A
        x∉L = ∉-++ˡ a∉
        x∉b : x ∉ fv b'
        x∉b = ∉-++ˡ (∉-++ʳ L a∉)
        x∉d : x ∉ dom ΓP
        x∉d = ∉-++ʳ (fv b') (∉-++ʳ L a∉)

    go : (b' ≡ bvar 0) ⊎ (b' ≡ Top) → Reach (lam (fvar 0) b')
    go (inj₁ refl) = r-P
    go (inj₂ refl) = r-Top

Reach-step r-Top (Srs-FunOp {u' = b'} L F) = go (bodyS L F)
  where
    bodyS : ∀ L → (∀ {x} → x ∉ L → ((x , Top) ∷ ΓP) ∣ [] ⊢ (Top ^ fvar x) ⟶≤ (b' ^ fvar x))
          → b' ≡ Top
    bodyS L F = body-step-Top refl (F (fresh-∉ L))

    go : b' ≡ Top → Reach (lam (fvar 0) b')
    go refl = r-Top
```

```agda
Reach-chain : ∀ {t u} → Reach t → ΓP ∣ (Top ∷ []) ⊢ t ⟶≤* u → Reach u
Reach-chain r εₚ        = r
Reach-chain r (st ◅ₚ c) = Reach-chain (Reach-step r st) c
```

The chain out of the *variable* adds only the promotion to `P` itself, and stuttering.

```agda
no-chain : ∀ {w} → ΓP ∣ (Top ∷ []) ⊢ fvar 1 ⟶≤* w → Reach w ⊎ (w ≡ fvar 1)
no-chain εₚ                                = inj₂ refl
no-chain (Srs-Prom _ (here refl) ◅ₚ c)     = inj₁ (Reach-chain r-P c)
no-chain (Srs-Prom _ (there (here ())) ◅ₚ c)
no-chain (Srs-Top _ ◅ₚ c)                  = inj₁ (Reach-chain r-⊤ c)
no-chain (Srs-Eq _ Cr-Var ◅ₚ c)            = no-chain c
```

`Q` reduces only to itself under `⟶≡`.

```agda
Q-fixed′ : ∀ {t v} → t ≡ Q → t ⟶≡* v → v ≡ Q
Q-fixed′ eq εₑ = eq
Q-fixed′ refl (Cr-Fun {t' = a'} {u' = b'} L e F ◅ₑ c) =
  Q-fixed′ (shape (ann e) (bod L F)) c
  where
    ann : fvar 0 ⟶≡ a' → a' ≡ fvar 0
    ann Cr-Var = refl

    bod : ∀ L → (∀ {x} → x ∉ L → (fvar 0 ^ fvar x) ⟶≡ (b' ^ fvar x)) → b' ≡ fvar 0
    bod L F = inv refl (F x∉L)
      where
        A   = 0 ∷ (L ++ fv b')
        x   = fresh A
        a∉  = fresh-∉ A
        x≢0 : x ≢ 0
        x≢0 q = a∉ (here q)
        x∉L : x ∉ L
        x∉L = ∉-++ˡ (∉-tail a∉)

        inv : ∀ {v} → v ≡ (b' ^ fvar x) → fvar 0 ⟶≡ v → b' ≡ fvar 0
        inv eq Cr-Var = open-≡-fvar0 b' x x≢0 (sym eq)

    shape : a' ≡ fvar 0 → b' ≡ fvar 0 → lam a' b' ≡ Q
    shape refl refl = refl

Q-fixed : ∀ {v} → Q ⟶≡* v → v ≡ Q
Q-fixed = Q-fixed′ refl

finish : ∀ {w} → Q ⟶≡* w → (Reach w ⊎ (w ≡ fvar 1)) → ⊥
finish e (inj₁ rw)   = Q∉Reach (subst Reach (Q-fixed e) rw)
finish e (inj₂ refl) with Q-fixed e
... | ()

conclusion-fails : ¬ (ΓP ∣ (Top ∷ []) ⊢ fvar 1 ≤ Q)
conclusion-fails d with ⊲⇒diag d
... | w , chain , ce = finish ce (no-chain chain)
```

## The refutation

```agda
bounded-narrowing-false : ¬ BoundedNarrowing
bounded-narrowing-false narrow = conclusion-fails (narrow hyp premise)
```

## What this establishes

**Bounded narrowing is false for λ⊲.** With `y ≤ Top` in scope, `P = λx≤y. x` is below
`Q = λx≤y. y` at the empty stack, and a variable `z ≤ Q` reaches `Q` at any stack. Narrow `z`'s
bound from `Q` to `P` and the fact is lost: at stack `[Top]`, `z` reaches `P`, and `P` cannot
reach `Q` there — `Srs-Fun` needs an empty stack, and `Srs-FunOp` binds the parameter to the
stacked operand `Top`, from which the body only reaches `Top`.

The `Reach` predicate makes that precise: everything reachable from `P` at stack `[Top]` has body
`bvar 0` or `Top`, never `fvar 0`.

**Consequence for `Embed/TypePreserving`.** Its `t-ƛ` parameter cannot be discharged by bounded
narrowing, because λ⊲ does not have it. The obstruction is not a missing lemma but the design:
promotion is not stack-monotone, and narrowing a bound is exactly the operation that needs it to
be.

**What would still suffice.** The refutation turns on a *single* step: under `x ≤ Q` the variable
reaches `Q` in one `Srs-Prom`, and under `x ≤ P` it needs `P ⟶≤* Q`, which is available only at
the empty stack. A narrowing lemma stated over `⟶≤*` chains **at a fixed stack** is not refuted by
this witness, and the `MPSS/StackObligation` experiment points the same way: the information
survives, it just costs extra steps that the single-step rules cannot absorb.

So the honest status is: bounded narrowing in the F<:-shaped form is refuted; a multi-step form
at a fixed stack remains open, and is the version worth attempting next.
