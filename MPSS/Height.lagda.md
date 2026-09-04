# MPSS: unfolding height

A candidate measure for the diamond. `Me-Pro` replaces a variable by its equivalence annotation,
and prevalidity scopes that annotation strictly earlier in the context — so unfolding descends a
finite chain, and the depth of that chain is a number the rule strictly decreases.

Two choices in the definition carry the weight.

A **subtype** annotation counts zero. `Me-Pro` reads equivalence annotations only, so a variable
bound by `Me-Fun` can never be unfolded and going under that binder costs nothing.

A **stack entry** is charged one more than its own height, because `Me-FOp` will bind it to a
variable worth exactly that. The operand of an application is *not* charged that way, and the
tension between those two facts is what this module ends up pinning down — see the last section.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Height where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; ⊔-mono-≤; m≤m⊔n; m≤n⊔m; ≤-refl; ≤-trans; ≤-reflexive; ⊔-lub; ⊔-identityʳ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import MPSS.WellFormed
```

## The height

```agda
mutual
  hvar : Ctx → Name → ℕ
  hvar []                   x = 0
  hvar ((y , sub , w) ∷ Γ) x = hvar Γ x
  hvar ((y , eqv , α) ∷ Γ) x with x ≟ y
  ... | yes _ = suc (htm Γ α)
  ... | no  _ = hvar Γ x

  htm : Ctx → Tm → ℕ
  htm Γ (bvar _)  = 0
  htm Γ (fvar x)  = hvar Γ x
  htm Γ Top       = 0
  htm Γ (lam w b) = htm Γ w ⊔ htm Γ b
  htm Γ (app a b) = htm Γ a ⊔ htm Γ b
```

## Adding a binding a term does not mention leaves its height alone

```agda
htm-∉ : ∀ {y c w} Γ t → y ∉ fv t → htm ((y , c , w) ∷ Γ) t ≡ htm Γ t
htm-∉ Γ (bvar _) y∉ = refl
htm-∉ Γ Top      y∉ = refl
htm-∉ {c = sub} Γ (fvar x) y∉ = refl
htm-∉ {y} {eqv} Γ (fvar x) y∉ with x ≟ y
... | yes refl = ⊥-elim (y∉ (here refl))
... | no  _    = refl
htm-∉ Γ (lam w b) y∉ =
  cong₂ _⊔_ (htm-∉ Γ w (λ h → y∉ (∈-++⁺ˡ h)))
            (htm-∉ Γ b (λ h → y∉ (∈-++⁺ʳ (fv w) h)))
htm-∉ Γ (app a b) y∉ =
  cong₂ _⊔_ (htm-∉ Γ a (λ h → y∉ (∈-++⁺ˡ h)))
            (htm-∉ Γ b (λ h → y∉ (∈-++⁺ʳ (fv a) h)))
```

## Unfolding strictly decreases the height

The heart of the measure. `Me-Pro` replaces `x` by its annotation, prevalidity scopes that
annotation strictly earlier, and the entry `x` itself contributes the extra `suc`.

```agda
bound-fv : ∀ {Γ x c t} → Γ prevalid → (x , c , t) ∈ Γ → fv t ⊑ dom Γ
bound-fv (Pv-Ctx pv _ _ f) (here refl) h = there (f h)
bound-fv (Pv-EqA pv _ _ f) (here refl) h = there (f h)
bound-fv (Pv-Ctx pv _ _ _) (there m)   h = there (bound-fv pv m h)
bound-fv (Pv-EqA pv _ _ _) (there m)   h = there (bound-fv pv m h)

ht-unfold : ∀ {Γ x α} → Γ prevalid → x ≐ α ∈ Γ → suc (htm Γ α) ≤ hvar Γ x
ht-unfold {(y , eqv , α) ∷ Γ'} (Pv-EqA pv y∉ _ fα) (here refl) with y ≟ y
... | no  q    = ⊥-elim (q refl)
... | yes _    = s≤s (≤-reflexive (htm-∉ Γ' α (λ h → y∉ (fα h))))
ht-unfold {(y , sub , w) ∷ Γ'} {x} {α} (Pv-Ctx pv y∉ _ _) (there m) =
  ≤-trans (s≤s (≤-reflexive (htm-∉ Γ' α y∉fv))) (ht-unfold pv m)
  where
    y∉fv : y ∉ fv α
    y∉fv h = y∉ (bound-fv pv m h)
ht-unfold {(y , eqv , w) ∷ Γ'} {x} {α} (Pv-EqA pv y∉ _ _) (there m) with x ≟ y
... | yes refl = ⊥-elim (y∉ (∈-dom m))
... | no  _    = ≤-trans (s≤s (≤-reflexive (htm-∉ Γ' α y∉fv))) (ht-unfold pv m)
  where
    y∉fv : y ∉ fv α
    y∉fv h = y∉ (bound-fv pv m h)
```

## The configuration measure

A stack entry is charged one more than its own height, because `Me-FOp` will bind it to a variable
worth exactly that.

```agda
hstk : Ctx → Stack → ℕ
hstk Γ []      = 0
hstk Γ (α ∷ s) = suc (htm Γ α) ⊔ hstk Γ s

M : Ctx → Stack → Tm → ℕ
M Γ s t = htm Γ t ⊔ hstk Γ s

hvar-∉ : ∀ Γ {z} → z ∉ dom Γ → hvar Γ z ≡ 0
hvar-∉ []                   z∉ = refl
hvar-∉ ((y , sub , w) ∷ Γ) z∉ = hvar-∉ Γ (λ h → z∉ (there h))
hvar-∉ ((y , eqv , α) ∷ Γ) {z} z∉ with z ≟ y
... | yes refl = ⊥-elim (z∉ (here refl))
... | no  _    = hvar-∉ Γ (λ h → z∉ (there h))

hstk-∉ : ∀ {y c w} Γ s → y ∉ fvStack s → hstk ((y , c , w) ∷ Γ) s ≡ hstk Γ s
hstk-∉ Γ []      y∉ = refl
hstk-∉ Γ (α ∷ s) y∉ =
  cong₂ (λ p q → suc p ⊔ q)
        (htm-∉ Γ α (λ h → y∉ (∈-++⁺ˡ h)))
        (hstk-∉ Γ s (λ h → y∉ (∈-++⁺ʳ (fv α) h)))
```

Opening a body raises its height by at most the height of the name it is opened at.

```agda
htm-open : ∀ Γ k z b → htm Γ (openRec k (fvar z) b) ≤ htm Γ b ⊔ hvar Γ z
htm-open Γ k z (bvar i) with k ≟ i
... | yes _ = m≤n⊔m 0 (hvar Γ z)
... | no  _ = z≤n
htm-open Γ k z (fvar y) = m≤m⊔n (hvar Γ y) (hvar Γ z)
htm-open Γ k z Top      = z≤n
htm-open Γ k z (lam w b) =
  ⊔-lub (≤-trans (htm-open Γ k z w) (⊔-mono-≤ (m≤m⊔n (htm Γ w) (htm Γ b)) ≤-refl))
        (≤-trans (htm-open Γ (suc k) z b) (⊔-mono-≤ (m≤n⊔m (htm Γ w) (htm Γ b)) ≤-refl))
htm-open Γ k z (app a b) =
  ⊔-lub (≤-trans (htm-open Γ k z a) (⊔-mono-≤ (m≤m⊔n (htm Γ a) (htm Γ b)) ≤-refl))
        (≤-trans (htm-open Γ k z b) (⊔-mono-≤ (m≤n⊔m (htm Γ a) (htm Γ b)) ≤-refl))
```

## The rules that leave it alone

Three of the four structural rules do not increase the measure, each for its own reason.

```agda
ht-fun : ∀ Γ {z w} b → z ∉ dom Γ → z ∉ fv b
       → M ((z , sub , w) ∷ Γ) [] (b ^ fvar z) ≤ M Γ [] (lam w b)
ht-fun Γ {z} {w} b z∉Γ z∉b
  rewrite ⊔-identityʳ (htm ((z , sub , w) ∷ Γ) (b ^ fvar z))
        | ⊔-identityʳ (htm Γ (lam w b)) =
  ≤-trans (htm-open ((z , sub , w) ∷ Γ) 0 z b)
          (≤-trans (⊔-mono-≤ (≤-reflexive (htm-∉ Γ b z∉b))
                             (≤-reflexive (hvar-∉ Γ z∉Γ)))
                   (≤-trans (≤-reflexive (⊔-identityʳ (htm Γ b)))
                            (m≤n⊔m (htm Γ w) (htm Γ b))))

ht-fop : ∀ Γ {z w α} s b → z ∉ dom Γ → z ∉ fv b → z ∉ fvStack s
       → M ((z , eqv , α) ∷ Γ) s (b ^ fvar z) ≤ M Γ (α ∷ s) (lam w b)
ht-fop Γ {z} {w} {α} s b z∉Γ z∉b z∉s =
  ⊔-lub body (≤-trans (≤-reflexive (hstk-∉ Γ s z∉s))
                      (≤-trans (m≤n⊔m (suc (htm Γ α)) (hstk Γ s))
                               (m≤n⊔m (htm Γ (lam w b)) (hstk Γ (α ∷ s)))))
  where
    zval : hvar ((z , eqv , α) ∷ Γ) z ≡ suc (htm Γ α)
    zval with z ≟ z
    ... | yes _ = refl
    ... | no  q = ⊥-elim (q refl)

    body : htm ((z , eqv , α) ∷ Γ) (b ^ fvar z) ≤ htm Γ (lam w b) ⊔ hstk Γ (α ∷ s)
    body = ≤-trans (htm-open ((z , eqv , α) ∷ Γ) 0 z b)
                   (⊔-lub (≤-trans (≤-reflexive (htm-∉ Γ b z∉b))
                                      (≤-trans (m≤n⊔m (htm Γ w) (htm Γ b))
                                               (m≤m⊔n (htm Γ (lam w b)) (hstk Γ (α ∷ s)))))
                             (≤-trans (≤-reflexive zval)
                                      (≤-trans (m≤m⊔n (suc (htm Γ α)) (hstk Γ s))
                                               (m≤n⊔m (htm Γ (lam w b)) (hstk Γ (α ∷ s))))))

ht-bet : ∀ Γ {x w v} s b → x ∉ dom Γ
       → M Γ s (b ^ fvar x) ≤ M Γ s (app (lam w b) v)
ht-bet Γ {x} {w} {v} s b x∉ =
  ⊔-mono-≤ (≤-trans (htm-open Γ 0 x b)
                    (≤-trans (⊔-mono-≤ ≤-refl (≤-reflexive (hvar-∉ Γ x∉)))
                             (≤-trans (≤-reflexive (⊔-identityʳ (htm Γ b)))
                                      (≤-trans (m≤n⊔m (htm Γ w) (htm Γ b))
                                               (m≤m⊔n (htm Γ (lam w b)) (htm Γ v))))))
           ≤-refl
```

## The rule it does not survive

`Me-App` moves the operand onto the stack, where it is charged one more than its own height — the
charge `Me-FOp` needs. The term it came from was not charged that way, so the measure goes up.

Not an obstacle to be worked around: a counterexample, at the smallest configuration there is.

```agda
Me-App-nonincreasing : Set
Me-App-nonincreasing = ∀ Γ s a b → M Γ (b ∷ s) a ≤ M Γ s (app a b)

ht-app-false : ¬ Me-App-nonincreasing
ht-app-false h with h [] [] Top Top
... | ()
```

`M [] (⊤ :: nil) ⊤` is `1` and `M [] nil (⊤ ⊤)` is `0`.

The two demands are exactly opposed. `Me-FOp` binds a stack entry to a variable worth one more
than the entry, so a stack entry must carry that `suc` or the body outgrows the abstraction it came
from. `Me-App` puts an operand on the stack unchanged, so the same `suc` appears from nowhere. And
the operand cannot be charged in the term instead: `htm (app a b) = htm a ⊔ suc (htm b)` makes the
charge compound with nesting depth, and the opening lemma above then fails in its own application
case — which is how this version was arrived at.

## What this establishes

The measure is well defined, `Me-Pro` strictly decreases it, and `Me-Fun`, `Me-FOp` and `Me-Bet`
leave it alone — so four of the five rules the diamond inducts over are accounted for, machine
checked.

`Me-App` is not, and `ht-app-false` says so with a counterexample rather than a failed attempt.
That turns the obstruction from something observed while searching into something proved: no
measure of this shape can work, because the `suc` a stack entry must carry for `Me-FOp` is the
same `suc` `Me-App` cannot pay.
