# MPSS: covariant contexts, decided on the pair

Lemmas 29 and 30 are separated by whether a promotion derivation "is of the form `Co[x] ⟶≤ Co[t]`
for some covariant context `Co`". `MPSS/SubstDrop` weakens that to a condition on the source term
alone, which is enough for Lemma 30 but throws away what Lemma 29 needs: the covariant context,
and the fact that the target is `Co[t]`.

The condition stated on the *pair* recovers both, and is still a property of terms rather than of
a derivation — so it still propagates uniformly through a cofinite family, which is what made the
weakening necessary in the first place.

> `Co ::= □ | (λx≤t.Co) | (Co t)`

`CoPair x t u v` says `u = Co[x]` and `v = Co[t]` for one and the same `Co`. It is decidable, and
the decision is what Lemma 9's case split runs on.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CoPair where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)

open import MPSS.WellFormed
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug)

open import PSS.Syntax using (closeRec)
open import PSS.Close using (close-open; fv-close; open-inj)
open import PSS.Syntax using (open-lc-id)
```

## Decidable equality of terms

```agda
_≟Tm_ : (u v : Tm) → Dec (u ≡ v)
bvar i  ≟Tm bvar j  with i ≟ j
... | yes refl = yes refl
... | no  q    = no (λ { refl → q refl })
bvar _  ≟Tm fvar _  = no (λ ())
bvar _  ≟Tm Top     = no (λ ())
bvar _  ≟Tm lam _ _ = no (λ ())
bvar _  ≟Tm app _ _ = no (λ ())
fvar _  ≟Tm bvar _  = no (λ ())
fvar x  ≟Tm fvar y  with x ≟ y
... | yes refl = yes refl
... | no  q    = no (λ { refl → q refl })
fvar _  ≟Tm Top     = no (λ ())
fvar _  ≟Tm lam _ _ = no (λ ())
fvar _  ≟Tm app _ _ = no (λ ())
Top     ≟Tm bvar _  = no (λ ())
Top     ≟Tm fvar _  = no (λ ())
Top     ≟Tm Top     = yes refl
Top     ≟Tm lam _ _ = no (λ ())
Top     ≟Tm app _ _ = no (λ ())
lam _ _ ≟Tm bvar _  = no (λ ())
lam _ _ ≟Tm fvar _  = no (λ ())
lam _ _ ≟Tm Top     = no (λ ())
lam a b ≟Tm lam c d with a ≟Tm c | b ≟Tm d
... | yes refl | yes refl = yes refl
... | no  q    | _        = no (λ { refl → q refl })
... | _        | no  q    = no (λ { refl → q refl })
lam _ _ ≟Tm app _ _ = no (λ ())
app _ _ ≟Tm bvar _  = no (λ ())
app _ _ ≟Tm fvar _  = no (λ ())
app _ _ ≟Tm Top     = no (λ ())
app _ _ ≟Tm lam _ _ = no (λ ())
app a b ≟Tm app c d with a ≟Tm c | b ≟Tm d
... | yes refl | yes refl = yes refl
... | no  q    | _        = no (λ { refl → q refl })
... | _        | no  q    = no (λ { refl → q refl })
```

## The pair condition

```agda
data CoPair (x : Name) (t : Tm) : Tm → Tm → Set where
  cp-var : CoPair x t (fvar x) t
  cp-fun : ∀ {w b b'} → CoPair x t b b' → CoPair x t (lam w b) (lam w b')
  cp-app : ∀ {a a' v} → CoPair x t a a' → CoPair x t (app a v) (app a' v)
```

The covariant context it names, and the two equations that make it one.

```agda
coOf : ∀ {x t u v} → CoPair x t u v → CoCtx
coOf cp-var     = ∙
coOf (cp-fun {w = w} c) = co-fun w (coOf c)
coOf (cp-app {v = v} c) = co-app (coOf c) v

co-src : ∀ {x t u v} (c : CoPair x t u v) → u ≡ plug (coOf c) (fvar x)
co-src cp-var     = refl
co-src (cp-fun c) = cong (lam _) (co-src c)
co-src (cp-app c) = cong (λ q → app q _) (co-src c)

co-tgt : ∀ {x t u v} (c : CoPair x t u v) → v ≡ plug (coOf c) t
co-tgt cp-var     = refl
co-tgt (cp-fun c) = cong (lam _) (co-tgt c)
co-tgt (cp-app c) = cong (λ q → app q _) (co-tgt c)
```

## Decidability

```agda
coPair? : ∀ x t u v → Dec (CoPair x t u v)
coPair? x t (bvar _) v = no (λ ())
coPair? x t (fvar y) v with x ≟ y
... | no  q    = no (λ { cp-var → q refl })
... | yes refl with v ≟Tm t
...   | yes refl = yes cp-var
...   | no  q    = no (λ { cp-var → q refl })
coPair? x t Top v = no (λ ())
coPair? x t (lam w b) (bvar _) = no (λ ())
coPair? x t (lam w b) (fvar _) = no (λ ())
coPair? x t (lam w b) Top      = no (λ ())
coPair? x t (lam w b) (lam w' b') with w ≟Tm w'
... | no  q = no (λ { (cp-fun _) → q refl })
... | yes refl with coPair? x t b b'
...   | yes c = yes (cp-fun c)
...   | no  q = no (λ { (cp-fun c) → q c })
coPair? x t (lam w b) (app _ _) = no (λ ())
coPair? x t (app a v) (bvar _)  = no (λ ())
coPair? x t (app a v) (fvar _)  = no (λ ())
coPair? x t (app a v) Top       = no (λ ())
coPair? x t (app a v) (lam _ _) = no (λ ())
coPair? x t (app a v) (app a' v') with v ≟Tm v'
... | no  q = no (λ { (cp-app _) → q refl })
... | yes refl with coPair? x t a a'
...   | yes c = yes (cp-app c)
...   | no  q = no (λ { (cp-app c) → q c })
```

## Carrying the condition under a binder

`⟶ˢ-drop′` must pass its side condition into a cofinite family, so it needs the pattern to be
reflected back through opening. Matching a `CoPair` against an opened term does not work
directly — `cp-var`'s target index is `t`, and unifying it with `openRec k (fvar z) b'` is
blocked — so the equations are taken as arguments instead, and the opened terms are inverted by
hand.

```agda
close-fresh : ∀ k z u → z ∉ fv u → closeRec k z u ≡ u
close-fresh k z (bvar i) z∉ = refl
close-fresh k z (fvar y) z∉ with z ≟ y
... | yes refl = ⊥-elim (z∉ (here refl))
... | no  _    = refl
close-fresh k z Top      z∉ = refl
close-fresh k z (lam a b) z∉ =
  cong₂ lam (close-fresh k z a (λ h → z∉ (∈-++⁺ˡ h)))
            (close-fresh (suc k) z b (λ h → z∉ (∈-++⁺ʳ (fv a) h)))
close-fresh k z (app a b) z∉ =
  cong₂ app (close-fresh k z a (λ h → z∉ (∈-++⁺ˡ h)))
            (close-fresh k z b (λ h → z∉ (∈-++⁺ʳ (fv a) h)))

open-fvar-inv : ∀ k z b {y} → z ≢ y → openRec k (fvar z) b ≡ fvar y → b ≡ fvar y
open-fvar-inv k z (bvar i) z≢y e with k ≟ i
open-fvar-inv k z (bvar i) z≢y refl | yes _ = ⊥-elim (z≢y refl)
open-fvar-inv k z (bvar i) z≢y ()   | no  _
open-fvar-inv k z (fvar w) z≢y refl = refl

open-lam-inv : ∀ k z b {A B} → openRec k (fvar z) b ≡ lam A B
             → ∃[ w ] ∃[ c ] ((b ≡ lam w c)
                              × (openRec k (fvar z) w ≡ A)
                              × (openRec (suc k) (fvar z) c ≡ B))
open-lam-inv k z (bvar i) e with k ≟ i
open-lam-inv k z (bvar i) () | yes _
open-lam-inv k z (bvar i) () | no  _
open-lam-inv k z (lam w c) refl = w , c , refl , refl , refl

open-app-inv : ∀ k z b {A B} → openRec k (fvar z) b ≡ app A B
             → ∃[ a ] ∃[ v ] ((b ≡ app a v)
                              × (openRec k (fvar z) a ≡ A)
                              × (openRec k (fvar z) v ≡ B))
open-app-inv k z (bvar i) e with k ≟ i
open-app-inv k z (bvar i) () | yes _
open-app-inv k z (bvar i) () | no  _
open-app-inv k z (app a v) refl = a , v , refl , refl , refl

cp-open : ∀ {x t} k z {p q} b b'
        → z ≢ x → z ∉ fv t → z ∉ fv b → z ∉ fv b'
        → p ≡ openRec k (fvar z) b → q ≡ openRec k (fvar z) b'
        → CoPair x t p q
        → CoPair x t b b'
cp-open {x} {t} k z b b' z≢x z∉t z∉b z∉b' ep eq cp-var =
  go (open-fvar-inv k z b z≢x (sym ep)) b'≡t
  where
    b'≡t : b' ≡ t
    b'≡t = trans (sym (close-open k z b' z∉b'))
                 (trans (cong (closeRec k z) (sym eq)) (close-fresh k z t z∉t))

    go : b ≡ fvar x → b' ≡ t → CoPair x t b b'
    go refl refl = cp-var
cp-open {x} {t} k z b b' z≢x z∉t z∉b z∉b' ep eq (cp-fun {w = w₀} c)
  with open-lam-inv k z b (sym ep) | open-lam-inv k z b' (sym eq)
... | w , cc , refl , ew , ec | w' , cc' , refl , ew' , ec' =
      go (open-inj k z w w' (λ h → z∉b (∈-++⁺ˡ h)) (λ h → z∉b' (∈-++⁺ˡ h))
                   (trans ew (sym ew')))
  where
    go : w ≡ w' → CoPair x t (lam w cc) (lam w' cc')
    go refl = cp-fun (cp-open (suc k) z cc cc' z≢x z∉t
                              (λ h → z∉b (∈-++⁺ʳ _ h))
                              (λ h → z∉b' (∈-++⁺ʳ _ h))
                              (sym ec) (sym ec') c)
cp-open {x} {t} k z b b' z≢x z∉t z∉b z∉b' ep eq (cp-app {v = v₀} c)
  with open-app-inv k z b (sym ep) | open-app-inv k z b' (sym eq)
... | a , v , refl , ea , ev | a' , v' , refl , ea' , ev' =
      go (open-inj k z v v' (λ h → z∉b (∈-++⁺ʳ _ h)) (λ h → z∉b' (∈-++⁺ʳ _ h))
                   (trans ev (sym ev')))
  where
    go : v ≡ v' → CoPair x t (app a v) (app a' v')
    go refl = cp-app (cp-open k z a a' z≢x z∉t
                              (λ h → z∉b (∈-++⁺ˡ h))
                              (λ h → z∉b' (∈-++⁺ˡ h))
                              (sym ea) (sym ea') c)

cp-open₀ : ∀ {x t} k z b b'
         → z ≢ x → z ∉ fv t → z ∉ fv b → z ∉ fv b'
         → CoPair x t (openRec k (fvar z) b) (openRec k (fvar z) b')
         → CoPair x t b b'
cp-open₀ k z b b' z≢x z∉t z∉b z∉b' = cp-open k z b b' z≢x z∉t z∉b z∉b' refl refl
```

## Retargeting and opening

Changing the hole's content leaves the covariant context alone, which is what lets the narrowed
promotion be rebuilt without looking at the old derivation at all.

```agda
cp-retarget : ∀ {x t t' u v} (c : CoPair x t u v) → CoPair x t' u (plug (coOf c) t')
cp-retarget cp-var     = cp-var
cp-retarget (cp-fun c) = cp-fun (cp-retarget c)
cp-retarget (cp-app c) = cp-app (cp-retarget c)
```

The positive direction of `cp-open₀`, which needs only that the plugged term is locally closed —
opening reaches the context, never the hole.

```agda
cp-open⁺ : ∀ {x t b b'} k z → LC t
         → CoPair x t b b'
         → CoPair x t (openRec k (fvar z) b) (openRec k (fvar z) b')
cp-open⁺ {t = t} k z lt cp-var rewrite sym (open-lc-id lt k (fvar z)) = cp-var
cp-open⁺ k z lt (cp-fun c) = cp-fun (cp-open⁺ (suc k) z lt c)
cp-open⁺ k z lt (cp-app c) = cp-app (cp-open⁺ k z lt c)
```

## What this establishes

`CoPair`, the covariant-context condition stated on the source and target together; the covariant
context it names, with the two plug equations; its decidability; and `cp-open₀`, which reflects it
back through opening so that it can be carried into a cofinite family; and `cp-retarget`, which
swaps the hole's content while keeping the context.
