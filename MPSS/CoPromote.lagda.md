# MPSS: rebuilding a covariant promotion

Lemma 24's remaining obligation is the narrowed promotion itself: from `Co[x] ⟶≤ Co[t]` in
`Γ, x≤t, Γ′`, obtain `Co[x] ⟶≤ Co[t′]` in `Γ, x≤t′, Γ′`.

The obvious route — walk the old derivation and rebuild it — runs into the cofinite families of
`Ms-Fun` and `Ms-FOp`, where a case analysis on the derivation need not come out the same way for
every fresh name. There is no need to walk it. A covariant promotion is determined by its
covariant context and the annotation it reads: given `CoPair x t′ u v`, the derivation can be
*built from scratch*, and `MPSS/CoPair`'s `cp-retarget` supplies that witness from the old one.

What the construction actually needs is only scoping — local closure of the term and of the new
annotation, and the membership `x ≤ t′`. Well-formedness would be the wrong hypothesis here: the
abstraction case at a non-empty stack uses `Ms-FOp`, which binds the parameter to the stack head
with an *equivalence* annotation, and a well-formedness derivation for the body speaks about the
subtype annotation instead.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CoPromote where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

open import MPSS.WellFormed
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug)
open import MPSS.CoPair using (CoPair; cp-var; cp-fun; cp-app; coOf; cp-open⁺)
open import MPSS.StackPush using (prevalid-cons)

open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ)
```

## Free variables under opening

```agda
fv-open : ∀ k z b {y} → y ∈ fv (openRec k (fvar z) b) → (y ≡ z) ⊎ (y ∈ fv b)
fv-open k z (bvar i) h with k ≟ i
fv-open k z (bvar i) (here p) | yes _ = inj₁ p
fv-open k z (bvar i) ()       | no  _
fv-open k z (fvar w) h = inj₂ h
fv-open k z Top      ()
fv-open k z (lam a b) {y} h with ∈-++⁻ (fv (openRec k (fvar z) a)) h
... | inj₁ p with fv-open k z a p
...   | inj₁ q = inj₁ q
...   | inj₂ q = inj₂ (∈-++⁺ˡ q)
fv-open k z (lam a b) {y} h | inj₂ p with fv-open (suc k) z b p
...   | inj₁ q = inj₁ q
...   | inj₂ q = inj₂ (∈-++⁺ʳ (fv a) q)
fv-open k z (app a b) {y} h with ∈-++⁻ (fv (openRec k (fvar z) a)) h
... | inj₁ p with fv-open k z a p
...   | inj₁ q = inj₁ q
...   | inj₂ q = inj₂ (∈-++⁺ˡ q)
fv-open k z (app a b) {y} h | inj₂ p with fv-open k z b p
...   | inj₁ q = inj₁ q
...   | inj₂ q = inj₂ (∈-++⁺ʳ (fv a) q)

fv-open⊑ : ∀ {Γ : Ctx} k z b → fv b ⊑ dom Γ
         → fv (openRec k (fvar z) b) ⊑ (z ∷ dom Γ)
fv-open⊑ k z b f h with fv-open k z b h
... | inj₁ refl = here refl
... | inj₂ q    = there (f q)
```

## Building the promotion

```agda
cp-promote : ∀ {Γ s x t' u v}
           → CoPair x t' u v
           → LC u → fv u ⊑ dom Γ → LC t'
           → x ≤ t' ∈ Γ
           → Γ ∣ s prevalid
           → Γ ∣ s ⊢ u ⟶ˢ v

cp-promote cp-var lu fu lt' m pv = Ms-Pro pv m

cp-promote (cp-app c) (lc-app la lw) fu lt' m pv =
  Ms-App (cp-promote c la (λ h → fu (∈-++⁺ˡ h)) lt' m
                     (Pv-Sta pv lw (λ h → fu (∈-++⁺ʳ _ h))))
```

At an abstraction the stack decides the rule, and with it which kind of annotation the parameter
picks up — `Ms-Fun` takes the abstraction's own, `Ms-FOp` takes the stack head. Either way the
recursive call needs only that the new entry is scoped, which prevalidity of the stack already
gives in the second case and the term's own local closure gives in the first.

```agda
cp-promote {Γ} {[]} {x} {t'} (cp-fun {w = w} {b} {b'} c)
           (lc-lam L lw F) fu lt' m pv =
  Ms-Fun (L ++ dom Γ) fam
  where
    fam : ∀ {z} → z ∉ (L ++ dom Γ)
        → ((z , sub , w) ∷ Γ) ∣ [] ⊢ (b ^ fvar z) ⟶ˢ (b' ^ fvar z)
    fam {z} z∉ =
      cp-promote (cp-open⁺ 0 z lt' c)
                 (F (∉-++ˡ z∉))
                 (fv-open⊑ 0 z b (λ h → fu (∈-++⁺ʳ (fv w) h)))
                 lt' (there m)
                 (prevalid-cons pv (∉-++ʳ L z∉) lw (λ h → fu (∈-++⁺ˡ h)))

cp-promote {Γ} {α ∷ s} {x} {t'} (cp-fun {w = w} {b} {b'} c)
           (lc-lam L lw F) fu lt' m pv =
  Ms-FOp (L ++ dom Γ) fam
  where
    fam : ∀ {z} → z ∉ (L ++ dom Γ)
        → ((z , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar z) ⟶ˢ (b' ^ fvar z)
    fam {z} z∉ =
      cp-promote (cp-open⁺ 0 z lt' c)
                 (F (∉-++ˡ z∉))
                 (fv-open⊑ 0 z b (λ h → fu (∈-++⁺ʳ (fv w) h)))
                 lt' (there m)
                 (prevalid-cons (prevalid-pop pv) (∉-++ʳ L z∉)
                                (prevalid-head-lc pv) (prevalid-head-fv pv))
```

## What this establishes

`cp-promote`: a covariant promotion can be built from its covariant context, its target
annotation, and scoping alone. With `cp-retarget` this gives the narrowed promotion —
`Co[x] ⟶≤ Co[t′]` from `Co[x] ⟶≤ Co[t]` — without inspecting the old derivation, which is what
keeps the cofinite families uniform. Together with `MPSS/CoNarrow`'s well-formedness and
`MPSS/Narrow24`'s split, Lemma 24's third conclusion is complete.
