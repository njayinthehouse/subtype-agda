# MPSS: narrowing a context from subtype entries to equivalence entries

The push lemma of the Conjecture 8 plan replays a body derivation made under `x ≤ w` in a
context where the parameter is instead bound `x ≡ α`, with `α ≤*wf w` in hand. Several
parameters may have been narrowed at once, so the relation between the two contexts is a
pointwise one: entries agree, except that a subtype entry `x ≤ w` on the left may face an
equivalence entry `x ≡ α` on the right, with `α ≤*wf w` in the prefix context on the left.

This module defines that relation and proves what every rule other than `Ms-Pro` on a narrowed
variable needs: domains agree, prevalidity transfers, lookups that do not hit a narrowed entry
transfer, a subtype lookup that does hit one yields the operand and its derivation, and
equivalence reduction transfers verbatim, since it never reads a subtype entry.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Narrow where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import MPSS.WellFormed
open import MPSS.Weakening using (⊑*wf-weaken₁)
open import PSS.Scope using (fv-open-lower)
```

## Well-formed terms are scoped

Needed to show that a narrowed entry's operand is scoped, from its derivation.

```agda
wf-fv    : ∀ {Γ t} → Γ ⊢ t wf → fv t ⊑ dom Γ
⊑*wf-fvˡ : ∀ {Γ u m t} → Γ ⊢ u ⊑*wf[ m ] t → fv u ⊑ dom Γ

wf-fv (Wf-PrS _ m) (here refl)  = ∈-dom m
wf-fv (Wf-PrE _ m) (here refl)  = ∈-dom m
wf-fv (Wf-Top _)   ()
wf-fv {Γ} (Wf-Fun {t = t} {u = u} L F d) h with ∈-++⁻ (fv t) h
... | inj₁ p = wf-fv d p
... | inj₂ p = body p
  where
    x   = fresh (L ++ fv u)
    x∉L = ∉-++ˡ (fresh-∉ (L ++ fv u))
    x∉u : x ∉ fv u
    x∉u = ∉-++ʳ L (fresh-∉ (L ++ fv u))

    body : ∀ {y} → y ∈ fv u → y ∈ dom Γ
    body {y} q with wf-fv (F x∉L) (fv-open-lower 0 (fvar x) u q)
    ... | here refl = ⊥-elim (x∉u q)
    ... | there r   = r
wf-fv (Wf-App {u = u} d₁ d₂) h with ∈-++⁻ (fv u) h
... | inj₁ p = ⊑*wf-fvˡ d₁ p
... | inj₂ p = ⊑*wf-fvˡ d₂ p

⊑*wf-fvˡ (Ws-Sub w _ _)  = wf-fv w
⊑*wf-fvˡ (Ws-Trs d _ _)  = ⊑*wf-fvˡ d
```

## The relation

```agda
infix 4 _▷_
data _▷_ : Ctx → Ctx → Set where

  n-nil  : [] ▷ []

  n-keep : ∀ {Γˢ Γᵉ x a t}
         → Γˢ ▷ Γᵉ
         → ((x , a , t) ∷ Γˢ) ▷ ((x , a , t) ∷ Γᵉ)

  n-eqv  : ∀ {Γˢ Γᵉ x w α}
         → Γˢ ▷ Γᵉ
         → Γˢ ⊢ α ≤*wf w
         → ((x , sub , w) ∷ Γˢ) ▷ ((x , eqv , α) ∷ Γᵉ)

▷-refl : ∀ Γ → Γ ▷ Γ
▷-refl []                = n-nil
▷-refl ((x , a , t) ∷ Γ) = n-keep (▷-refl Γ)
```

## Domains agree, prevalidity transfers

```agda
▷-dom : ∀ {Γˢ Γᵉ} → Γˢ ▷ Γᵉ → dom Γˢ ≡ dom Γᵉ
▷-dom n-nil                = refl
▷-dom (n-keep {x = x} n)   = cong (x ∷_) (▷-dom n)
▷-dom (n-eqv {x = x} n _)  = cong (x ∷_) (▷-dom n)

▷-prevalid : ∀ {Γˢ Γᵉ} → Γˢ ▷ Γᵉ → Γˢ prevalid → Γᵉ prevalid
▷-prevalid n-nil pv = pv
▷-prevalid (n-keep {a = sub} n) (Pv-Ctx pv x∉ lt ft) =
  Pv-Ctx (▷-prevalid n pv) (subst (_ ∉_) (▷-dom n) x∉) lt
         (λ h → subst (_ ∈_) (▷-dom n) (ft h))
▷-prevalid (n-keep {a = eqv} n) (Pv-EqA pv x∉ lt ft) =
  Pv-EqA (▷-prevalid n pv) (subst (_ ∉_) (▷-dom n) x∉) lt
         (λ h → subst (_ ∈_) (▷-dom n) (ft h))
▷-prevalid (n-eqv n h) (Pv-Ctx pv x∉ _ _) =
  Pv-EqA (▷-prevalid n pv) (subst (_ ∉_) (▷-dom n) x∉)
         (wf⇒lc wα) (λ k → subst (_ ∈_) (▷-dom n) (wf-fv wα k))
  where wα = ⊑*wf⇒wfˡ h

▷-prevalidˢ : ∀ {Γˢ Γᵉ s} → Γˢ ▷ Γᵉ → Γˢ ∣ s prevalid → Γᵉ ∣ s prevalid
▷-prevalidˢ n (Pv-Nil pv)       = Pv-Nil (▷-prevalid n pv)
▷-prevalidˢ n (Pv-Sta pv lα fα) =
  Pv-Sta (▷-prevalidˢ n pv) lα (λ h → subst (_ ∈_) (▷-dom n) (fα h))
```

## Lookups

An equivalence lookup is never narrowed. A subtype lookup either survives or hits a narrowed
entry, in which case the operand and its derivation come back, weakened to the whole left
context.

```agda
▷-≐ : ∀ {Γˢ Γᵉ y β} → Γˢ ▷ Γᵉ → y ≐ β ∈ Γˢ → y ≐ β ∈ Γᵉ
▷-≐ (n-keep n)  (here refl) = here refl
▷-≐ (n-keep n)  (there m)   = there (▷-≐ n m)
▷-≐ (n-eqv n _) (there m)   = there (▷-≐ n m)

▷-≤ : ∀ {Γˢ Γᵉ y t} → Γˢ ▷ Γᵉ → Γˢ prevalid → y ≤ t ∈ Γˢ
    → (y ≤ t ∈ Γᵉ) ⊎ (∃[ α ] ((y ≐ α ∈ Γᵉ) × (Γˢ ⊢ α ≤*wf t)))
▷-≤ (n-keep n)  pv (here refl) = inj₁ (here refl)
▷-≤ (n-keep n)  pv (there m) with ▷-≤ n (tail-prevalid pv) m
... | inj₁ k              = inj₁ (there k)
... | inj₂ (α , k , h)    = inj₂ (α , there k , ⊑*wf-weaken₁ pv h)
▷-≤ (n-eqv n h) pv (here refl) = inj₂ (_ , here refl , ⊑*wf-weaken₁ pv h)
▷-≤ (n-eqv n _) pv (there m) with ▷-≤ n (tail-prevalid pv) m
... | inj₁ k              = inj₁ (there k)
... | inj₂ (α , k , h)    = inj₂ (α , there k , ⊑*wf-weaken₁ pv h)
```

## Equivalence reduction transfers

Stated generically: any two contexts with the same domain, transferable prevalidity and
transferable equivalence lookups support the same `⟶ᵉ` derivations. All three hypotheses are
stable under extending both contexts by the same entry, which is what the binder cases need.

```agda
record Transfer (Γ₁ Γ₂ : Ctx) : Set where
  field
    t-dom : dom Γ₁ ≡ dom Γ₂
    t-pv  : Γ₁ prevalid → Γ₂ prevalid
    t-≐   : ∀ {y β} → y ≐ β ∈ Γ₁ → y ≐ β ∈ Γ₂

open Transfer

transfer-ext : ∀ {Γ₁ Γ₂ x a t} → Transfer Γ₁ Γ₂ → Transfer ((x , a , t) ∷ Γ₁) ((x , a , t) ∷ Γ₂)
transfer-ext {x = x} T = record
  { t-dom = cong (x ∷_) (t-dom T)
  ; t-pv  = pv-ext
  ; t-≐   = λ { (here refl) → here refl ; (there m) → there (t-≐ T m) } }
  where
    pv-ext : ∀ {x a t} → ((x , a , t) ∷ _) prevalid → ((x , a , t) ∷ _) prevalid
    pv-ext (Pv-Ctx pv x∉ lt ft) =
      Pv-Ctx (t-pv T pv) (subst (_ ∉_) (t-dom T) x∉) lt (λ h → subst (_ ∈_) (t-dom T) (ft h))
    pv-ext (Pv-EqA pv x∉ lt ft) =
      Pv-EqA (t-pv T pv) (subst (_ ∉_) (t-dom T) x∉) lt (λ h → subst (_ ∈_) (t-dom T) (ft h))

transfer-pvˢ : ∀ {Γ₁ Γ₂ s} → Transfer Γ₁ Γ₂ → Γ₁ ∣ s prevalid → Γ₂ ∣ s prevalid
transfer-pvˢ T (Pv-Nil pv)       = Pv-Nil (t-pv T pv)
transfer-pvˢ T (Pv-Sta pv lα fα) =
  Pv-Sta (transfer-pvˢ T pv) lα (λ h → subst (_ ∈_) (t-dom T) (fα h))

⟶ᵉ-transfer : ∀ {Γ₁ Γ₂ s u v} → Transfer Γ₁ Γ₂ → Γ₁ ∣ s ⊢ u ⟶ᵉ v → Γ₂ ∣ s ⊢ u ⟶ᵉ v
⟶ᵉ-transfer T (Me-Var pv)      = Me-Var (transfer-pvˢ T pv)
⟶ᵉ-transfer T (Me-Top pv)      = Me-Top (transfer-pvˢ T pv)
⟶ᵉ-transfer T (Me-TAp pv)      = Me-TAp (transfer-pvˢ T pv)
⟶ᵉ-transfer T (Me-Pro pv m d)  = Me-Pro (transfer-pvˢ T pv) (t-≐ T m) (⟶ᵉ-transfer T d)
⟶ᵉ-transfer T (Me-App d e)     = Me-App (⟶ᵉ-transfer T d) (⟶ᵉ-transfer T e)
⟶ᵉ-transfer T (Me-Bet {u' = u'} L F e) =
  Me-Bet {u' = u'} L (λ x∉ → ⟶ᵉ-transfer T (F x∉)) (⟶ᵉ-transfer T e)
⟶ᵉ-transfer T (Me-Fun {u' = u'} L d F) =
  Me-Fun {u' = u'} L (⟶ᵉ-transfer T d) (λ x∉ → ⟶ᵉ-transfer (transfer-ext T) (F x∉))
⟶ᵉ-transfer T (Me-FOp {u' = u'} L d F) =
  Me-FOp {u' = u'} L (⟶ᵉ-transfer T d) (λ x∉ → ⟶ᵉ-transfer (transfer-ext T) (F x∉))

▷-transfer : ∀ {Γˢ Γᵉ} → Γˢ ▷ Γᵉ → Transfer Γˢ Γᵉ
▷-transfer n = record { t-dom = ▷-dom n ; t-pv = ▷-prevalid n ; t-≐ = ▷-≐ n }

⟶ᵉ-▷ : ∀ {Γˢ Γᵉ s u v} → Γˢ ▷ Γᵉ → Γˢ ∣ s ⊢ u ⟶ᵉ v → Γᵉ ∣ s ⊢ u ⟶ᵉ v
⟶ᵉ-▷ n = ⟶ᵉ-transfer (▷-transfer n)
```

Narrowing is stable under extending both sides by the same entry, and under extending both
contexts of an `Ms-Fun`/`Ms-FOp` body.

```agda
▷-ext : ∀ {Γˢ Γᵉ x a t} → Γˢ ▷ Γᵉ → ((x , a , t) ∷ Γˢ) ▷ ((x , a , t) ∷ Γᵉ)
▷-ext = n-keep
```

## What this establishes

The narrowing relation `Γˢ ▷ Γᵉ` and everything about it that is rule-independent: domains
agree, prevalidity transfers, equivalence lookups transfer, a subtype lookup that hits a
narrowed entry returns the operand with its derivation weakened to the full context, and
`⟶ᵉ` transfers verbatim (`⟶ᵉ-▷`). The one thing that does *not* transfer is `Ms-Pro` on a
narrowed variable, which is where the replay of the plan does its work.
