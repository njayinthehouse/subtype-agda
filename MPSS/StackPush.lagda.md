# MPSS: reflexivity with scoping, relabelling, and stack-monotonicity of `⟶ᵉ`

Three unconditional facts about v2's equivalence reduction that the Conjecture 8 proof plan
(`../PLAN.md`, third pass) needs first.

1. **Reflexivity, corrected.** v2's Proposition 18 claims `Γ;s ⊢ u ⟶≡ u` for every term. That
   is false for a term with a free variable outside `dom Γ` (`MPSS/Scope`), because `Me-App`
   pushes the operand and `Pv-Sta` demands it be scoped. With `fv u ⊑ dom Γ` it holds.
2. **Relabelling.** A `⟶ᵉ` derivation under `x ≤ t` never consults `x`'s entry — `Me-Pro` reads
   only `≡` annotations — so it is valid verbatim under `x ≡ α`, anywhere in the context.
3. **Stack-monotonicity.** A `⟶ᵉ` step at stack `s` holds at `s ++ s′`. The one rule that sees
   the stack's emptiness is `Me-Fun`; at a non-empty stack it becomes `Me-FOp`, whose body is
   under `x ≡ α` instead of `x ≤ t` — which is where relabelling is spent.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackPush where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import MPSS.Reduction
open import PSS.Scope using (fv-open-split)
```

## Adding a binding under a stack

Prevalidity puts context entries at the empty stack. To add one under a non-empty stack, strip
the stack, add the entry, and re-add the stack; the operands stay scoped because the domain only
grows.

```agda
prevalid-cons : ∀ {Γ s x a α}
              → Γ ∣ s prevalid → x ∉ dom Γ → LC α → fv α ⊑ dom Γ
              → ((x , a , α) ∷ Γ) ∣ s prevalid
prevalid-cons {a = sub} (Pv-Nil pv) x∉ lα fα = Pv-Nil (Pv-Ctx pv x∉ lα fα)
prevalid-cons {a = eqv} (Pv-Nil pv) x∉ lα fα = Pv-Nil (Pv-EqA pv x∉ lα fα)
prevalid-cons (Pv-Sta pv lβ fβ) x∉ lα fα =
  Pv-Sta (prevalid-cons pv x∉ lα fα) lβ (λ h → there (fβ h))
```

## Reflexivity, with the scoping hypothesis

```agda
fv-lam-ann : ∀ {t b N} → fv (lam t b) ⊑ N → fv t ⊑ N
fv-lam-ann f h = f (∈-++⁺ˡ h)

fv-lam-body : ∀ {t b N} → fv (lam t b) ⊑ N → fv b ⊑ N
fv-lam-body {t} f h = f (∈-++⁺ʳ (fv t) h)

fv-app-op : ∀ {u v N} → fv (app u v) ⊑ N → fv u ⊑ N
fv-app-op f h = f (∈-++⁺ˡ h)

fv-app-arg : ∀ {u v N} → fv (app u v) ⊑ N → fv v ⊑ N
fv-app-arg {u} f h = f (∈-++⁺ʳ (fv u) h)

fv-open-cons : ∀ {b N} x → fv b ⊑ N → fv (b ^ fvar x) ⊑ (x ∷ N)
fv-open-cons {b} x f h with fv-open-split 0 (fvar x) b h
... | inj₁ p           = there (f p)
... | inj₂ (here refl) = here refl

⟶ᵉ-refl : ∀ {Γ s t} → Γ ∣ s prevalid → LC t → fv t ⊑ dom Γ → Γ ∣ s ⊢ t ⟶ᵉ t
⟶ᵉ-refl pv lc-fvar        f = Me-Var pv
⟶ᵉ-refl pv lc-Top         f = Me-Top pv
⟶ᵉ-refl pv (lc-app {u} {v} lu lv) f =
  Me-App (⟶ᵉ-refl (Pv-Sta pv lv (fv-app-arg {u} {v} f)) lu (fv-app-op {u} {v} f))
         (⟶ᵉ-refl (prevalid-nil pv) lv (fv-app-arg {u} {v} f))
⟶ᵉ-refl {Γ} {[]} pv (lc-lam {t} {b} L lt F) f =
  Me-Fun (L ++ dom Γ) (⟶ᵉ-refl pv lt (fv-lam-ann {t} {b} f)) body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ (b ^ fvar x)
    body {x} x∉ =
      ⟶ᵉ-refl (prevalid-cons pv (∉-++ʳ L x∉) lt (fv-lam-ann {t} {b} f))
              (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))
⟶ᵉ-refl {Γ} {α ∷ s} pv (lc-lam {t} {b} L lt F) f =
  Me-FOp (L ++ dom Γ) (⟶ᵉ-refl (prevalid-nil pv) lt (fv-lam-ann {t} {b} f)) body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ (b ^ fvar x)
    body {x} x∉ =
      ⟶ᵉ-refl (prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                             (prevalid-head-lc pv) (prevalid-head-fv pv))
              (F (∉-++ˡ x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} f))

⟶ˢ-refl : ∀ {Γ s t} → Γ ∣ s prevalid → LC t → fv t ⊑ dom Γ → Γ ∣ s ⊢ t ⟶ˢ t
⟶ˢ-refl pv lt f = Ms-Equ pv (⟶ᵉ-refl pv lt f)
```

## Relabelling a subtype entry as an equivalence entry

The context `Δ ++ (x , sub , t) ∷ Γ` becomes `Δ ++ (x , eqv , α) ∷ Γ`. Domains agree, so every
scoping side condition survives; the only thing to supply is that the new entry is itself
prevalid on top of `Γ`.

```agda
dom-++ : ∀ (Δ Γ : Ctx) → dom (Δ ++ Γ) ≡ dom Δ ++ dom Γ
dom-++ []            Γ = refl
dom-++ ((x , _) ∷ Δ) Γ = cong (x ∷_) (dom-++ Δ Γ)

dom-relabel : ∀ (Δ : Ctx) {Γ x t α}
            → dom (Δ ++ (x , sub , t) ∷ Γ) ≡ dom (Δ ++ (x , eqv , α) ∷ Γ)
dom-relabel Δ {Γ} {x} {t} {α} =
  trans (dom-++ Δ ((x , sub , t) ∷ Γ)) (sym (dom-++ Δ ((x , eqv , α) ∷ Γ)))

prevalid-relabel : ∀ (Δ : Ctx) {Γ x t α}
                 → ((x , eqv , α) ∷ Γ) prevalid
                 → (Δ ++ (x , sub , t) ∷ Γ) prevalid
                 → (Δ ++ (x , eqv , α) ∷ Γ) prevalid
prevalid-relabel [] pe (Pv-Ctx _ _ _ _) = pe
prevalid-relabel ((y , sub , u) ∷ Δ) {Γ} {x} {t} {α} pe (Pv-Ctx pv y∉ lu fu) =
  Pv-Ctx (prevalid-relabel Δ pe pv)
         (subst (y ∉_) (dom-relabel Δ {Γ} {x} {t} {α}) y∉) lu
         (λ h → subst (_ ∈_) (dom-relabel Δ {Γ} {x} {t} {α}) (fu h))
prevalid-relabel ((y , eqv , u) ∷ Δ) {Γ} {x} {t} {α} pe (Pv-EqA pv y∉ lu fu) =
  Pv-EqA (prevalid-relabel Δ pe pv)
         (subst (y ∉_) (dom-relabel Δ {Γ} {x} {t} {α}) y∉) lu
         (λ h → subst (_ ∈_) (dom-relabel Δ {Γ} {x} {t} {α}) (fu h))

prevalid-relabelˢ : ∀ (Δ : Ctx) {Γ x t α s}
                  → ((x , eqv , α) ∷ Γ) prevalid
                  → (Δ ++ (x , sub , t) ∷ Γ) ∣ s prevalid
                  → (Δ ++ (x , eqv , α) ∷ Γ) ∣ s prevalid
prevalid-relabelˢ Δ pe (Pv-Nil pv) = Pv-Nil (prevalid-relabel Δ pe pv)
prevalid-relabelˢ Δ {Γ} {x} {t} {α} pe (Pv-Sta pv lβ fβ) =
  Pv-Sta (prevalid-relabelˢ Δ pe pv) lβ
         (λ h → subst (_ ∈_) (dom-relabel Δ {Γ} {x} {t} {α}) (fβ h))
```

An equivalence lookup never lands on the relabelled entry, because that entry was a subtype one.

```agda
≐-relabel : ∀ (Δ : Ctx) {Γ x t α y β}
          → y ≐ β ∈ (Δ ++ (x , sub , t) ∷ Γ)
          → y ≐ β ∈ (Δ ++ (x , eqv , α) ∷ Γ)
≐-relabel Δ m with ∈-++⁻ Δ m
... | inj₁ p           = ∈-++⁺ˡ p
... | inj₂ (there p)   = ∈-++⁺ʳ Δ (there p)

relabelᵉ : ∀ (Δ : Ctx) {Γ x t α s u v}
         → ((x , eqv , α) ∷ Γ) prevalid
         → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v
         → (Δ ++ (x , eqv , α) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v
relabelᵉ Δ pe (Me-Var pv)       = Me-Var (prevalid-relabelˢ Δ pe pv)
relabelᵉ Δ pe (Me-Top pv)       = Me-Top (prevalid-relabelˢ Δ pe pv)
relabelᵉ Δ pe (Me-TAp pv)       = Me-TAp (prevalid-relabelˢ Δ pe pv)
relabelᵉ Δ pe (Me-Pro pv m d)   =
  Me-Pro (prevalid-relabelˢ Δ pe pv) (≐-relabel Δ m) (relabelᵉ Δ pe d)
relabelᵉ Δ pe (Me-App d e)      = Me-App (relabelᵉ Δ pe d) (relabelᵉ Δ pe e)
relabelᵉ Δ pe (Me-Bet {u' = u'} L F e)    =
  Me-Bet {u' = u'} L (λ x∉ → relabelᵉ Δ pe (F x∉)) (relabelᵉ Δ pe e)
relabelᵉ Δ pe (Me-Fun {t = t′} {u' = u'} L d F) =
  Me-Fun {u' = u'} L (relabelᵉ Δ pe d)
         (λ {y} y∉ → relabelᵉ ((y , sub , t′) ∷ Δ) pe (F y∉))
relabelᵉ Δ pe (Me-FOp {α = β} {u' = u'} L d F) =
  Me-FOp {u' = u'} L (relabelᵉ Δ pe d)
         (λ {y} y∉ → relabelᵉ ((y , eqv , β) ∷ Δ) pe (F y∉))
```

## Stack-monotonicity

```agda
pushᵉ : ∀ {Γ s s′ u v}
      → Γ ∣ s ⊢ u ⟶ᵉ v
      → Γ ∣ (s ++ s′) prevalid
      → Γ ∣ (s ++ s′) ⊢ u ⟶ᵉ v
pushᵉ (Me-Var _)       pv = Me-Var pv
pushᵉ (Me-Top _)       pv = Me-Top pv
pushᵉ (Me-TAp _)       pv = Me-TAp pv
pushᵉ (Me-Pro _ m d)   pv = Me-Pro pv m (pushᵉ d pv)
pushᵉ {s = s} (Me-App {v = w} d e) pv =
  Me-App (pushᵉ d (Pv-Sta pv (prevalid-head-lc pv₀) (prevalid-head-fv pv₀))) e
  where
    pv₀ = ⟶ᵉ-prevalid d
pushᵉ (Me-Bet {u' = u'} L F e)   pv = Me-Bet {u' = u'} L (λ x∉ → pushᵉ (F x∉) pv) e
pushᵉ {s′ = []} (Me-Fun L d F) pv = Me-Fun L d F
pushᵉ {Γ} {s′ = α ∷ s″} (Me-Fun {t = t} {u = u} {u' = u'} L d F) pv =
  Me-FOp {u' = u'} (L ++ dom Γ) d body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , eqv , α) ∷ Γ) ∣ s″ ⊢ (u ^ fvar x) ⟶ᵉ (u' ^ fvar x)
    body {x} x∉ =
      pushᵉ (relabelᵉ [] pe (F (∉-++ˡ x∉))) pv′
      where
        pe : ((x , eqv , α) ∷ Γ) prevalid
        pe = Pv-EqA (prevalid-ctx pv) (∉-++ʳ L x∉) (prevalid-head-lc pv) (prevalid-head-fv pv)
        pv′ : ((x , eqv , α) ∷ Γ) ∣ s″ prevalid
        pv′ = prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                            (prevalid-head-lc pv) (prevalid-head-fv pv)
pushᵉ {Γ} {s = α ∷ s₀} {s′} (Me-FOp {u = u} {u' = u'} L d F) pv =
  Me-FOp {u' = u'} (L ++ dom Γ) d body
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , eqv , α) ∷ Γ) ∣ (s₀ ++ s′) ⊢ (u ^ fvar x) ⟶ᵉ (u' ^ fvar x)
    body {x} x∉ =
      pushᵉ (F (∉-++ˡ x∉))
            (prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                           (prevalid-head-lc pv) (prevalid-head-fv pv))
```

## What this establishes

- `⟶ᵉ-refl`, `⟶ˢ-refl`: v2's Proposition 18 with the scoping hypothesis it needs.
- `relabelᵉ`: a `⟶ᵉ` derivation is insensitive to whether a variable is bound by `≤` or `≡`.
- `pushᵉ`: **equivalence reduction is stack-monotone.** This is the first of the two facts the
  reduction of `AppCongr₁` to `FunStep` in `MPSS/Conjecture8Star` needs.

The relabelling lemma is what makes `pushᵉ` go through at `Me-Fun`, and it is also the reason
the same statement is *false* for `⟶ˢ`: a promotion derivation under `x ≤ t` may use `Ms-Pro` on
`x`, which has no counterpart under `x ≡ α` (`MPSS/Diff`, `push-is-false`).
