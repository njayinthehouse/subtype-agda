# MPSS: the mixed diamond — an original step against a variant step, joined in one step each

`MPSS/DiamondStep` closes every case of Lemma 2 for the original relation `⟶ᵉ` against the
diamond as a hypothesis and leaves the induction open; `MPSS/NoMeasure` shows no measure on
configurations can carry it, and `../PLAN.md` records the failure of every measure on the pair of
derivations tried. This module proves the *mixed* statement:

> If `Γ₀;s₀ ⊢ t₀ ⟶ᵉ′ t₁` (variant: promotion premises at the empty stack) and
> `Γ₀;s₀ ⊢ t₀ ⟶ᵉ t₂` (original), then for context reductions `Γ₀;s₀ ↣′ Γ₁;s₁` (variant pieces)
> and `Γ₀;s₀ ↣ Γ₂;s₂` (original pieces) there is `t₃` with `Γ₁;s₁ ⊢ t₁ ⟶ᵉ t₃` and
> `Γ₂;s₂ ⊢ t₂ ⟶ᵉ t₃`, both **original one-step** reductions.

The recursion is `DiamondStep`'s, with one asymmetry: when the variant side promotes against an
original variable, its premise is at the empty stack, so the recursive call is at the empty stack
on the annotation, with the annotation's piece from the original side's context reduction as the
new original derivation. That call is where every symmetric measure failed — the pulled piece was
pushed under the current stack — and here it is what makes the measure work: the call discards
the stack pieces and every piece not reachable from the annotation. When the original side
promotes, its premise is a subderivation. So the measure is on the original side alone:
`MPSS/MixedMeasure`'s `Ψ`, the size of the original derivation plus the sizes of the live pieces
of its context reduction, and `MPSS/Sized` supplies the sizes.

The invariant is `DiamondStep`'s: the join is derivable with any closed set of names removed that
the other edge and the other context reduction avoid.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.MixedDiamond where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_; ≤-trans; ≤-refl; m≤m+n; m≤n+m; n≤1+n)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; Σ; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-eqv; ↣-empty; ↣-nil)
open import MPSS.CtxPrevalid using (↣-prevalid)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ)
open import MPSS.StackPush using (pushᵉ; ⟶ᵉ-refl)
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.Rename using (⟶ᵉ-rename-head)
open import MPSS.Open using (⟶ᵉ-subst₀; ⟶ᵉ-open₀)
open import MPSS.SubstEqv using (⟶ᵉ-subst≡-head)
open import MPSS.Strengthen using (Avoids; unbound-avoids)
open import MPSS.AvoidsPreserve using (avoids-push; avoids-weaken)
open import MPSS.Closed
open import MPSS.Drop
open import MPSS.Subst.Base using (∉-stack)
open import MPSS.DiamondStep
  using (Pieces; Pieces*; unbound-pieces; pieces-empty; avoids-eqv; Popped; same; piece;
         ↣-pop; pop-piece; PoppedAvoids; pieces-pop; avoids-pop; ↣-closed;
         remove; remove-⊑; ∉-remove; ∈-remove; ∖-remove; closed-remove; head-∉′; ≐-unique;
         close-rename₀; stack-free)
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-lc; fv-⟶ᵉ′; ⟶ᵉ′-weaken; ⟶ᵉ′-prevalid)
open import MPSS.VariantPush using (pushᵉ′)
open import MPSS.VariantCtx
open import MPSS.VariantAvoids
  using (Avoids′; Avoids*′; stack-free′; avoids-push′; avoids-weaken′; unbound-avoids′;
         fv-closed′; ↣′-stack-closed)
open import MPSS.VariantDiamond
  using (Pieces′; Pieces*′; unbound-pieces′; pieces-empty′; avoids-eqv′; Popped′; same′; piece′;
         ↣′-pop; pop-piece′; PoppedAvoids′; pieces-pop′; avoids-pop′; ↣′-closed)
open import MPSS.Sized
open import MPSS.Uniform using (SizedCtx; uniform; uniformCtx; stack-lc)
open import MPSS.MixedMeasure
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; subst-intro; closeRec)
open import PSS.Close using (open-close; fv-close)
```

## The statement

The first edge `v` is variant, the second `d` original; each side's join is derivable with any
closed set removed that the *other* edge and the other context reduction avoid.

```agda
Join : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂}
     → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁ → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂
     → Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂ → Set
Join {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t₀} {t₁} {t₂} v d c₁ c₂ =
  ∃[ t₃ ] ((∀ B → Closed Γ₀ B → Avoids* B d → Pieces* B c₂ → (Γ₁ ∖ B) ∣ s₁ ⊢ t₁ ⟶ᵉ t₃)
         × (∀ B → Closed Γ₀ B → Avoids*′ B v → Pieces*′ B c₁ → (Γ₂ ∖ B) ∣ s₂ ⊢ t₂ ⟶ᵉ t₃))

-- the induction hypothesis: the statement whenever the original side measures below k
IH : ℕ → Set
IH k = ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂ n}
     → LC t₀
     → (v : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁) (d : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂) → Sized d n
     → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
     → Ψ c₂ sc n t₀ < k
     → Join v d c₁ c₂
```

## The cases

```agda
module _ (k : ℕ) (ih : IH k) where
```

### Leaves

```agda
  var-var : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
          → Join (Me-Var′ {x = x} pv) (Me-Var pv′) c₁ c₂
  var-var {x = x} pv pv′ c₁ c₂ =
    _ , (λ B cl av pc → Me-Var (prevalid-∖-ext (↣′-closed cl c₁)
                                 (↣′-stack-closed cl (stack-free (Me-Var {x = x} pv′) av) c₁)
                                 (↣′-prevalid pv c₁)))
      , (λ B cl av pc → Me-Var (prevalid-∖-ext (↣-closed cl c₂)
                                 (↣-stack-closed cl (stack-free′ (Me-Var′ {x = x} pv) av) c₂)
                                 (↣-prevalid pv c₂)))

  top-top : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
          → Join (Me-Top′ pv) (Me-Top pv′) c₁ c₂
  top-top pv pv′ c₁ c₂ =
    Top , (λ B cl av pc → Me-Top (prevalid-∖-ext (↣′-closed cl c₁)
                                   (↣′-stack-closed cl (stack-free (Me-Top pv′) av) c₁)
                                   (↣′-prevalid pv c₁)))
        , (λ B cl av pc → Me-Top (prevalid-∖-ext (↣-closed cl c₂)
                                   (↣-stack-closed cl (stack-free′ (Me-Top′ pv) av) c₂)
                                   (↣-prevalid pv c₂)))

  tap-tap : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
          → Join (Me-TAp′ {u = u} pv) (Me-TAp pv′) c₁ c₂
  tap-tap {u = u} pv pv′ c₁ c₂ =
    Top , (λ B cl av pc → Me-Top (prevalid-∖-ext (↣′-closed cl c₁)
                                   (↣′-stack-closed cl (stack-free (Me-TAp {u = u} pv′) av) c₁)
                                   (↣′-prevalid pv c₁)))
        , (λ B cl av pc → Me-Top (prevalid-∖-ext (↣-closed cl c₂)
                                   (↣-stack-closed cl (stack-free′ (Me-TAp′ {u = u} pv) av) c₂)
                                   (↣-prevalid pv c₂)))

  tap-app : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u u'} (pv : Γ₀ ∣ s₀ prevalid)
            (pv′ : Γ₀ ∣ (u ∷ s₀) prevalid) (e : Γ₀ ∣ [] ⊢ u ⟶ᵉ u')
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
          → Join (Me-TAp′ pv) (Me-App (Me-Top pv′) e) c₁ c₂
  tap-app {u = u} pv pv′ e c₁ c₂ =
    Top , (λ B cl av pc → Me-Top (prevalid-∖-ext (↣′-closed cl c₁)
                                   (↣′-stack-closed cl (∉*-++ʳ (fv u) (stack-free (Me-Top pv′) (λ b∈ → proj₁ (av b∈)))) c₁)
                                   (↣′-prevalid pv c₁)))
        , (λ B cl av pc → Me-TAp (prevalid-∖-ext (↣-closed cl c₂)
                                   (↣-stack-closed cl (stack-free′ (Me-TAp′ {u = u} pv) av) c₂)
                                   (↣-prevalid pv c₂)))

  app-tap : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u u'} (pv : Γ₀ ∣ s₀ prevalid)
            (pv′ : Γ₀ ∣ (u ∷ s₀) prevalid) (e : Γ₀ ∣ [] ⊢ u ⟶ᵉ′ u')
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂)
          → Join (Me-App′ (Me-Top′ pv′) e) (Me-TAp pv) c₁ c₂
  app-tap {u = u} pv pv′ e c₁ c₂ =
    Top , (λ B cl av pc → Me-TAp (prevalid-∖-ext (↣′-closed cl c₁)
                                   (↣′-stack-closed cl (stack-free (Me-TAp {u = u} pv) av) c₁)
                                   (↣′-prevalid pv c₁)))
        , (λ B cl av pc → Me-Top (prevalid-∖-ext (↣-closed cl c₂)
                                   (↣-stack-closed cl (∉*-++ʳ (fv u) (stack-free′ (Me-Top′ pv′) (λ b∈ → proj₁ (av b∈)))) c₂)
                                   (↣-prevalid pv c₂)))
```

### The variable cases

Both promote: the variant premise is pushed under the stack, the original premise is a
subderivation, and the call is at the annotation under the same stack.

```agda
  pro-pro : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x α α′ α₁ α₂ n} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (m : x ≐ α ∈ Γ₀) (m′ : x ≐ α′ ∈ Γ₀)
            (e′ : Γ₀ ∣ [] ⊢ α ⟶ᵉ′ α₁) (e : Γ₀ ∣ s₀ ⊢ α′ ⟶ᵉ α₂) (se : Sized e n)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc n) (fvar x) ≤ k
          → Join (Me-Pro′ pv m e′) (Me-Pro pv′ m′ e) c₁ c₂
  pro-pro {Γ₀} {s₀} {x = x} {α = α} pv pv′ m m′ e′ e se c₁ c₂ sc bd
    with ≐-unique (prevalid-ctx pv) m m′
  ... | refl with ih (prevalid-bound-lc (prevalid-ctx pv) m)
                     (pushᵉ′ {s = []} {s′ = s₀} e′ pv) e se c₁ c₂ sc
                     (≤-trans (Ψ-pro c₂ sc (prevalid-ctx pv) m) bd)
  ...   | t₃ , f₁ , f₂ =
    t₃ , (λ B cl av pc → f₁ B cl (λ b∈ → proj₂ (proj₂ (av b∈))) pc)
       , (λ B cl av pc → f₂ B cl (λ b∈ → avoids-push′ e′ pv (proj₂ (proj₂ (av b∈))) (proj₁ (proj₂ (av b∈)))) pc)
```

The variant variable against the original promotion: the piece copied out of `c₁` is variant,
pushed under the stack against the original premise; the variant side reaches the join by an
original promotion at `Γ₁ ∖ B`.

```agda
  var-pro : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x α α₁ n} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (m : x ≐ α ∈ Γ₀) (e : Γ₀ ∣ s₀ ⊢ α ⟶ᵉ α₁) (se : Sized e n)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc n) (fvar x) ≤ k
          → Join (Me-Var′ {x = x} pv) (Me-Pro pv′ m e) c₁ c₂
  var-pro {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {x} {α} pv pv′ m e se c₁ c₂ sc bd
    with ↣′-eqv (prevalid-ctx pv) c₁ m | avoids-eqv″
    where
      avoids-eqv″ : ∀ {b} → Pieces′ b c₁ → Avoids′ b (proj₂ (proj₂ (↣′-eqv (prevalid-ctx pv) c₁ m)))
      avoids-eqv″ = avoids-eqv′ (prevalid-ctx pv) c₁ m
  ... | α′ , m′ , e′ | av-e′
    with ih (prevalid-bound-lc (prevalid-ctx pv) m)
            (pushᵉ′ {s = []} {s′ = s₀} e′ pv) e se c₁ c₂ sc
            (≤-trans (Ψ-pro c₂ sc (prevalid-ctx pv) m) bd)
  ...   | t₃ , f₁ , f₂ =
    t₃ , (λ B cl av pc →
            Me-Pro (prevalid-∖-ext (↣′-closed cl c₁)
                                   (↣′-stack-closed cl (stack-free (Me-Pro pv′ m e) av) c₁)
                                   (↣′-prevalid pv c₁))
                   (∈-∖ (λ x∈B → proj₁ (av x∈B) refl) m′)
                   (f₁ B cl (λ b∈ → proj₂ (proj₂ (av b∈))) pc))
       , (λ B cl av pc → f₂ B cl (λ b∈ → avoids-push′ e′ pv (av-e′ (pc b∈)) (av b∈)) pc)
```

The variant promotion against the original variable — the case that decides the induction. The
variant premise sits at the empty stack; the piece copied out of `c₂` is original and at the
empty stack too, and becomes the recursive call's original derivation, with its size read off
the sized context reduction. The original side reaches the join by promoting at `Γ₂ ∖ B` and
pushing the recursive join under its reduced stack.

```agda
  pro-var : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x α α₁} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (m : x ≐ α ∈ Γ₀) (e′ : Γ₀ ∣ [] ⊢ α ⟶ᵉ′ α₁)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc 1 (fvar x) ≤ k
          → Join (Me-Pro′ pv m e′) (Me-Var {x = x} pv′) c₁ c₂
  pro-var {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {x} {α} pv pv′ m e′ c₁ c₂ sc bd
    with ↣-eqv (prevalid-ctx pv) c₂ m | avoids-eqv″ | Sized-eqv (prevalid-ctx pv) c₂ sc m
    where
      avoids-eqv″ : ∀ {b} → Pieces b c₂ → Avoids b (proj₂ (proj₂ (↣-eqv (prevalid-ctx pv) c₂ m)))
      avoids-eqv″ = avoids-eqv (prevalid-ctx pv) c₂ m
  ... | α′ , m′ , e | av-e | se
    with ih (prevalid-bound-lc (prevalid-ctx pv) m) e′ e se
            (↣′-empty c₁) (↣-empty c₂) (sizedEmpty c₂ sc)
            (≤-trans (Ψ-pull c₂ sc (prevalid-ctx pv) m) bd)
  ...   | t₃ , f₁ , f₂ =
    t₃ , (λ B cl av pc →
            pushᵉ {s = []} {s′ = s₁}
                  (f₁ B cl (λ b∈ → av-e (pc b∈)) (λ b∈ → pieces-empty c₂ (pc b∈)))
                  (prevalid-∖-ext (↣′-closed cl c₁)
                                  (↣′-stack-closed cl (stack-free (Me-Var {x = x} pv′) av) c₁)
                                  (↣′-prevalid pv c₁)))
       , (λ B cl av pc →
            Me-Pro (prevalid-∖-ext (↣-closed cl c₂)
                                   (↣-stack-closed cl (stack-free′ (Me-Pro′ pv m e′) av) c₂)
                                   (↣-prevalid pv c₂))
                   (∈-∖ (λ x∈B → proj₁ (av x∈B) refl) m′)
                   (pushᵉ {s = []} {s′ = s₂}
                          (f₂ B cl (λ b∈ → proj₂ (proj₂ (av b∈))) (λ b∈ → pieces-empty′ c₁ (pc b∈)))
                          (prevalid-∖-ext (↣-closed cl c₂)
                                          (↣-stack-closed cl (stack-free′ (Me-Pro′ pv m e′) av) c₂)
                                          (↣-prevalid pv c₂))))
```

### Application

```agda
  app-app : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u v u₁ v₁ u₂ v₂ n₁ n₂} → LC u → LC v
          → (o₁ : Γ₀ ∣ (v ∷ s₀) ⊢ u ⟶ᵉ′ u₁) (p₁ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₁)
          → (o₂ : Γ₀ ∣ (v ∷ s₀) ⊢ u ⟶ᵉ u₂) (p₂ : Γ₀ ∣ [] ⊢ v ⟶ᵉ v₂)
          → (so : Sized o₂ n₁) (sp : Sized p₂ n₂)
          → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc (n₁ + n₂)) (app u v) ≤ k
          → Join (Me-App′ o₁ p₁) (Me-App o₂ p₂) c₁ c₂
  app-app {Γ₀} {s₀} {u = u} {v = v} {n₁ = n₁} {n₂} lu lv o₁ p₁ o₂ p₂ so sp c₁ c₂ sc bd
    with ih lu o₁ o₂ so (Ct-Stk′ c₁ p₁) (Ct-Stk c₂ p₂) (sc , n₂ , sp)
            (≤-trans (Ψ-app-op {u = u} {v = v} c₂ sc sp) bd)
       | ih lv p₁ p₂ sp (↣′-empty c₁) (↣-empty c₂) (sizedEmpty c₂ sc)
            (≤-trans (Ψ-arg {u = u} {v = v} c₂ sc (m≤n+m n₂ n₁)) bd)
  ... | u₃ , g₁ , g₂ | v₃ , h₁ , h₂ =
    app u₃ v₃
    , (λ B cl av pc → Me-App (g₁ B cl (λ b∈ → proj₁ (av b∈)) (λ b∈ → pc b∈ , proj₂ (av b∈)))
                             (h₁ B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty c₂ (pc b∈))))
    , (λ B cl av pc → Me-App (g₂ B cl (λ b∈ → proj₁ (av b∈)) (λ b∈ → pc b∈ , proj₂ (av b∈)))
                             (h₂ B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈))))
```

### Abstraction against abstraction, at the empty stack

The body join is taken at one fresh name and closed over it; each side's family is recovered by
renaming, at the context with `B` removed, exactly as in `MPSS/DiamondStep`.

```agda
  fun-fun : ∀ {Γ₀ Γ₁ Γ₂ t u t₁ u₁ t₂ u₂ n₁ n₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x))
          → (L₁ : List Name) (a₁ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₁)
            (F₁ : ∀ {x} → x ∉ L₁ → ((x , sub , t) ∷ Γ₀) ∣ [] ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
          → (L₂ : List Name) (a₂ : Γ₀ ∣ [] ⊢ t ⟶ᵉ t₂)
            (F₂ : ∀ {x} → x ∉ L₂ → ((x , sub , t) ∷ Γ₀) ∣ [] ⊢ (u ^ fvar x) ⟶ᵉ (u₂ ^ fvar x))
          → (sa : Sized a₂ n₁) (sF : ∀ {x} (x∉ : x ∉ L₂) → Sized (F₂ x∉) n₂)
          → (c₁ : Γ₀ ∣ [] ↣′ Γ₁ ∣ []) (c₂ : Γ₀ ∣ [] ↣ Γ₂ ∣ []) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc (n₁ + n₂)) (lam t u) ≤ k
          → Join (Me-Fun′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-Fun {u = u} {u' = u₂} L₂ a₂ F₂) c₁ c₂
  fun-fun {Γ₀} {Γ₁} {Γ₂} {t} {u} {t₁} {u₁} {t₂} {u₂} {n₁} {n₂} L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ sa sF c₁ c₂ sc bd =
    lam t₃ b₃ , side₁ , side₂
    where
      A = L₀ ++ L₁ ++ L₂ ++ dom Γ₀ ++ dom Γ₁ ++ dom Γ₂ ++ fv u ++ fv u₁ ++ fv u₂ ++ fv t₁ ++ fv t₂
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L₁ = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L₁ r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ₀ : x ∉ dom Γ₀
      x∉Γ₀ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ₀) r₃
      x∉Γ₁ : x ∉ dom Γ₁
      x∉Γ₁ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ₁) r₄
      x∉Γ₂ : x ∉ dom Γ₂
      x∉Γ₂ = ∉-++ˡ r₅
      r₆ = ∉-++ʳ (dom Γ₂) r₅
      x∉u : x ∉ fv u
      x∉u = ∉-++ˡ r₆
      r₇ = ∉-++ʳ (fv u) r₆
      x∉u₁ : x ∉ fv u₁
      x∉u₁ = ∉-++ˡ r₇
      r₈ = ∉-++ʳ (fv u₁) r₇
      x∉u₂ : x ∉ fv u₂
      x∉u₂ = ∉-++ˡ r₈
      r₉ = ∉-++ʳ (fv u₂) r₈
      x∉t₁ : x ∉ fv t₁
      x∉t₁ = ∉-++ˡ r₉
      x∉t₂ : x ∉ fv t₂
      x∉t₂ = ∉-++ʳ (fv t₁) r₉

      ja = ih lt a₁ a₂ sa (↣′-empty c₁) (↣-empty c₂) (sizedEmpty c₂ sc)
              (≤-trans (Ψ-ann {t = t} {u = u} c₂ sc (m≤m+n n₁ n₂)) bd)
      t₃ = proj₁ ja
      jb = ih (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂) (sF x∉L₂)
              (Ct-Ann′ c₁ a₁) (Ct-Ann c₂ a₂) (sc , n₁ , sa)
              (≤-trans (Ψ-fun-body {x = x} {u = u} c₂ sc sa x∉Γ₀) bd)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ-lc (⟶ᵉ′-lc (F₀ x∉L₀) (F₁ x∉L₁))
                  (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids* B (Me-Fun {u = u} {u' = u₂} L₂ a₂ F₂) → Pieces* B c₂
            → (Γ₁ ∖ B) ∣ [] ⊢ lam t₁ u₁ ⟶ᵉ lam t₃ b₃
      side₁ B cl av pc = Me-Fun A (proj₁ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈)))
                                                    (λ b∈ → pieces-empty c₂ (pc b∈))) body
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , sub , t) ∷ Γ₀) B′
          cl′ = closed-sub (closed-remove x∉Γ₀ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids* B′ (F₂ x∉L₂)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₂
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces* B′ (Ct-Ann {x = x} {c = sub} c₂ a₂)
          pc′ b∈ = pc (remove-⊑ {x} {B} b∈) , proj₁ (proj₂ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , sub , t₁) ∷ Γ₁) ∖ B′) ∣ [] ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g = proj₁ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , sub , t₁) ∷ (Γ₁ ∖ B)) ∣ [] ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g′ rewrite sym (∖-remove Γ₁ {B} x∉Γ₁) | sym (∖-∉ {Γ₁} {B′} {x} {sub} {t₁} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , sub , t₁) ∷ (Γ₁ ∖ B)) ∣ [] ⊢ (u₁ ^ fvar y) ⟶ᵉ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ-rename-head {b = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) (∉-dom-∖ Γ₁ y∉Γ₁) x∉t₁ x∉u₁ (λ ()) lw₃ g′
            where
              y∉Γ₁ : y ∉ dom Γ₁
              y∉Γ₁ = ∉-++ˡ (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉))))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Fun′ {u = u} {u' = u₁} L₁ a₁ F₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ [] ⊢ lam t₂ u₂ ⟶ᵉ lam t₃ b₃
      side₂ B cl av pc = Me-Fun A (proj₂ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈)))
                                                    (λ b∈ → pieces-empty′ c₁ (pc b∈))) body
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , sub , t) ∷ Γ₀) B′
          cl′ = closed-sub (closed-remove x∉Γ₀ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids*′ B′ (F₁ x∉L₁)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₁
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces*′ B′ (Ct-Ann′ {x = x} {c = sub} c₁ a₁)
          pc′ b∈ = pc (remove-⊑ {x} {B} b∈) , proj₁ (proj₂ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , sub , t₂) ∷ Γ₂) ∖ B′) ∣ [] ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g = proj₂ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , sub , t₂) ∷ (Γ₂ ∖ B)) ∣ [] ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g′ rewrite sym (∖-remove Γ₂ {B} x∉Γ₂) | sym (∖-∉ {Γ₂} {B′} {x} {sub} {t₂} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , sub , t₂) ∷ (Γ₂ ∖ B)) ∣ [] ⊢ (u₂ ^ fvar y) ⟶ᵉ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ-rename-head {b = u₂} x y (∉-dom-∖ Γ₂ x∉Γ₂) (∉-dom-∖ Γ₂ y∉Γ₂) x∉t₂ x∉u₂ (λ ()) lw₃ g′
            where
              y∉Γ₂ : y ∉ dom Γ₂
              y∉Γ₂ = ∉-++ˡ (∉-++ʳ (dom Γ₁) (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉)))))
```

### Abstraction against abstraction, under a stack

The stack head is popped off both context reductions and the parameter bound to it; the
original side's popped piece carries its size into the extended sized context.

```agda
  fop-fop : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ α t u t₁ u₁ t₂ u₂ n₁ n₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x))
          → (L₁ : List Name) (a₁ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₁)
            (F₁ : ∀ {x} → x ∉ L₁ → ((x , eqv , α) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
          → (L₂ : List Name) (a₂ : Γ₀ ∣ [] ⊢ t ⟶ᵉ t₂)
            (F₂ : ∀ {x} → x ∉ L₂ → ((x , eqv , α) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ (u₂ ^ fvar x))
          → (sa : Sized a₂ n₁) (sF : ∀ {x} (x∉ : x ∉ L₂) → Sized (F₂ x∉) n₂)
          → (c₁ : Γ₀ ∣ (α ∷ s₀) ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ (α ∷ s₀) ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc (n₁ + n₂)) (lam t u) ≤ k
          → Join (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-FOp {u = u} {u' = u₂} L₂ a₂ F₂) c₁ c₂
  fop-fop {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {α} {t} {u} {t₁} {u₁} {t₂} {u₂} {n₁} {n₂}
          L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ sa sF c₁ c₂ sc bd =
    lam t₃ b₃ , side₁ , side₂
    where
      pv₀ : Γ₀ ∣ (α ∷ s₀) prevalid
      pv₀ = ⟶ᵉ-prevalid (Me-FOp {u = u} {u' = u₂} L₂ a₂ F₂)
      pvn = prevalid-nil pv₀
      lα  = prevalid-head-lc pv₀
      fα  = prevalid-head-fv pv₀

      pop₁ = ↣′-pop c₁
      α₁   = proj₁ pop₁
      s₁′  = proj₁ (proj₂ pop₁)
      eq₁  = proj₁ (proj₂ (proj₂ pop₁))
      c₁′  = proj₁ (proj₂ (proj₂ (proj₂ pop₁)))
      pp₁  = proj₂ (proj₂ (proj₂ (proj₂ pop₁)))
      q₁   = pop-piece′ pvn lα fα pp₁
      pop₂ = ↣-pop c₂
      α₂   = proj₁ pop₂
      s₂′  = proj₁ (proj₂ pop₂)
      eq₂  = proj₁ (proj₂ (proj₂ pop₂))
      c₂′  = popCtx c₂
      pp₂  = popPc c₂
      q₂   = pop-piece pvn lα fα pp₂
      sc₂′ = proj₁ (sizedPop c₂ sc)
      m₂   = proj₁ (proj₂ (sizedPop c₂ sc))
      sq₂  = Sized-pop pvn lα fα pp₂ (proj₂ (proj₂ (sizedPop c₂ sc)))

      A = L₀ ++ L₁ ++ L₂ ++ dom Γ₀ ++ dom Γ₁ ++ dom Γ₂ ++ fv u ++ fv u₁ ++ fv u₂
          ++ fv α₁ ++ fv α₂ ++ fvStack s₁′ ++ fvStack s₂′
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L₁ = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L₁ r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ₀ : x ∉ dom Γ₀
      x∉Γ₀ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ₀) r₃
      x∉Γ₁ : x ∉ dom Γ₁
      x∉Γ₁ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ₁) r₄
      x∉Γ₂ : x ∉ dom Γ₂
      x∉Γ₂ = ∉-++ˡ r₅
      r₆ = ∉-++ʳ (dom Γ₂) r₅
      r₇ = ∉-++ʳ (fv u) r₆
      x∉u₁ : x ∉ fv u₁
      x∉u₁ = ∉-++ˡ r₇
      r₈ = ∉-++ʳ (fv u₁) r₇
      x∉u₂ : x ∉ fv u₂
      x∉u₂ = ∉-++ˡ r₈
      r₉ = ∉-++ʳ (fv u₂) r₈
      x∉α₁ : x ∉ fv α₁
      x∉α₁ = ∉-++ˡ r₉
      r₁₀ = ∉-++ʳ (fv α₁) r₉
      x∉α₂ : x ∉ fv α₂
      x∉α₂ = ∉-++ˡ r₁₀
      r₁₁ = ∉-++ʳ (fv α₂) r₁₀
      x∉s₁ : x ∉ fvStack s₁′
      x∉s₁ = ∉-++ˡ r₁₁
      x∉s₂ : x ∉ fvStack s₂′
      x∉s₂ = ∉-++ʳ (fvStack s₁′) r₁₁

      ja = ih lt a₁ a₂ sa (↣′-empty c₁) (↣-empty c₂) (sizedEmpty c₂ sc)
              (≤-trans (Ψ-ann {t = t} {u = u} c₂ sc (m≤m+n n₁ n₂)) bd)
      t₃ = proj₁ ja
      jb = ih (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂) (sF x∉L₂)
              (Ct-Ann′ {x = x} {c = eqv} c₁′ q₁) (Ct-Ann {x = x} {c = eqv} c₂′ q₂) (sc₂′ , m₂ , sq₂)
              (≤-trans (Ψ-fop-body {x = x} {t = t} {u = u} c₂ sc pvn lα fα x∉Γ₀) bd)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ-lc (⟶ᵉ′-lc (F₀ x∉L₀) (F₁ x∉L₁))
                  (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids* B (Me-FOp {u = u} {u' = u₂} L₂ a₂ F₂) → Pieces* B c₂
            → (Γ₁ ∖ B) ∣ s₁ ⊢ lam t₁ u₁ ⟶ᵉ lam t₃ b₃
      side₁ B cl av pc =
        subst (λ s → (Γ₁ ∖ B) ∣ s ⊢ lam t₁ u₁ ⟶ᵉ lam t₃ b₃) (sym eq₁)
              (Me-FOp A (proj₁ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈)))
                                            (λ b∈ → pieces-empty c₂ (pc b∈))) body)
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , eqv , α) ∷ Γ₀) B′
          cl′ = closed-eqv (closed-remove x∉Γ₀ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids* B′ (F₂ x∉L₂)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₂
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces* B′ (Ct-Ann {x = x} {c = eqv} c₂′ q₂)
          pc′ b∈ = proj₁ (pieces-pop c₂ (pc (remove-⊑ {x} {B} b∈)))
                 , avoids-pop pvn lα fα pp₂ (proj₂ (pieces-pop c₂ (pc (remove-⊑ {x} {B} b∈))))
                              (proj₁ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , eqv , α₁) ∷ Γ₁) ∖ B′) ∣ s₁′ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g = proj₁ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , eqv , α₁) ∷ (Γ₁ ∖ B)) ∣ s₁′ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g′ rewrite sym (∖-remove Γ₁ {B} x∉Γ₁) | sym (∖-∉ {Γ₁} {B′} {x} {eqv} {α₁} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , eqv , α₁) ∷ (Γ₁ ∖ B)) ∣ s₁′ ⊢ (u₁ ^ fvar y) ⟶ᵉ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ-rename-head {b = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) (∉-dom-∖ Γ₁ y∉Γ₁) x∉α₁ x∉u₁ x∉s₁ lw₃ g′
            where
              y∉Γ₁ : y ∉ dom Γ₁
              y∉Γ₁ = ∉-++ˡ (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉))))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ F₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ s₂ ⊢ lam t₂ u₂ ⟶ᵉ lam t₃ b₃
      side₂ B cl av pc =
        subst (λ s → (Γ₂ ∖ B) ∣ s ⊢ lam t₂ u₂ ⟶ᵉ lam t₃ b₃) (sym eq₂)
              (Me-FOp A (proj₂ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈)))
                                            (λ b∈ → pieces-empty′ c₁ (pc b∈))) body)
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , eqv , α) ∷ Γ₀) B′
          cl′ = closed-eqv (closed-remove x∉Γ₀ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids*′ B′ (F₁ x∉L₁)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₁
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces*′ B′ (Ct-Ann′ {x = x} {c = eqv} c₁′ q₁)
          pc′ b∈ = proj₁ (pieces-pop′ c₁ (pc (remove-⊑ {x} {B} b∈)))
                 , avoids-pop′ pvn lα fα pp₁ (proj₂ (pieces-pop′ c₁ (pc (remove-⊑ {x} {B} b∈))))
                               (proj₁ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , eqv , α₂) ∷ Γ₂) ∖ B′) ∣ s₂′ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g = proj₂ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , eqv , α₂) ∷ (Γ₂ ∖ B)) ∣ s₂′ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g′ rewrite sym (∖-remove Γ₂ {B} x∉Γ₂) | sym (∖-∉ {Γ₂} {B′} {x} {eqv} {α₂} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , eqv , α₂) ∷ (Γ₂ ∖ B)) ∣ s₂′ ⊢ (u₂ ^ fvar y) ⟶ᵉ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ-rename-head {b = u₂} x y (∉-dom-∖ Γ₂ x∉Γ₂) (∉-dom-∖ Γ₂ y∉Γ₂) x∉α₂ x∉u₂ x∉s₂ lw₃ g′
            where
              y∉Γ₂ : y ∉ dom Γ₂
              y∉Γ₂ = ∉-++ˡ (∉-++ʳ (dom Γ₁) (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉)))))
```

### Contraction against contraction

```agda
  bet-bet : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t u v u₁ v₁ u₂ v₂ n₁ n₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x)) → LC v
          → (L₁ : List Name) (F₁ : ∀ {x} → x ∉ L₁ → Γ₀ ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
            (p₁ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₁)
          → (L₂ : List Name) (F₂ : ∀ {x} → x ∉ L₂ → Γ₀ ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ (u₂ ^ fvar x))
            (p₂ : Γ₀ ∣ [] ⊢ v ⟶ᵉ v₂)
          → (sF : ∀ {x} (x∉ : x ∉ L₂) → Sized (F₂ x∉) n₁) (sp : Sized p₂ n₂)
          → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc (n₁ + n₂)) (app (lam t u) v) ≤ k
          → Join (Me-Bet′ {t = t} {u = u} {u' = u₁} L₁ F₁ p₁) (Me-Bet {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) c₁ c₂
  bet-bet {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t} {u} {v} {u₁} {v₁} {u₂} {v₂} {n₁} {n₂}
          L₀ lt F₀ lv L₁ F₁ p₁ L₂ F₂ p₂ sF sp c₁ c₂ sc bd =
    (b₃ ^ v₃) , side₁ , side₂
    where
      A = L₀ ++ L₁ ++ L₂ ++ dom Γ₀ ++ dom Γ₁ ++ dom Γ₂ ++ fv u ++ fv u₁ ++ fv u₂
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L₁ = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L₁ r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ₀ : x ∉ dom Γ₀
      x∉Γ₀ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ₀) r₃
      x∉Γ₁ : x ∉ dom Γ₁
      x∉Γ₁ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ₁) r₄
      x∉Γ₂ : x ∉ dom Γ₂
      x∉Γ₂ = ∉-++ˡ r₅
      r₆ = ∉-++ʳ (dom Γ₂) r₅
      r₇ = ∉-++ʳ (fv u) r₆
      x∉u₁ : x ∉ fv u₁
      x∉u₁ = ∉-++ˡ r₇
      x∉u₂ : x ∉ fv u₂
      x∉u₂ = ∉-++ʳ (fv u₁) r₇

      jp = ih lv p₁ p₂ sp (↣′-empty c₁) (↣-empty c₂) (sizedEmpty c₂ sc)
              (≤-trans (Ψ-arg {u = lam t u} {v = v} c₂ sc (m≤n+m n₂ n₁)) bd)
      v₃ = proj₁ jp
      jb = ih (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂) (sF x∉L₂) c₁ c₂ sc
              (≤-trans (Ψ-bet-body {x = x} {t = t} {u = u} {v = v} c₂ sc x∉Γ₀ (m≤m+n n₁ n₂)) bd)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ-lc (⟶ᵉ′-lc (F₀ x∉L₀) (F₁ x∉L₁))
                  (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids* B (Me-Bet {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) → Pieces* B c₂
            → (Γ₁ ∖ B) ∣ s₁ ⊢ (u₁ ^ v₁) ⟶ᵉ (b₃ ^ v₃)
      side₁ B cl av pc =
        ⟶ᵉ-open₀ {u = u₁} {u′ = b₃} A (⟶ᵉ′-lc lv p₁) (⟶ᵉ-lc (⟶ᵉ′-lc lv p₁) h)
                 (λ {y} y∉ → close-rename₀ {u = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) x∉u₁ lw₃ g) h
        where
          g : (Γ₁ ∖ B) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g = proj₁ (proj₂ jb) B cl (λ b∈ → proj₁ (av b∈) x∉L₂) pc
          h : (Γ₁ ∖ B) ∣ [] ⊢ v₁ ⟶ᵉ v₃
          h = proj₁ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty c₂ (pc b∈))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Bet′ {t = t} {u = u} {u' = u₁} L₁ F₁ p₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ s₂ ⊢ (u₂ ^ v₂) ⟶ᵉ (b₃ ^ v₃)
      side₂ B cl av pc =
        ⟶ᵉ-open₀ {u = u₂} {u′ = b₃} A (⟶ᵉ-lc lv p₂) (⟶ᵉ-lc (⟶ᵉ-lc lv p₂) h)
                 (λ {y} y∉ → close-rename₀ {u = u₂} x y (∉-dom-∖ Γ₂ x∉Γ₂) x∉u₂ lw₃ g) h
        where
          g : (Γ₂ ∖ B) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g = proj₂ (proj₂ jb) B cl (λ b∈ → proj₁ (av b∈) x∉L₁) pc
          h : (Γ₂ ∖ B) ∣ [] ⊢ v₂ ⟶ᵉ v₃
          h = proj₂ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈))
```

### Variant application over `Me-FOp′` against original contraction

The original `Me-Bet` body is weakened to the extended context, which preserves its size.

```agda
  app-bet : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t u v t₁ u₁ v₁ u₂ v₂ n₁ n₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x)) → LC v
          → (L₁ : List Name) (a₁ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₁)
            (G₁ : ∀ {x} → x ∉ L₁ → ((x , eqv , v) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
            (p₁ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₁)
          → (L₂ : List Name) (F₂ : ∀ {x} → x ∉ L₂ → Γ₀ ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ (u₂ ^ fvar x))
            (p₂ : Γ₀ ∣ [] ⊢ v ⟶ᵉ v₂)
          → (sF : ∀ {x} (x∉ : x ∉ L₂) → Sized (F₂ x∉) n₁) (sp : Sized p₂ n₂)
          → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc (n₁ + n₂)) (app (lam t u) v) ≤ k
          → Join (Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁)
                 (Me-Bet {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) c₁ c₂
  app-bet {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t} {u} {v} {t₁} {u₁} {v₁} {u₂} {v₂} {n₁} {n₂}
          L₀ lt F₀ lv L₁ a₁ G₁ p₁ L₂ F₂ p₂ sF sp c₁ c₂ sc bd =
    (b₃ ^ v₃) , side₁ , side₂
    where
      A = L₀ ++ L₁ ++ L₂ ++ dom Γ₀ ++ dom Γ₁ ++ dom Γ₂ ++ fv u ++ fv u₁ ++ fv u₂
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L₁ = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L₁ r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ₀ : x ∉ dom Γ₀
      x∉Γ₀ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ₀) r₃
      x∉Γ₁ : x ∉ dom Γ₁
      x∉Γ₁ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ₁) r₄
      x∉Γ₂ : x ∉ dom Γ₂
      x∉Γ₂ = ∉-++ˡ r₅
      r₆ = ∉-++ʳ (dom Γ₂) r₅
      r₇ = ∉-++ʳ (fv u) r₆
      x∉u₁ : x ∉ fv u₁
      x∉u₁ = ∉-++ˡ r₇
      x∉u₂ : x ∉ fv u₂
      x∉u₂ = ∉-++ʳ (fv u₁) r₇

      pvx : ((x , eqv , v) ∷ Γ₀) ∣ s₀ prevalid
      pvx = ⟶ᵉ′-prevalid (G₁ x∉L₁)
      pv₀ : Γ₀ ∣ s₀ prevalid
      pv₀ = ⟶ᵉ-prevalid (F₂ x∉L₂)
      fvv : fv v ⊑ dom Γ₀
      fvv = head-fv (prevalid-ctx pvx)

      F₂ʷ : ((x , eqv , v) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ (u₂ ^ fvar x)
      F₂ʷ = ⟶ᵉ-weaken [] ((x , eqv , v) ∷ []) pvx (F₂ x∉L₂)
      sF₂ʷ : Sized F₂ʷ n₁
      sF₂ʷ = Sized-weaken [] ((x , eqv , v) ∷ []) pvx (F₂ x∉L₂) (sF x∉L₂)

      jp = ih lv p₁ p₂ sp (↣′-empty c₁) (↣-empty c₂) (sizedEmpty c₂ sc)
              (≤-trans (Ψ-arg {u = lam t u} {v = v} c₂ sc (m≤n+m n₂ n₁)) bd)
      v₃ = proj₁ jp
      jb = ih (F₀ x∉L₀) (G₁ x∉L₁) F₂ʷ sF₂ʷ
              (Ct-Ann′ {x = x} {c = eqv} c₁ p₁) (Ct-Ann {x = x} {c = eqv} c₂ p₂) (sc , n₂ , sp)
              (≤-trans (Ψ-app-bet-body {x = x} {t = t} {u = u} c₂ sc sp x∉Γ₀ ≤-refl) bd)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ-lc (⟶ᵉ′-lc (F₀ x∉L₀) (G₁ x∉L₁))
                  (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids* B (Me-Bet {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) → Pieces* B c₂
            → (Γ₁ ∖ B) ∣ s₁ ⊢ app (lam t₁ u₁) v₁ ⟶ᵉ (b₃ ^ v₃)
      side₁ B cl av pc =
        Me-Bet {t = t₁} {u = u₁} {u' = b₃} A
               (λ {y} y∉ → close-rename₀ {u = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) x∉u₁ lw₃ g′) h
        where
          cl′ : Closed ((x , eqv , v) ∷ Γ₀) (x ∷ B)
          cl′ = closed-add (prevalid-ctx pv₀) x∉Γ₀ cl
          av′ : Avoids* (x ∷ B) F₂ʷ
          av′ (here refl) = avoids-weaken [] _ pvx (F₂ x∉L₂) (unbound-avoids x x∉Γ₀ (F₂ x∉L₂))
          av′ (there b∈)  = avoids-weaken [] _ pvx (F₂ x∉L₂) (proj₁ (av b∈) x∉L₂)
          pc′ : Pieces* (x ∷ B) (Ct-Ann {x = x} {c = eqv} c₂ p₂)
          pc′ (here refl) = unbound-pieces x x∉Γ₀ c₂ , unbound-avoids x x∉Γ₀ p₂
          pc′ (there b∈)  = pc b∈ , proj₂ (av b∈)
          g : (((x , eqv , v₁) ∷ Γ₁) ∖ (x ∷ B)) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g = proj₁ (proj₂ jb) (x ∷ B) cl′ av′ pc′
          g′ : (Γ₁ ∖ B) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g′ = subst (λ Γ → Γ ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃)
                     (trans (∖-∈ {Γ₁} {x ∷ B} {x} {eqv} {v₁} (here refl)) (∖-∉dom Γ₁ x∉Γ₁)) g
          h : (Γ₁ ∖ B) ∣ [] ⊢ v₁ ⟶ᵉ v₃
          h = proj₁ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty c₂ (pc b∈))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ s₂ ⊢ (u₂ ^ v₂) ⟶ᵉ (b₃ ^ v₃)
      side₂ B cl av pc =
        ⟶ᵉ-subst≡-head {u = u₂} {u′ = b₃} x x∉u₂ (fv-close 0 x w₃) x∉s₂
                       (⟶ᵉ-lc lv p₂) (⟶ᵉ-lc (⟶ᵉ-lc lv p₂) h) fvv₂ g″ h
        where
          B″ = remove x B
          x∉B″ : x ∉ B″
          x∉B″ = ∉-remove {x} {B}
          v∉ : B ∉* fv v
          v∉ b∈ = proj₁ (proj₁ (av b∈))
          cl″ : Closed ((x , eqv , v) ∷ Γ₀) B″
          cl″ = closed-eqv (closed-remove x∉Γ₀ cl) (λ b∈ → v∉ (remove-⊑ {x} {B} b∈))
          av″ : Avoids*′ B″ (G₁ x∉L₁)
          av″ b∈ = proj₂ (proj₂ (proj₁ (av (remove-⊑ {x} {B} b∈)))) x∉L₁
                         (λ eq → x∉B″ (subst (_∈ B″) (sym eq) b∈))
          pc″ : Pieces*′ B″ (Ct-Ann′ {x = x} {c = eqv} c₁ p₁)
          pc″ b∈ = pc (remove-⊑ {x} {B} b∈) , proj₂ (av (remove-⊑ {x} {B} b∈))
          g : (((x , eqv , v₂) ∷ Γ₂) ∖ B″) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g = proj₂ (proj₂ jb) B″ cl″ av″ pc″
          g′ : ((x , eqv , v₂) ∷ (Γ₂ ∖ B)) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g′ rewrite sym (∖-remove Γ₂ {B} x∉Γ₂) | sym (∖-∉ {Γ₂} {B″} {x} {eqv} {v₂} x∉B″) = g
          g″ : ((x , eqv , v₂) ∷ (Γ₂ ∖ B)) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ (b₃ ^ fvar x)
          g″ rewrite open-close lw₃ 0 x = g′
          h : (Γ₂ ∖ B) ∣ [] ⊢ v₂ ⟶ᵉ v₃
          h = proj₂ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈))
          x∉s₂ : x ∉ fvStack s₂
          x∉s₂ = ∉-stack (↣-prevalid pv₀ c₂) x∉Γ₂
          fvv₂ : fv v₂ ⊑ dom (Γ₂ ∖ B)
          fvv₂ {y} h′ = ∈-dom-∖ Γ₂ (λ y∈B → fv-closed cl (λ _ ()) v∉ p₂ y∈B h′)
                                  (fv-⟶ᵉ (λ q → subst (_ ∈_) (↣-dom c₂) q) p₂
                                          (λ q → subst (_ ∈_) (↣-dom c₂) (fvv q)) h′)
```

### Variant contraction against original application over `Me-FOp`

The mirror orientation; now the variant `Me-Bet′` body is weakened, which costs nothing, and
the original `Me-FOp` body is a subderivation.

```agda
  bet-app : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t u v u₁ v₁ t₂ u₂ v₂ n₀ n₁ n₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x)) → LC v
          → (L₁ : List Name) (F₁ : ∀ {x} → x ∉ L₁ → Γ₀ ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
            (p₁ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₁)
          → (L₂ : List Name) (a₂ : Γ₀ ∣ [] ⊢ t ⟶ᵉ t₂)
            (G₂ : ∀ {x} → x ∉ L₂ → ((x , eqv , v) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ (u₂ ^ fvar x))
            (p₂ : Γ₀ ∣ [] ⊢ v ⟶ᵉ v₂)
          → (sa : Sized a₂ n₀) (sG : ∀ {x} (x∉ : x ∉ L₂) → Sized (G₂ x∉) n₁) (sp : Sized p₂ n₂)
          → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
          → Ψ c₂ sc (suc (suc (n₀ + n₁) + n₂)) (app (lam t u) v) ≤ k
          → Join (Me-Bet′ {t = t} {u = u} {u' = u₁} L₁ F₁ p₁)
                 (Me-App (Me-FOp {u = u} {u' = u₂} L₂ a₂ G₂) p₂) c₁ c₂
  bet-app {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t} {u} {v} {u₁} {v₁} {t₂} {u₂} {v₂} {n₀} {n₁} {n₂}
          L₀ lt F₀ lv L₁ F₁ p₁ L₂ a₂ G₂ p₂ sa sG sp c₁ c₂ sc bd =
    (b₃ ^ v₃) , side₁ , side₂
    where
      A = L₀ ++ L₁ ++ L₂ ++ dom Γ₀ ++ dom Γ₁ ++ dom Γ₂ ++ fv u ++ fv u₁ ++ fv u₂
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L₁ = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L₁ r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ₀ : x ∉ dom Γ₀
      x∉Γ₀ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ₀) r₃
      x∉Γ₁ : x ∉ dom Γ₁
      x∉Γ₁ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ₁) r₄
      x∉Γ₂ : x ∉ dom Γ₂
      x∉Γ₂ = ∉-++ˡ r₅
      r₆ = ∉-++ʳ (dom Γ₂) r₅
      r₇ = ∉-++ʳ (fv u) r₆
      x∉u₁ : x ∉ fv u₁
      x∉u₁ = ∉-++ˡ r₇
      x∉u₂ : x ∉ fv u₂
      x∉u₂ = ∉-++ʳ (fv u₁) r₇

      pvx : ((x , eqv , v) ∷ Γ₀) ∣ s₀ prevalid
      pvx = ⟶ᵉ-prevalid (G₂ x∉L₂)
      pv₀ : Γ₀ ∣ s₀ prevalid
      pv₀ = ⟶ᵉ′-prevalid (F₁ x∉L₁)
      fvv : fv v ⊑ dom Γ₀
      fvv = head-fv (prevalid-ctx pvx)

      F₁ʷ : ((x , eqv , v) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x)
      F₁ʷ = ⟶ᵉ′-weaken [] ((x , eqv , v) ∷ []) pvx (F₁ x∉L₁)

      jp = ih lv p₁ p₂ sp (↣′-empty c₁) (↣-empty c₂) (sizedEmpty c₂ sc)
              (≤-trans (Ψ-arg {u = lam t u} {v = v} c₂ sc (m≤n+m n₂ (suc (n₀ + n₁)))) bd)
      v₃ = proj₁ jp
      jb = ih (F₀ x∉L₀) F₁ʷ (G₂ x∉L₂) (sG x∉L₂)
              (Ct-Ann′ {x = x} {c = eqv} c₁ p₁) (Ct-Ann {x = x} {c = eqv} c₂ p₂) (sc , n₂ , sp)
              (≤-trans (Ψ-app-bet-body {x = x} {t = t} {u = u} c₂ sc sp x∉Γ₀
                          (≤-trans (m≤n+m (n₁ + n₂) n₀ ⟨≤⟩ ≤-reflexive (sym (+-assoc n₀ n₁ n₂)))
                                   (n≤1+n (n₀ + n₁ + n₂)))) bd)
        where
          open import Data.Nat.Properties using (+-assoc; ≤-reflexive)
          _⟨≤⟩_ : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
          _⟨≤⟩_ = ≤-trans
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ-lc (⟶ᵉ′-lc (F₀ x∉L₀) F₁ʷ)
                  (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids* B (Me-App (Me-FOp {u = u} {u' = u₂} L₂ a₂ G₂) p₂) → Pieces* B c₂
            → (Γ₁ ∖ B) ∣ s₁ ⊢ (u₁ ^ v₁) ⟶ᵉ (b₃ ^ v₃)
      side₁ B cl av pc =
        ⟶ᵉ-subst≡-head {u = u₁} {u′ = b₃} x x∉u₁ (fv-close 0 x w₃) x∉s₁
                       (⟶ᵉ′-lc lv p₁) (⟶ᵉ-lc (⟶ᵉ′-lc lv p₁) h) fvv₁ g″ h
        where
          B″ = remove x B
          x∉B″ : x ∉ B″
          x∉B″ = ∉-remove {x} {B}
          v∉ : B ∉* fv v
          v∉ b∈ = proj₁ (proj₁ (av b∈))
          cl″ : Closed ((x , eqv , v) ∷ Γ₀) B″
          cl″ = closed-eqv (closed-remove x∉Γ₀ cl) (λ b∈ → v∉ (remove-⊑ {x} {B} b∈))
          av″ : Avoids* B″ (G₂ x∉L₂)
          av″ b∈ = proj₂ (proj₂ (proj₁ (av (remove-⊑ {x} {B} b∈)))) x∉L₂
                         (λ eq → x∉B″ (subst (_∈ B″) (sym eq) b∈))
          pc″ : Pieces* B″ (Ct-Ann {x = x} {c = eqv} c₂ p₂)
          pc″ b∈ = pc (remove-⊑ {x} {B} b∈) , proj₂ (av (remove-⊑ {x} {B} b∈))
          g : (((x , eqv , v₁) ∷ Γ₁) ∖ B″) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g = proj₁ (proj₂ jb) B″ cl″ av″ pc″
          g′ : ((x , eqv , v₁) ∷ (Γ₁ ∖ B)) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ w₃
          g′ rewrite sym (∖-remove Γ₁ {B} x∉Γ₁) | sym (∖-∉ {Γ₁} {B″} {x} {eqv} {v₁} x∉B″) = g
          g″ : ((x , eqv , v₁) ∷ (Γ₁ ∖ B)) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ (b₃ ^ fvar x)
          g″ rewrite open-close lw₃ 0 x = g′
          h : (Γ₁ ∖ B) ∣ [] ⊢ v₁ ⟶ᵉ v₃
          h = proj₁ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty c₂ (pc b∈))
          x∉s₁ : x ∉ fvStack s₁
          x∉s₁ = ∉-stack (↣′-prevalid pv₀ c₁) x∉Γ₁
          fvv₁ : fv v₁ ⊑ dom (Γ₁ ∖ B)
          fvv₁ {y} h′ = ∈-dom-∖ Γ₁ (λ y∈B → fv-closed′ cl (λ _ ()) v∉ p₁ y∈B h′)
                                  (fv-⟶ᵉ′ (λ q → subst (_ ∈_) (↣′-dom c₁) q) p₁
                                           (λ q → subst (_ ∈_) (↣′-dom c₁) (fvv q)) h′)

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Bet′ {t = t} {u = u} {u' = u₁} L₁ F₁ p₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ s₂ ⊢ app (lam t₂ u₂) v₂ ⟶ᵉ (b₃ ^ v₃)
      side₂ B cl av pc =
        Me-Bet {t = t₂} {u = u₂} {u' = b₃} A
               (λ {y} y∉ → close-rename₀ {u = u₂} x y (∉-dom-∖ Γ₂ x∉Γ₂) x∉u₂ lw₃ g′) h
        where
          cl′ : Closed ((x , eqv , v) ∷ Γ₀) (x ∷ B)
          cl′ = closed-add (prevalid-ctx pv₀) x∉Γ₀ cl
          av′ : Avoids*′ (x ∷ B) F₁ʷ
          av′ (here refl) = avoids-weaken′ [] _ pvx (F₁ x∉L₁) (unbound-avoids′ x x∉Γ₀ (F₁ x∉L₁))
          av′ (there b∈)  = avoids-weaken′ [] _ pvx (F₁ x∉L₁) (proj₁ (av b∈) x∉L₁)
          pc′ : Pieces*′ (x ∷ B) (Ct-Ann′ {x = x} {c = eqv} c₁ p₁)
          pc′ (here refl) = unbound-pieces′ x x∉Γ₀ c₁ , unbound-avoids′ x x∉Γ₀ p₁
          pc′ (there b∈)  = pc b∈ , proj₂ (av b∈)
          g : (((x , eqv , v₂) ∷ Γ₂) ∖ (x ∷ B)) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g = proj₂ (proj₂ jb) (x ∷ B) cl′ av′ pc′
          g′ : (Γ₂ ∖ B) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃
          g′ = subst (λ Γ → Γ ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ w₃)
                     (trans (∖-∈ {Γ₂} {x ∷ B} {x} {eqv} {v₂} (here refl)) (∖-∉dom Γ₂ x∉Γ₂)) g
          h : (Γ₂ ∖ B) ∣ [] ⊢ v₂ ⟶ᵉ v₃
          h = proj₂ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈))
```

## One unfolding, and the induction

```agda
  step : IH (suc k)
  step lc (Me-Var′ pv) (Me-Var pv′) sd c₁ c₂ sc (s≤s bd) = var-var pv pv′ c₁ c₂
  step lc (Me-Var′ pv) (Me-Pro pv′ m e) (n , se , refl) c₁ c₂ sc (s≤s bd) =
    var-pro pv pv′ m e se c₁ c₂ sc bd
  step lc (Me-Pro′ pv m e′) (Me-Var pv′) refl c₁ c₂ sc (s≤s bd) = pro-var pv pv′ m e′ c₁ c₂ sc bd
  step lc (Me-Pro′ pv m e′) (Me-Pro pv′ m′ e) (n , se , refl) c₁ c₂ sc (s≤s bd) =
    pro-pro pv pv′ m m′ e′ e se c₁ c₂ sc bd
  step lc (Me-Top′ pv) (Me-Top pv′) sd c₁ c₂ sc (s≤s bd) = top-top pv pv′ c₁ c₂
  step lc (Me-TAp′ {u = u} pv) (Me-TAp pv′) sd c₁ c₂ sc (s≤s bd) = tap-tap {u = u} pv pv′ c₁ c₂
  step lc (Me-TAp′ pv) (Me-App (Me-Top pv′) e) sd c₁ c₂ sc (s≤s bd) = tap-app pv pv′ e c₁ c₂
  step lc (Me-App′ (Me-Top′ pv′) e) (Me-TAp pv) sd c₁ c₂ sc (s≤s bd) = app-tap pv pv′ e c₁ c₂
  step (lc-app lu lv) (Me-App′ o₁ p₁) (Me-App o₂ p₂) (n₁ , n₂ , so , sp , refl) c₁ c₂ sc (s≤s bd) =
    app-app lu lv o₁ p₁ o₂ p₂ so sp c₁ c₂ sc bd
  step (lc-app (lc-lam L₀ lt F₀) lv)
       (Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁) (Me-Bet {u' = u₂} L₂ F₂ p₂)
       (n₁ , n₂ , sF , sp , refl) c₁ c₂ sc (s≤s bd) =
    app-bet {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ lv L₁ a₁ G₁ p₁ L₂ F₂ p₂ sF sp c₁ c₂ sc bd
  step (lc-app (lc-lam L₀ lt F₀) lv)
       (Me-Bet′ {u = u} {u' = u₁} L₁ F₁ p₁) (Me-App (Me-FOp {u' = u₂} L₂ a₂ G₂) p₂)
       (n₀₁ , n₂ , (n₀ , n₁ , sa , sG , refl) , sp , refl) c₁ c₂ sc (s≤s bd) =
    bet-app {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ lv L₁ F₁ p₁ L₂ a₂ G₂ p₂ sa sG sp c₁ c₂ sc bd
  step (lc-app (lc-lam L₀ lt F₀) lv)
       (Me-Bet′ {u = u} {u' = u₁} L₁ F₁ p₁) (Me-Bet {u' = u₂} L₂ F₂ p₂)
       (n₁ , n₂ , sF , sp , refl) c₁ c₂ sc (s≤s bd) =
    bet-bet {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ lv L₁ F₁ p₁ L₂ F₂ p₂ sF sp c₁ c₂ sc bd
  step (lc-lam L₀ lt F₀) (Me-Fun′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-Fun {u' = u₂} L₂ a₂ F₂)
       (n₁ , n₂ , sa , sF , refl) c₁ c₂ sc (s≤s bd)
    with ↣′-nil c₁ | ↣-nil c₂
  ... | refl | refl = fun-fun {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ sa sF c₁ c₂ sc bd
  step (lc-lam L₀ lt F₀) (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-FOp {u' = u₂} L₂ a₂ F₂)
       (n₁ , n₂ , sa , sF , refl) c₁ c₂ sc (s≤s bd) =
    fop-fop {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ sa sF c₁ c₂ sc bd
```

```agda
diamond : ∀ k → IH k
diamond zero    lc v d sd c₁ c₂ sc ()
diamond (suc k) = step k (diamond k)
```

## The mixed diamond

The invariant at every configuration, for a uniformly sized original side; then the plain
statement, for any original derivation and any context reduction, by uniformizing first.

```agda
join : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂ n} → LC t₀
     → (v : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁) (d : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂) → Sized d n
     → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂) (sc : SizedCtx c₂)
     → Join v d c₁ c₂
join {t₀ = t₀} {n = n} lc v d sd c₁ c₂ sc =
  diamond (suc (Ψ c₂ sc n t₀)) lc v d sd c₁ c₂ sc (s≤s ≤-refl)

Lem-2ᵐ : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂} → LC t₀
       → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁ → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂
       → Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
       → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ t₁ ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ t₂ ⟶ᵉ t₃))
Lem-2ᵐ {Γ₁ = Γ₁} {Γ₂ = Γ₂} lc v d c₁ c₂
  with uniform lc d | uniformCtx (prevalid-ctx (⟶ᵉ-prevalid d)) (stack-lc (⟶ᵉ-prevalid d)) c₂
... | d′ , n , sd | c₂′ , sc with join lc v d′ sd c₁ c₂′ sc
...   | t₃ , f₁ , f₂ =
  t₃ , subst (λ Γ → Γ ∣ _ ⊢ _ ⟶ᵉ t₃) (∖-[] Γ₁) (f₁ [] (λ _ ()) (λ ()) (λ ()))
     , subst (λ Γ → Γ ∣ _ ⊢ _ ⟶ᵉ t₃) (∖-[] Γ₂) (f₂ [] (λ _ ()) (λ ()) (λ ()))
```

## What this establishes

`Lem-2ᵐ`: **an original one-step equivalence reduction and a variant one-step equivalence
reduction from the same subject, at any two reduced configurations, are joined by one original
step each.** Nothing is assumed. The induction is strong induction on `MPSS/MixedMeasure`'s `Ψ`,
the size of the original derivation plus the sizes of the live pieces of the original side's
context reduction; every recursive call of every case is at a strictly smaller `Ψ`.

The one-step diamond for two original steps (`MPSS/Assumed`'s `Lem-2`) is the same statement
with the variant edge replaced by an original one. What separates the two is exactly the case
`pro-var`: with the variant premise at the empty stack the recursive call discards the stack
and the pieces it reaches; with an original premise it would not, and `MPSS/NoMeasure` and
`../PLAN.md` record why no measure survives that.
