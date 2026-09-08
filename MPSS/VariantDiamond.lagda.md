# MPSS: the diamond for the variant, proved

`MPSS/DiamondStep`'s case analysis for the variant relation `⟶ᵉ′` (`MPSS/EmptyStackPro`), with the
induction it lacked for the original: strong induction on the measure `Φ` of the shared
configuration (`MPSS/VariantMeasure`). The one substantive change is at `Me-Var′` against
`Me-Pro′`, and at `Me-Pro′` against `Me-Pro′`: the promotion's premise is at the empty stack, so
the copied piece is not pushed under anything, the recursive call is at the empty stack, and the
side that promoted reaches the join by promoting again at the reduced context with the recursive
join as its premise. Every other case is the original's with primes.

The statement carries the invariant `MPSS/DiamondStep` found necessary — the join is derivable
with any closed set of names removed that the other edge and the other context reduction avoid —
and the diamond of the paper's shape is the invariant at the empty set.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantDiamond where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_; ≤-trans)
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
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas
open import MPSS.VariantPush using (pushᵉ′)
open import MPSS.VariantCtx
open import MPSS.VariantAvoids
open import MPSS.VariantSubstEqv using (⟶ᵉ′-subst≡-head; ⟶ᵉ′-open₀; close-rename₀′)
open import MPSS.VariantMeasure
open import MPSS.Closed
open import MPSS.Drop
open import MPSS.DiamondStep using (remove; remove-⊑; ∉-remove; ∈-remove; ∖-remove; closed-remove; head-∉′; ≐-unique)
open import MPSS.Subst.Base using (∉-stack)
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; subst-intro; closeRec)
open import PSS.Close using (open-close; fv-close)
```

## Pieces of a context reduction

```agda
Pieces′ : Name → ∀ {Γ s Γ' s'} → Γ ∣ s ↣′ Γ' ∣ s' → Set
Pieces′ b (Ct-Refl′ {Γ})   = b ∉ dom Γ
Pieces′ b (Ct-Ann′ c d)    = Pieces′ b c × Avoids′ b d
Pieces′ b (Ct-Stk′ c d)    = Pieces′ b c × Avoids′ b d

Pieces*′ : List Name → ∀ {Γ s Γ' s'} → Γ ∣ s ↣′ Γ' ∣ s' → Set
Pieces*′ B c = ∀ {b} → b ∈ B → Pieces′ b c

unbound-pieces′ : ∀ {Γ s Γ' s'} x → x ∉ dom Γ → (c : Γ ∣ s ↣′ Γ' ∣ s') → Pieces′ x c
unbound-pieces′ x x∉ Ct-Refl′      = x∉
unbound-pieces′ x x∉ (Ct-Ann′ c d) =
  unbound-pieces′ x (λ h → x∉ (there h)) c , unbound-avoids′ x (λ h → x∉ (there h)) d
unbound-pieces′ x x∉ (Ct-Stk′ c d) = unbound-pieces′ x x∉ c , unbound-avoids′ x x∉ d

pieces-empty′ : ∀ {b Γ s Γ' s'} (c : Γ ∣ s ↣′ Γ' ∣ s') → Pieces′ b c → Pieces′ b (↣′-empty c)
pieces-empty′ Ct-Refl′      pc = pc
pieces-empty′ (Ct-Ann′ c d) (pc , av) = pieces-empty′ c pc , av
pieces-empty′ (Ct-Stk′ c d) (pc , _)  = pieces-empty′ c pc

avoids-eqv′ : ∀ {b Γ s Γ' s' x α} (pv : Γ prevalid) (c : Γ ∣ s ↣′ Γ' ∣ s') (m : x ≐ α ∈ Γ)
            → Pieces′ b c → Avoids′ b (proj₂ (proj₂ (↣′-eqv pv c m)))
avoids-eqv′ pv Ct-Refl′ m b∉ =
  avoids-refl′ _ _ _ (λ ()) (λ h → b∉ (prevalid-bound-fv pv m h))
avoids-eqv′ pv (Ct-Stk′ c _) m (pc , _) = avoids-eqv′ pv c m pc
avoids-eqv′ pv (Ct-Ann′ c e) (here refl) (pc , av) = avoids-weaken′ [] _ _ e av
avoids-eqv′ pv (Ct-Ann′ c e) (there m) (pc , av)
  with ↣′-eqv (tail-prevalid pv) c m | avoids-eqv′ (tail-prevalid pv) c m pc
... | α' , m' , e' | av' = avoids-weaken′ [] _ _ e' av'
```

## Popping the stack head off a context reduction

```agda
data Popped′ (Γ : Ctx) (α : Tm) : Tm → Set where
  same′  : Popped′ Γ α α
  piece′ : ∀ {α'} (Δ Γₜ : Ctx) → Γ ≡ Δ ++ Γₜ → Γₜ ∣ [] ⊢ α ⟶ᵉ′ α' → Popped′ Γ α α'

↣′-pop : ∀ {Γ s Γ' s' α} → Γ ∣ (α ∷ s) ↣′ Γ' ∣ s'
       → ∃[ α' ] ∃[ s'' ] ((s' ≡ α' ∷ s'') × (Γ ∣ s ↣′ Γ' ∣ s'') × Popped′ Γ α α')
↣′-pop Ct-Refl′      = _ , _ , refl , Ct-Refl′ , same′
↣′-pop (Ct-Stk′ c e) = _ , _ , refl , c , piece′ [] _ refl e
↣′-pop (Ct-Ann′ {x = y} {c = k} {t = t₀} c e) with ↣′-pop c
... | α' , s'' , refl , c′ , same′                 = α' , s'' , refl , Ct-Ann′ c′ e , same′
... | α' , s'' , refl , c′ , piece′ Δ Γₜ refl e′   =
  α' , s'' , refl , Ct-Ann′ c′ e , piece′ ((y , k , t₀) ∷ Δ) Γₜ refl e′

pop-piece′ : ∀ {Γ α α'} → Γ ∣ [] prevalid → LC α → fv α ⊑ dom Γ
           → Popped′ Γ α α' → Γ ∣ [] ⊢ α ⟶ᵉ′ α'
pop-piece′ pv lα f same′                     = ⟶ᵉ′-refl pv lα f
pop-piece′ pv lα f (piece′ Δ Γₜ refl e)      = ⟶ᵉ′-weaken [] Δ pv e

PoppedAvoids′ : Name → ∀ {Γ α α'} → Popped′ Γ α α' → Set
PoppedAvoids′ b same′               = ⊤
PoppedAvoids′ b (piece′ Δ Γₜ eq e)  = Avoids′ b e

pieces-pop′ : ∀ {b Γ s Γ' s' α} (c : Γ ∣ (α ∷ s) ↣′ Γ' ∣ s') → Pieces′ b c
            → Pieces′ b (proj₁ (proj₂ (proj₂ (proj₂ (↣′-pop c)))))
              × PoppedAvoids′ b (proj₂ (proj₂ (proj₂ (proj₂ (↣′-pop c)))))
pieces-pop′ Ct-Refl′      pc        = pc , tt
pieces-pop′ (Ct-Stk′ c e) (pc , av) = pc , av
pieces-pop′ (Ct-Ann′ c e) (pc , av) with ↣′-pop c | pieces-pop′ c pc
... | α' , s'' , refl , c′ , same′               | pc′ , _   = (pc′ , av) , tt
... | α' , s'' , refl , c′ , piece′ Δ Γₜ refl e′ | pc′ , av′ = (pc′ , av) , av′

avoids-pop′ : ∀ {b Γ α α'} (pv : Γ ∣ [] prevalid) (lα : LC α) (f : fv α ⊑ dom Γ)
            → (p : Popped′ Γ α α') → PoppedAvoids′ b p → b ∉ fv α
            → Avoids′ b (pop-piece′ pv lα f p)
avoids-pop′ pv lα f same′                _  b∉α = avoids-refl′ pv lα f (λ ()) b∉α
avoids-pop′ pv lα f (piece′ Δ Γₜ refl e) av b∉α = avoids-weaken′ [] Δ pv e av
```

## Closure along a context reduction

```agda
↣′-closed : ∀ {Γ s Γ' s' B} → Closed Γ B → Γ ∣ s ↣′ Γ' ∣ s' → Closed Γ' B
↣′-closed cl Ct-Refl′      = cl
↣′-closed cl (Ct-Stk′ c e) = ↣′-closed cl c
↣′-closed {B = B} cl (Ct-Ann′ {x = y} {t = t} {t' = t'} c e) {b = b} (there m) b∈ h =
  ↣′-closed (closed-tail cl) c m b∈ h
↣′-closed {B = B} cl (Ct-Ann′ {x = y} {t = t} {t' = t'} c e) {b = b} (here refl) b∈ h with y ∈? B
... | yes p = p
... | no  q = ⊥-elim (fv-closed′ (closed-tail cl) (λ _ ()) t∉ e b∈ h)
  where
    t∉ : B ∉* fv t
    t∉ b′∈ h′ = q (cl (here refl) b′∈ h′)
```

## The statement

```agda
Join′ : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂}
      → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁ → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₂
      → Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂ → Set
Join′ {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t₀} {t₁} {t₂} d₁ d₂ c₁ c₂ =
  ∃[ t₃ ] ((∀ B → Closed Γ₀ B → Avoids*′ B d₂ → Pieces*′ B c₂ → (Γ₁ ∖ B) ∣ s₁ ⊢ t₁ ⟶ᵉ′ t₃)
         × (∀ B → Closed Γ₀ B → Avoids*′ B d₁ → Pieces*′ B c₁ → (Γ₂ ∖ B) ∣ s₂ ⊢ t₂ ⟶ᵉ′ t₃))

-- the induction hypothesis: the statement for every configuration of measure below n
IH : ℕ → Set
IH n = ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂}
     → Φ Γ₀ s₀ t₀ < n → LC t₀
     → (d₁ : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁) (d₂ : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₂)
     → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
     → Join′ d₁ d₂ c₁ c₂

swap′ : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂}
      → {d₁ : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁} {d₂ : Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₂}
        {c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁} {c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂}
      → Join′ d₂ d₁ c₂ c₁ → Join′ d₁ d₂ c₁ c₂
swap′ (t₃ , f₂ , f₁) = t₃ , f₁ , f₂
```

## The cases

Each case takes the hypothesis for smaller measures and a bound `Φ Γ₀ s₀ t₀ ≤ n` on its own.

```agda
module _ (n : ℕ) (ih : IH n) where
```

### Leaves

```agda
  var-var : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Join′ (Me-Var′ {x = x} pv) (Me-Var′ pv′) c₁ c₂
  var-var {x = x} pv pv′ c₁ c₂ =
    _ , (λ B cl av pc → Me-Var′ (prevalid-∖-ext (↣′-closed cl c₁)
                                  (↣′-stack-closed cl (stack-free′ (Me-Var′ {x = x} pv′) av) c₁)
                                  (↣′-prevalid pv c₁)))
      , (λ B cl av pc → Me-Var′ (prevalid-∖-ext (↣′-closed cl c₂)
                                  (↣′-stack-closed cl (stack-free′ (Me-Var′ {x = x} pv) av) c₂)
                                  (↣′-prevalid pv c₂)))

  top-top : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Join′ (Me-Top′ pv) (Me-Top′ pv′) c₁ c₂
  top-top pv pv′ c₁ c₂ =
    Top , (λ B cl av pc → Me-Top′ (prevalid-∖-ext (↣′-closed cl c₁)
                                    (↣′-stack-closed cl (stack-free′ (Me-Top′ pv′) av) c₁)
                                    (↣′-prevalid pv c₁)))
        , (λ B cl av pc → Me-Top′ (prevalid-∖-ext (↣′-closed cl c₂)
                                    (↣′-stack-closed cl (stack-free′ (Me-Top′ pv) av) c₂)
                                    (↣′-prevalid pv c₂)))

  tap-tap : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Join′ (Me-TAp′ {u = u} pv) (Me-TAp′ pv′) c₁ c₂
  tap-tap {u = u} pv pv′ c₁ c₂ =
    Top , (λ B cl av pc → Me-Top′ (prevalid-∖-ext (↣′-closed cl c₁)
                                    (↣′-stack-closed cl (stack-free′ (Me-TAp′ {u = u} pv′) av) c₁)
                                    (↣′-prevalid pv c₁)))
        , (λ B cl av pc → Me-Top′ (prevalid-∖-ext (↣′-closed cl c₂)
                                    (↣′-stack-closed cl (stack-free′ (Me-TAp′ {u = u} pv) av) c₂)
                                    (↣′-prevalid pv c₂)))

  tap-app : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u u'} (pv : Γ₀ ∣ s₀ prevalid)
            (pv′ : Γ₀ ∣ (u ∷ s₀) prevalid) (e : Γ₀ ∣ [] ⊢ u ⟶ᵉ′ u')
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Join′ (Me-TAp′ pv) (Me-App′ (Me-Top′ pv′) e) c₁ c₂
  tap-app {u = u} pv pv′ e c₁ c₂ =
    Top , (λ B cl av pc → Me-Top′ (prevalid-∖-ext (↣′-closed cl c₁)
                                    (↣′-stack-closed cl (∉*-++ʳ (fv u) (stack-free′ (Me-Top′ pv′) (λ b∈ → proj₁ (av b∈)))) c₁)
                                    (↣′-prevalid pv c₁)))
        , (λ B cl av pc → Me-TAp′ (prevalid-∖-ext (↣′-closed cl c₂)
                                    (↣′-stack-closed cl (stack-free′ (Me-TAp′ {u = u} pv) av) c₂)
                                    (↣′-prevalid pv c₂)))
```

### The variable cases

Both premises are at the empty stack, so the recursive call is too; each side's join is pushed
back under its own reduced stack.

```agda
  pro-pro : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x α α′ α₁ α₂} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (m : x ≐ α ∈ Γ₀) (m′ : x ≐ α′ ∈ Γ₀)
            (e₁ : Γ₀ ∣ [] ⊢ α ⟶ᵉ′ α₁) (e₂ : Γ₀ ∣ [] ⊢ α′ ⟶ᵉ′ α₂)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Φ Γ₀ s₀ (fvar x) ≤ n
          → Join′ (Me-Pro′ pv m e₁) (Me-Pro′ pv′ m′ e₂) c₁ c₂
  pro-pro {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {x} {α} pv pv′ m m′ e₁ e₂ c₁ c₂ bd
    with ≐-unique (prevalid-ctx pv) m m′
  ... | refl with ih (≤-trans (Φ-pull {s = s₀} (prevalid-ctx pv) m) bd)
                     (prevalid-bound-lc (prevalid-ctx pv) m) e₁ e₂ (↣′-empty c₁) (↣′-empty c₂)
  ...   | t₃ , f₁ , f₂ =
    t₃ , (λ B cl av pc →
            pushᵉ′ {s = []} {s′ = s₁}
                   (f₁ B cl (λ b∈ → proj₂ (proj₂ (av b∈))) (λ b∈ → pieces-empty′ c₂ (pc b∈)))
                   (prevalid-∖-ext (↣′-closed cl c₁)
                                   (↣′-stack-closed cl (stack-free′ (Me-Pro′ pv′ m e₂) av) c₁)
                                   (↣′-prevalid pv c₁)))
       , (λ B cl av pc →
            pushᵉ′ {s = []} {s′ = s₂}
                   (f₂ B cl (λ b∈ → proj₂ (proj₂ (av b∈))) (λ b∈ → pieces-empty′ c₁ (pc b∈)))
                   (prevalid-∖-ext (↣′-closed cl c₂)
                                   (↣′-stack-closed cl (stack-free′ (Me-Pro′ pv m e₁) av) c₂)
                                   (↣′-prevalid pv c₂)))
```

`Me-Var′` against `Me-Pro′`: the piece copied out of `c₁` is at the empty stack, as is the
promotion's premise; the recursive call joins them there. The first side promotes `x` at
`Γ₁ ∖ B` with the recursive join as its premise; the second side's join is pushed under `s₂`.

```agda
  var-pro : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ x α α₁} (pv pv′ : Γ₀ ∣ s₀ prevalid)
            (m : x ≐ α ∈ Γ₀) (e : Γ₀ ∣ [] ⊢ α ⟶ᵉ′ α₁)
            (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Φ Γ₀ s₀ (fvar x) ≤ n
          → Join′ (Me-Var′ {x = x} pv) (Me-Pro′ pv′ m e) c₁ c₂
  var-pro {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {x} {α} pv pv′ m e c₁ c₂ bd
    with ↣′-eqv (prevalid-ctx pv) c₁ m | avoids-eqv″
    where
      avoids-eqv″ : ∀ {b} → Pieces′ b c₁ → Avoids′ b (proj₂ (proj₂ (↣′-eqv (prevalid-ctx pv) c₁ m)))
      avoids-eqv″ = avoids-eqv′ (prevalid-ctx pv) c₁ m
  ... | α′ , m′ , e′ | av-e′
    with ih (≤-trans (Φ-pull {s = s₀} (prevalid-ctx pv) m) bd)
            (prevalid-bound-lc (prevalid-ctx pv) m) e′ e (↣′-empty c₁) (↣′-empty c₂)
  ...   | t₃ , f₁ , f₂ =
    t₃ , (λ B cl av pc →
            Me-Pro′ (prevalid-∖-ext (↣′-closed cl c₁)
                                    (↣′-stack-closed cl (stack-free′ (Me-Pro′ pv′ m e) av) c₁)
                                    (↣′-prevalid pv c₁))
                    (∈-∖ (λ x∈B → proj₁ (av x∈B) refl) m′)
                    (f₁ B cl (λ b∈ → proj₂ (proj₂ (av b∈))) (λ b∈ → pieces-empty′ c₂ (pc b∈))))
       , (λ B cl av pc →
            pushᵉ′ {s = []} {s′ = s₂}
                   (f₂ B cl (λ b∈ → av-e′ (pc b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈)))
                   (prevalid-∖-ext (↣′-closed cl c₂)
                                   (↣′-stack-closed cl (stack-free′ (Me-Var′ {x = x} pv) av) c₂)
                                   (↣′-prevalid pv c₂)))
```

### Application

```agda
  app-app : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ u v u₁ v₁ u₂ v₂} → LC u → LC v
          → (o₁ : Γ₀ ∣ (v ∷ s₀) ⊢ u ⟶ᵉ′ u₁) (p₁ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₁)
          → (o₂ : Γ₀ ∣ (v ∷ s₀) ⊢ u ⟶ᵉ′ u₂) (p₂ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₂)
          → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Φ Γ₀ s₀ (app u v) ≤ n
          → Join′ (Me-App′ o₁ p₁) (Me-App′ o₂ p₂) c₁ c₂
  app-app {Γ₀} {s₀} {u = u} {v = v} lu lv o₁ p₁ o₂ p₂ c₁ c₂ bd
    with ih (≤-trans (Φ-app-op Γ₀ s₀ u v) bd) lu o₁ o₂ (Ct-Stk′ c₁ p₁) (Ct-Stk′ c₂ p₂)
       | ih (≤-trans (Φ-app-arg Γ₀ s₀ u v) bd) lv p₁ p₂ (↣′-empty c₁) (↣′-empty c₂)
  ... | u₃ , g₁ , g₂ | v₃ , h₁ , h₂ =
    app u₃ v₃
    , (λ B cl av pc → Me-App′ (g₁ B cl (λ b∈ → proj₁ (av b∈)) (λ b∈ → pc b∈ , proj₂ (av b∈)))
                              (h₁ B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₂ (pc b∈))))
    , (λ B cl av pc → Me-App′ (g₂ B cl (λ b∈ → proj₁ (av b∈)) (λ b∈ → pc b∈ , proj₂ (av b∈)))
                              (h₂ B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈))))
```

### Abstraction against abstraction, at the empty stack

```agda
  fun-fun : ∀ {Γ₀ Γ₁ Γ₂ t u t₁ u₁ t₂ u₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x))
          → (L₁ : List Name) (a₁ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₁)
            (F₁ : ∀ {x} → x ∉ L₁ → ((x , sub , t) ∷ Γ₀) ∣ [] ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
          → (L₂ : List Name) (a₂ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₂)
            (F₂ : ∀ {x} → x ∉ L₂ → ((x , sub , t) ∷ Γ₀) ∣ [] ⊢ (u ^ fvar x) ⟶ᵉ′ (u₂ ^ fvar x))
          → (c₁ : Γ₀ ∣ [] ↣′ Γ₁ ∣ []) (c₂ : Γ₀ ∣ [] ↣′ Γ₂ ∣ [])
          → Φ Γ₀ [] (lam t u) ≤ n
          → Join′ (Me-Fun′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-Fun′ {u = u} {u' = u₂} L₂ a₂ F₂) c₁ c₂
  fun-fun {Γ₀} {Γ₁} {Γ₂} {t} {u} {t₁} {u₁} {t₂} {u₂} L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ c₁ c₂ bd =
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

      ja = ih (≤-trans (Φ-ann Γ₀ [] t u) bd) lt a₁ a₂ c₁ c₂
      t₃ = proj₁ ja
      jb = ih (≤-trans (Φ-fun-body Γ₀ x t u x∉Γ₀) bd) (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)
              (Ct-Ann′ c₁ a₁) (Ct-Ann′ c₂ a₂)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ′-lc (⟶ᵉ′-lc (F₀ x∉L₀) (F₁ x∉L₁))
                   (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Fun′ {u = u} {u' = u₂} L₂ a₂ F₂) → Pieces*′ B c₂
            → (Γ₁ ∖ B) ∣ [] ⊢ lam t₁ u₁ ⟶ᵉ′ lam t₃ b₃
      side₁ B cl av pc = Me-Fun′ A (proj₁ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈))) pc) body
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , sub , t) ∷ Γ₀) B′
          cl′ = closed-sub (closed-remove x∉Γ₀ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids*′ B′ (F₂ x∉L₂)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₂
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces*′ B′ (Ct-Ann′ {x = x} {c = sub} c₂ a₂)
          pc′ b∈ = pc (remove-⊑ {x} {B} b∈) , proj₁ (proj₂ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , sub , t₁) ∷ Γ₁) ∖ B′) ∣ [] ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₁ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , sub , t₁) ∷ (Γ₁ ∖ B)) ∣ [] ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃
          g′ rewrite sym (∖-remove Γ₁ {B} x∉Γ₁) | sym (∖-∉ {Γ₁} {B′} {x} {sub} {t₁} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , sub , t₁) ∷ (Γ₁ ∖ B)) ∣ [] ⊢ (u₁ ^ fvar y) ⟶ᵉ′ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ′-rename-head {b = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) (∉-dom-∖ Γ₁ y∉Γ₁) x∉t₁ x∉u₁ (λ ()) lw₃ g′
            where
              y∉Γ₁ : y ∉ dom Γ₁
              y∉Γ₁ = ∉-++ˡ (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉))))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Fun′ {u = u} {u' = u₁} L₁ a₁ F₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ [] ⊢ lam t₂ u₂ ⟶ᵉ′ lam t₃ b₃
      side₂ B cl av pc = Me-Fun′ A (proj₂ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈))) pc) body
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
          g : (((x , sub , t₂) ∷ Γ₂) ∖ B′) ∣ [] ⊢ (u₂ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₂ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , sub , t₂) ∷ (Γ₂ ∖ B)) ∣ [] ⊢ (u₂ ^ fvar x) ⟶ᵉ′ w₃
          g′ rewrite sym (∖-remove Γ₂ {B} x∉Γ₂) | sym (∖-∉ {Γ₂} {B′} {x} {sub} {t₂} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , sub , t₂) ∷ (Γ₂ ∖ B)) ∣ [] ⊢ (u₂ ^ fvar y) ⟶ᵉ′ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ′-rename-head {b = u₂} x y (∉-dom-∖ Γ₂ x∉Γ₂) (∉-dom-∖ Γ₂ y∉Γ₂) x∉t₂ x∉u₂ (λ ()) lw₃ g′
            where
              y∉Γ₂ : y ∉ dom Γ₂
              y∉Γ₂ = ∉-++ˡ (∉-++ʳ (dom Γ₁) (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉)))))
```

### Abstraction against abstraction, under a stack

```agda
  fop-fop : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ α t u t₁ u₁ t₂ u₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x))
          → (L₁ : List Name) (a₁ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₁)
            (F₁ : ∀ {x} → x ∉ L₁ → ((x , eqv , α) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
          → (L₂ : List Name) (a₂ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₂)
            (F₂ : ∀ {x} → x ∉ L₂ → ((x , eqv , α) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₂ ^ fvar x))
          → (c₁ : Γ₀ ∣ (α ∷ s₀) ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ (α ∷ s₀) ↣′ Γ₂ ∣ s₂)
          → Φ Γ₀ (α ∷ s₀) (lam t u) ≤ n
          → Join′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-FOp′ {u = u} {u' = u₂} L₂ a₂ F₂) c₁ c₂
  fop-fop {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {α} {t} {u} {t₁} {u₁} {t₂} {u₂}
          L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ c₁ c₂ bd =
    lam t₃ b₃ , side₁ , side₂
    where
      pv₀ : Γ₀ ∣ (α ∷ s₀) prevalid
      pv₀ = ⟶ᵉ′-prevalid (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ F₁)
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
      pop₂ = ↣′-pop c₂
      α₂   = proj₁ pop₂
      s₂′  = proj₁ (proj₂ pop₂)
      eq₂  = proj₁ (proj₂ (proj₂ pop₂))
      c₂′  = proj₁ (proj₂ (proj₂ (proj₂ pop₂)))
      pp₂  = proj₂ (proj₂ (proj₂ (proj₂ pop₂)))
      q₂   = pop-piece′ pvn lα fα pp₂

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

      ja = ih (≤-trans (Φ-ann Γ₀ (α ∷ s₀) t u) bd) lt a₁ a₂ (↣′-empty c₁) (↣′-empty c₂)
      t₃ = proj₁ ja
      jb = ih (≤-trans (Φ-fop-body Γ₀ s₀ α x t u x∉Γ₀) bd) (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)
              (Ct-Ann′ {x = x} {c = eqv} c₁′ q₁) (Ct-Ann′ {x = x} {c = eqv} c₂′ q₂)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ′-lc (⟶ᵉ′-lc (F₀ x∉L₀) (F₁ x∉L₁))
                   (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-FOp′ {u = u} {u' = u₂} L₂ a₂ F₂) → Pieces*′ B c₂
            → (Γ₁ ∖ B) ∣ s₁ ⊢ lam t₁ u₁ ⟶ᵉ′ lam t₃ b₃
      side₁ B cl av pc =
        subst (λ s → (Γ₁ ∖ B) ∣ s ⊢ lam t₁ u₁ ⟶ᵉ′ lam t₃ b₃) (sym eq₁)
              (Me-FOp′ A (proj₁ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈)))
                                              (λ b∈ → pieces-empty′ c₂ (pc b∈))) body)
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , eqv , α) ∷ Γ₀) B′
          cl′ = closed-eqv (closed-remove x∉Γ₀ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids*′ B′ (F₂ x∉L₂)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₂
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces*′ B′ (Ct-Ann′ {x = x} {c = eqv} c₂′ q₂)
          pc′ b∈ = proj₁ (pieces-pop′ c₂ (pc (remove-⊑ {x} {B} b∈)))
                 , avoids-pop′ pvn lα fα pp₂ (proj₂ (pieces-pop′ c₂ (pc (remove-⊑ {x} {B} b∈))))
                               (proj₁ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , eqv , α₁) ∷ Γ₁) ∖ B′) ∣ s₁′ ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₁ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , eqv , α₁) ∷ (Γ₁ ∖ B)) ∣ s₁′ ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃
          g′ rewrite sym (∖-remove Γ₁ {B} x∉Γ₁) | sym (∖-∉ {Γ₁} {B′} {x} {eqv} {α₁} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , eqv , α₁) ∷ (Γ₁ ∖ B)) ∣ s₁′ ⊢ (u₁ ^ fvar y) ⟶ᵉ′ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ′-rename-head {b = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) (∉-dom-∖ Γ₁ y∉Γ₁) x∉α₁ x∉u₁ x∉s₁ lw₃ g′
            where
              y∉Γ₁ : y ∉ dom Γ₁
              y∉Γ₁ = ∉-++ˡ (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉))))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ F₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ s₂ ⊢ lam t₂ u₂ ⟶ᵉ′ lam t₃ b₃
      side₂ B cl av pc =
        subst (λ s → (Γ₂ ∖ B) ∣ s ⊢ lam t₂ u₂ ⟶ᵉ′ lam t₃ b₃) (sym eq₂)
              (Me-FOp′ A (proj₂ (proj₂ ja) B cl (λ b∈ → proj₁ (proj₂ (av b∈)))
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
          g : (((x , eqv , α₂) ∷ Γ₂) ∖ B′) ∣ s₂′ ⊢ (u₂ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₂ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , eqv , α₂) ∷ (Γ₂ ∖ B)) ∣ s₂′ ⊢ (u₂ ^ fvar x) ⟶ᵉ′ w₃
          g′ rewrite sym (∖-remove Γ₂ {B} x∉Γ₂) | sym (∖-∉ {Γ₂} {B′} {x} {eqv} {α₂} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , eqv , α₂) ∷ (Γ₂ ∖ B)) ∣ s₂′ ⊢ (u₂ ^ fvar y) ⟶ᵉ′ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ′-rename-head {b = u₂} x y (∉-dom-∖ Γ₂ x∉Γ₂) (∉-dom-∖ Γ₂ y∉Γ₂) x∉α₂ x∉u₂ x∉s₂ lw₃ g′
            where
              y∉Γ₂ : y ∉ dom Γ₂
              y∉Γ₂ = ∉-++ˡ (∉-++ʳ (dom Γ₁) (∉-++ʳ (dom Γ₀) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉)))))
```

### Contraction against contraction

```agda
  bet-bet : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t u v u₁ v₁ u₂ v₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x)) → LC v
          → (L₁ : List Name) (F₁ : ∀ {x} → x ∉ L₁ → Γ₀ ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
            (p₁ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₁)
          → (L₂ : List Name) (F₂ : ∀ {x} → x ∉ L₂ → Γ₀ ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₂ ^ fvar x))
            (p₂ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₂)
          → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Φ Γ₀ s₀ (app (lam t u) v) ≤ n
          → Join′ (Me-Bet′ {t = t} {u = u} {u' = u₁} L₁ F₁ p₁) (Me-Bet′ {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) c₁ c₂
  bet-bet {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t} {u} {v} {u₁} {v₁} {u₂} {v₂}
          L₀ lt F₀ lv L₁ F₁ p₁ L₂ F₂ p₂ c₁ c₂ bd =
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

      jp = ih (≤-trans (Φ-bet-arg Γ₀ s₀ t u v) bd) lv p₁ p₂ (↣′-empty c₁) (↣′-empty c₂)
      v₃ = proj₁ jp
      jb = ih (≤-trans (Φ-bet-body Γ₀ s₀ x t u v x∉Γ₀) bd) (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂) c₁ c₂
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ′-lc (⟶ᵉ′-lc (F₀ x∉L₀) (F₁ x∉L₁))
                   (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Bet′ {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) → Pieces*′ B c₂
            → (Γ₁ ∖ B) ∣ s₁ ⊢ (u₁ ^ v₁) ⟶ᵉ′ (b₃ ^ v₃)
      side₁ B cl av pc =
        ⟶ᵉ′-open₀ {u = u₁} {u′ = b₃} A (⟶ᵉ′-lc lv p₁) (⟶ᵉ′-lc (⟶ᵉ′-lc lv p₁) h)
                  (λ {y} y∉ → close-rename₀′ {u = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) x∉u₁ lw₃ g) h
        where
          g : (Γ₁ ∖ B) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₁ (proj₂ jb) B cl (λ b∈ → proj₁ (av b∈) x∉L₂) pc
          h : (Γ₁ ∖ B) ∣ [] ⊢ v₁ ⟶ᵉ′ v₃
          h = proj₁ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₂ (pc b∈))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Bet′ {t = t} {u = u} {u' = u₁} L₁ F₁ p₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ s₂ ⊢ (u₂ ^ v₂) ⟶ᵉ′ (b₃ ^ v₃)
      side₂ B cl av pc =
        ⟶ᵉ′-open₀ {u = u₂} {u′ = b₃} A (⟶ᵉ′-lc lv p₂) (⟶ᵉ′-lc (⟶ᵉ′-lc lv p₂) h)
                  (λ {y} y∉ → close-rename₀′ {u = u₂} x y (∉-dom-∖ Γ₂ x∉Γ₂) x∉u₂ lw₃ g) h
        where
          g : (Γ₂ ∖ B) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₂ (proj₂ jb) B cl (λ b∈ → proj₁ (av b∈) x∉L₁) pc
          h : (Γ₂ ∖ B) ∣ [] ⊢ v₂ ⟶ᵉ′ v₃
          h = proj₂ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈))
```

### Application against contraction

```agda
  app-bet : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t u v t₁ u₁ v₁ u₂ v₂} (L₀ : List Name) → LC t
          → (F₀ : ∀ {x} → x ∉ L₀ → LC (u ^ fvar x)) → LC v
          → (L₁ : List Name) (a₁ : Γ₀ ∣ [] ⊢ t ⟶ᵉ′ t₁)
            (G₁ : ∀ {x} → x ∉ L₁ → ((x , eqv , v) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₁ ^ fvar x))
            (p₁ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₁)
          → (L₂ : List Name) (F₂ : ∀ {x} → x ∉ L₂ → Γ₀ ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₂ ^ fvar x))
            (p₂ : Γ₀ ∣ [] ⊢ v ⟶ᵉ′ v₂)
          → (c₁ : Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁) (c₂ : Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂)
          → Φ Γ₀ s₀ (app (lam t u) v) ≤ n
          → Join′ (Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁)
                  (Me-Bet′ {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) c₁ c₂
  app-bet {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t} {u} {v} {t₁} {u₁} {v₁} {u₂} {v₂}
          L₀ lt F₀ lv L₁ a₁ G₁ p₁ L₂ F₂ p₂ c₁ c₂ bd =
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
      pv₀ = ⟶ᵉ′-prevalid (F₂ x∉L₂)
      fvv : fv v ⊑ dom Γ₀
      fvv = head-fv (prevalid-ctx pvx)

      F₂ʷ : ((x , eqv , v) ∷ Γ₀) ∣ s₀ ⊢ (u ^ fvar x) ⟶ᵉ′ (u₂ ^ fvar x)
      F₂ʷ = ⟶ᵉ′-weaken [] ((x , eqv , v) ∷ []) pvx (F₂ x∉L₂)

      jp = ih (≤-trans (Φ-bet-arg Γ₀ s₀ t u v) bd) lv p₁ p₂ (↣′-empty c₁) (↣′-empty c₂)
      v₃ = proj₁ jp
      jb = ih (≤-trans (Φ-app-bet-body Γ₀ s₀ x t u v x∉Γ₀) bd) (F₀ x∉L₀) (G₁ x∉L₁) F₂ʷ
              (Ct-Ann′ {x = x} {c = eqv} c₁ p₁) (Ct-Ann′ {x = x} {c = eqv} c₂ p₂)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ′-lc (⟶ᵉ′-lc (F₀ x∉L₀) (G₁ x∉L₁))
                   (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-Bet′ {t = t} {u = u} {u' = u₂} L₂ F₂ p₂) → Pieces*′ B c₂
            → (Γ₁ ∖ B) ∣ s₁ ⊢ app (lam t₁ u₁) v₁ ⟶ᵉ′ (b₃ ^ v₃)
      side₁ B cl av pc =
        Me-Bet′ {t = t₁} {u = u₁} {u' = b₃} A
                (λ {y} y∉ → close-rename₀′ {u = u₁} x y (∉-dom-∖ Γ₁ x∉Γ₁) x∉u₁ lw₃ g′) h
        where
          cl′ : Closed ((x , eqv , v) ∷ Γ₀) (x ∷ B)
          cl′ = closed-add (prevalid-ctx pv₀) x∉Γ₀ cl
          av′ : Avoids*′ (x ∷ B) F₂ʷ
          av′ (here refl) = avoids-weaken′ [] _ pvx (F₂ x∉L₂) (unbound-avoids′ x x∉Γ₀ (F₂ x∉L₂))
          av′ (there b∈)  = avoids-weaken′ [] _ pvx (F₂ x∉L₂) (proj₁ (av b∈) x∉L₂)
          pc′ : Pieces*′ (x ∷ B) (Ct-Ann′ {x = x} {c = eqv} c₂ p₂)
          pc′ (here refl) = unbound-pieces′ x x∉Γ₀ c₂ , unbound-avoids′ x x∉Γ₀ p₂
          pc′ (there b∈)  = pc b∈ , proj₂ (av b∈)
          g : (((x , eqv , v₁) ∷ Γ₁) ∖ (x ∷ B)) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₁ (proj₂ jb) (x ∷ B) cl′ av′ pc′
          g′ : (Γ₁ ∖ B) ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃
          g′ = subst (λ Γ → Γ ∣ s₁ ⊢ (u₁ ^ fvar x) ⟶ᵉ′ w₃)
                     (trans (∖-∈ {Γ₁} {x ∷ B} {x} {eqv} {v₁} (here refl)) (∖-∉dom Γ₁ x∉Γ₁)) g
          h : (Γ₁ ∖ B) ∣ [] ⊢ v₁ ⟶ᵉ′ v₃
          h = proj₁ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₂ (pc b∈))

      side₂ : ∀ B → Closed Γ₀ B → Avoids*′ B (Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁) → Pieces*′ B c₁
            → (Γ₂ ∖ B) ∣ s₂ ⊢ (u₂ ^ v₂) ⟶ᵉ′ (b₃ ^ v₃)
      side₂ B cl av pc =
        ⟶ᵉ′-subst≡-head {u = u₂} {u′ = b₃} x x∉u₂ (fv-close 0 x w₃) x∉s₂
                        (⟶ᵉ′-lc lv p₂) (⟶ᵉ′-lc (⟶ᵉ′-lc lv p₂) h) fvv₂ g″ h
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
          g : (((x , eqv , v₂) ∷ Γ₂) ∖ B″) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₂ (proj₂ jb) B″ cl″ av″ pc″
          g′ : ((x , eqv , v₂) ∷ (Γ₂ ∖ B)) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ′ w₃
          g′ rewrite sym (∖-remove Γ₂ {B} x∉Γ₂) | sym (∖-∉ {Γ₂} {B″} {x} {eqv} {v₂} x∉B″) = g
          g″ : ((x , eqv , v₂) ∷ (Γ₂ ∖ B)) ∣ s₂ ⊢ (u₂ ^ fvar x) ⟶ᵉ′ (b₃ ^ fvar x)
          g″ rewrite open-close lw₃ 0 x = g′
          h : (Γ₂ ∖ B) ∣ [] ⊢ v₂ ⟶ᵉ′ v₃
          h = proj₂ (proj₂ jp) B cl (λ b∈ → proj₂ (av b∈)) (λ b∈ → pieces-empty′ c₁ (pc b∈))
          x∉s₂ : x ∉ fvStack s₂
          x∉s₂ = ∉-stack (↣′-prevalid pv₀ c₂) x∉Γ₂
          fvv₂ : fv v₂ ⊑ dom (Γ₂ ∖ B)
          fvv₂ {y} h′ = ∈-dom-∖ Γ₂ (λ y∈B → fv-closed′ cl (λ _ ()) v∉ p₂ y∈B h′)
                                   (fv-⟶ᵉ′ (λ q → subst (_ ∈_) (↣′-dom c₂) q) p₂
                                            (λ q → subst (_ ∈_) (↣′-dom c₂) (fvv q)) h′)
```

## One unfolding, and the induction

```agda
  step′ : IH (suc n)
  step′ (s≤s bd) lc (Me-Var′ pv) (Me-Var′ pv′) c₁ c₂ = var-var pv pv′ c₁ c₂
  step′ (s≤s bd) lc (Me-Var′ pv) (Me-Pro′ pv′ m e) c₁ c₂ = var-pro pv pv′ m e c₁ c₂ bd
  step′ (s≤s bd) lc (Me-Pro′ pv m e) (Me-Var′ pv′) c₁ c₂ =
    swap′ {d₁ = Me-Pro′ pv m e} {d₂ = Me-Var′ pv′} (var-pro pv′ pv m e c₂ c₁ bd)
  step′ (s≤s bd) lc (Me-Pro′ pv m e₁) (Me-Pro′ pv′ m′ e₂) c₁ c₂ = pro-pro pv pv′ m m′ e₁ e₂ c₁ c₂ bd
  step′ (s≤s bd) lc (Me-Top′ pv) (Me-Top′ pv′) c₁ c₂ = top-top pv pv′ c₁ c₂
  step′ (s≤s bd) lc (Me-TAp′ {u = u} pv) (Me-TAp′ pv′) c₁ c₂ = tap-tap {u = u} pv pv′ c₁ c₂
  step′ (s≤s bd) lc (Me-TAp′ pv) (Me-App′ (Me-Top′ pv′) e) c₁ c₂ = tap-app pv pv′ e c₁ c₂
  step′ (s≤s bd) lc (Me-App′ (Me-Top′ pv′) e) (Me-TAp′ pv) c₁ c₂ =
    swap′ {d₁ = Me-App′ (Me-Top′ pv′) e} {d₂ = Me-TAp′ pv} (tap-app pv pv′ e c₂ c₁)
  step′ (s≤s bd) (lc-app lu lv) (Me-App′ o₁ p₁) (Me-App′ o₂ p₂) c₁ c₂ = app-app lu lv o₁ p₁ o₂ p₂ c₁ c₂ bd
  step′ (s≤s bd) (lc-app (lc-lam L₀ lt F₀) lv)
        (Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁) (Me-Bet′ {u' = u₂} L₂ F₂ p₂) c₁ c₂ =
    app-bet {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ lv L₁ a₁ G₁ p₁ L₂ F₂ p₂ c₁ c₂ bd
  step′ (s≤s bd) (lc-app (lc-lam L₀ lt F₀) lv)
        (Me-Bet′ {u' = u₂} L₂ F₂ p₂) (Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁) c₁ c₂ =
    swap′ {d₁ = Me-Bet′ {u' = u₂} L₂ F₂ p₂} {d₂ = Me-App′ (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ G₁) p₁}
          (app-bet {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ lv L₁ a₁ G₁ p₁ L₂ F₂ p₂ c₂ c₁ bd)
  step′ (s≤s bd) (lc-app (lc-lam L₀ lt F₀) lv)
        (Me-Bet′ {u = u} {u' = u₁} L₁ F₁ p₁) (Me-Bet′ {u' = u₂} L₂ F₂ p₂) c₁ c₂ =
    bet-bet {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ lv L₁ F₁ p₁ L₂ F₂ p₂ c₁ c₂ bd
  step′ (s≤s bd) (lc-lam L₀ lt F₀) (Me-Fun′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-Fun′ {u' = u₂} L₂ a₂ F₂) c₁ c₂
    with ↣′-nil c₁ | ↣′-nil c₂
  ... | refl | refl = fun-fun {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ c₁ c₂ bd
  step′ (s≤s bd) (lc-lam L₀ lt F₀) (Me-FOp′ {u = u} {u' = u₁} L₁ a₁ F₁) (Me-FOp′ {u' = u₂} L₂ a₂ F₂) c₁ c₂ =
    fop-fop {u = u} {u₁ = u₁} {u₂ = u₂} L₀ lt F₀ L₁ a₁ F₁ L₂ a₂ F₂ c₁ c₂ bd
```

```agda
diamond′ : ∀ n → IH n
diamond′ zero    ()
diamond′ (suc n) = step′ n (diamond′ n)
```

## The diamond

The invariant at the empty set, for every configuration.

```agda
Lem-2′ : ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂} → LC t₀
       → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₁ → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ′ t₂
       → Γ₀ ∣ s₀ ↣′ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣′ Γ₂ ∣ s₂
       → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ t₁ ⟶ᵉ′ t₃) × (Γ₂ ∣ s₂ ⊢ t₂ ⟶ᵉ′ t₃))
Lem-2′ {Γ₀} {s₀} {Γ₁} {s₁} {Γ₂} {s₂} {t₀} lc d₁ d₂ c₁ c₂
  with diamond′ (suc (Φ Γ₀ s₀ t₀)) (s≤s (≤-refl′ (Φ Γ₀ s₀ t₀))) lc d₁ d₂ c₁ c₂
  where
    ≤-refl′ : ∀ m → m ≤ m
    ≤-refl′ zero    = z≤n
    ≤-refl′ (suc m) = s≤s (≤-refl′ m)
... | t₃ , f₁ , f₂ =
  t₃ , subst (λ Γ → Γ ∣ _ ⊢ _ ⟶ᵉ′ t₃) (∖-[] Γ₁) (f₁ [] (λ _ ()) (λ ()) (λ ()))
     , subst (λ Γ → Γ ∣ _ ⊢ _ ⟶ᵉ′ t₃) (∖-[] Γ₂) (f₂ [] (λ _ ()) (λ ()) (λ ()))
```

## What this establishes

`Lem-2′`: **the one-step diamond for the variant equivalence reduction**, with two arbitrary
context reductions, on locally closed subjects. The induction is strong induction on `Φ`, the
size of the shared configuration counting only the reachable part of the context; every recursive
call of every case is at a configuration of smaller measure (`MPSS/VariantMeasure`). Nothing is
assumed.
