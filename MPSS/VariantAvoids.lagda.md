# MPSS: avoiding a name, for the variant relation

`MPSS/Strengthen`'s `Avoids`, `MPSS/AvoidsPreserve`'s four preservation lemmas, and the parts of
`MPSS/Closed` the diamond's invariant uses, transcribed to `⟶ᵉ′` and `↣′`. The facts about free
names of targets and stacks come through the embedding; the constructions are rebuilt clause by
clause, with `Me-Pro′`'s premise at the empty stack the only change.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantAvoids where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ)
open import PSS.Close using (fv-open-mono)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas
open import MPSS.VariantPush using (pushᵉ′; relabelᵉ′)
open import MPSS.VariantCtx
open import MPSS.Strengthen using (∉-++; stack-fv)
open import MPSS.AvoidsPreserve using (fvStack-++; ∉-stack-++)
open import MPSS.Closed using (_∉*_; ∉*-++; ∉*-++ˡ; ∉*-++ʳ; Closed; closed-tail; fv-closed)
```

## Avoiding a name

```agda
Avoids′ : ∀ x {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ′ v → Set
Avoids′ x (Me-Var′ {s = s} _)                = x ∉ fvStack s
Avoids′ x (Me-Top′ {s = s} _)                = x ∉ fvStack s
Avoids′ x (Me-TAp′ {s = s} _)                = x ∉ fvStack s
Avoids′ x (Me-Pro′ {s = s} {x = y} _ _ d)    = (x ≢ y) × (x ∉ fvStack s) × Avoids′ x d
Avoids′ x (Me-App′ d e)                      = Avoids′ x d × Avoids′ x e
Avoids′ x (Me-Bet′ L F e)                    = (∀ {z} (p : z ∉ L) → Avoids′ x (F p)) × Avoids′ x e
Avoids′ x (Me-Fun′ {t = t} L d F)            =
  (x ∉ fv t) × Avoids′ x d × (∀ {z} (p : z ∉ L) → z ≢ x → Avoids′ x (F p))
Avoids′ x (Me-FOp′ {α = α} L d F)            =
  (x ∉ fv α) × Avoids′ x d × (∀ {z} (p : z ∉ L) → z ≢ x → Avoids′ x (F p))

unbound-avoids′ : ∀ {Γ s u v} x → x ∉ dom Γ → (d : Γ ∣ s ⊢ u ⟶ᵉ′ v) → Avoids′ x d
unbound-avoids′ x x∉ (Me-Var′ pv) = λ h → x∉ (stack-fv pv h)
unbound-avoids′ x x∉ (Me-Top′ pv) = λ h → x∉ (stack-fv pv h)
unbound-avoids′ x x∉ (Me-TAp′ pv) = λ h → x∉ (stack-fv pv h)
unbound-avoids′ x x∉ (Me-Pro′ pv m d) =
  (λ { refl → x∉ (∈-dom m) }) , (λ h → x∉ (stack-fv pv h)) , unbound-avoids′ x x∉ d
unbound-avoids′ x x∉ (Me-App′ d e) = unbound-avoids′ x x∉ d , unbound-avoids′ x x∉ e
unbound-avoids′ x x∉ (Me-Bet′ L F e) = (λ p → unbound-avoids′ x x∉ (F p)) , unbound-avoids′ x x∉ e
unbound-avoids′ {Γ} x x∉ (Me-Fun′ {t = t} L d F) =
  (λ h → x∉ (head-fv inner h)) , unbound-avoids′ x x∉ d ,
  (λ {z} p z≢x → unbound-avoids′ x (x∉′ z≢x) (F p))
  where
    inner : ((fresh L , sub , t) ∷ Γ) prevalid
    inner = prevalid-ctx (⟶ᵉ′-prevalid (F (fresh-∉ L)))
    x∉′ : ∀ {z} → z ≢ x → x ∉ dom ((z , sub , t) ∷ Γ)
    x∉′ z≢x (here eq)  = z≢x (sym eq)
    x∉′ z≢x (there h)  = x∉ h
unbound-avoids′ {Γ} x x∉ (Me-FOp′ {α = α} {u = u} {u' = u'} L d F) =
  (λ h → x∉ (prevalid-head-fv (⟶ᵉ′-prevalid (Me-FOp′ {u = u} {u' = u'} L d F)) h)) ,
  unbound-avoids′ x x∉ d ,
  (λ {z} p z≢x → unbound-avoids′ x (x∉′ z≢x) (F p))
  where
    x∉′ : ∀ {z} → z ≢ x → x ∉ dom ((z , eqv , α) ∷ Γ)
    x∉′ z≢x (here eq)  = z≢x (sym eq)
    x∉′ z≢x (there h)  = x∉ h

AvoidsC′ : ∀ x {Γ s Γ' s'} → Γ ∣ s ↣′ Γ' ∣ s' → Set
AvoidsC′ x Ct-Refl′       = ⊤
AvoidsC′ x (Ct-Ann′ c d)  = AvoidsC′ x c × Avoids′ x d
AvoidsC′ x (Ct-Stk′ c d)  = AvoidsC′ x c × Avoids′ x d

Avoids*′ : List Name → ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ′ v → Set
Avoids*′ B d = ∀ {b} → b ∈ B → Avoids′ b d
```

## The stack of an avoiding derivation

```agda
avoids-stack′ : ∀ {b Γ s u v} (d : Γ ∣ s ⊢ u ⟶ᵉ′ v) → Avoids′ b d → b ∉ fvStack s
avoids-stack′ (Me-Var′ _)               av = av
avoids-stack′ (Me-Top′ _)               av = av
avoids-stack′ (Me-TAp′ _)               av = av
avoids-stack′ (Me-Pro′ _ _ _)           (_ , av , _) = av
avoids-stack′ (Me-App′ {v = v} d e)     (avd , _) = ∉-++ʳ (fv v) (avoids-stack′ d avd)
avoids-stack′ (Me-Bet′ L F e)           (avF , _) = avoids-stack′ (F (fresh-∉ L)) (avF (fresh-∉ L))
avoids-stack′ (Me-Fun′ L d F)           _ = λ ()
avoids-stack′ {b} (Me-FOp′ {s = s} {α = α} L d F) (b∉α , _ , avF) =
  ∉-++ b∉α (avoids-stack′ (F z∉L) (avF z∉L z≢b))
  where
    A   = L ++ b ∷ []
    z   = fresh A
    z∉L : z ∉ L
    z∉L = ∉-++ˡ (fresh-∉ A)
    z≢b : z ≢ b
    z≢b eq = ∉-++ʳ L (fresh-∉ A) (here eq)

stack-free′ : ∀ {B Γ s u v} (d : Γ ∣ s ⊢ u ⟶ᵉ′ v) → Avoids*′ B d → B ∉* fvStack s
stack-free′ d av b∈ = avoids-stack′ d (av b∈)
```

## Preservation under weakening, relabelling, pushing, and reflexivity

```agda
avoids-weaken′ : ∀ {b} (Δ Θ : Ctx) {Γ s u v}
               → (pv : (Δ ++ Θ ++ Γ) ∣ s prevalid) (d : (Δ ++ Γ) ∣ s ⊢ u ⟶ᵉ′ v)
               → Avoids′ b d → Avoids′ b (⟶ᵉ′-weaken Δ Θ pv d)
avoids-weaken′ Δ Θ pv (Me-Var′ _)     av = av
avoids-weaken′ Δ Θ pv (Me-Top′ _)     av = av
avoids-weaken′ Δ Θ pv (Me-TAp′ _)     av = av
avoids-weaken′ Δ Θ pv (Me-Pro′ _ m d) (b≢y , b∉s , av) = b≢y , b∉s , avoids-weaken′ Δ Θ _ d av
avoids-weaken′ Δ Θ pv (Me-App′ d e)   (avd , ave) =
  avoids-weaken′ Δ Θ _ d avd , avoids-weaken′ Δ Θ _ e ave
avoids-weaken′ Δ Θ pv (Me-Bet′ {u' = u'} L F e) (avF , ave) =
  (λ p → avoids-weaken′ Δ Θ pv (F p) (avF p)) , avoids-weaken′ Δ Θ _ e ave
avoids-weaken′ Δ Θ {Γ} pv (Me-Fun′ {t = t} {u = u} {u' = u'} L d F) (b∉t , avd , avF) =
  b∉t , avoids-weaken′ Δ Θ pv d avd ,
  (λ {y} y∉ y≢b → avoids-weaken′ ((y , sub , t) ∷ Δ) Θ _ (F (∉-++ˡ y∉)) (avF (∉-++ˡ y∉) y≢b))
avoids-weaken′ Δ Θ {Γ} pv (Me-FOp′ {s = s} {α = α} {u = u} {u' = u'} L d F) (b∉α , avd , avF) =
  b∉α , avoids-weaken′ Δ Θ _ d avd ,
  (λ {y} y∉ y≢b → avoids-weaken′ ((y , eqv , α) ∷ Δ) Θ _ (F (∉-++ˡ y∉)) (avF (∉-++ˡ y∉) y≢b))

avoids-relabel′ : ∀ {b} (Δ : Ctx) {Γ x t α s u v}
                → (pe : ((x , eqv , α) ∷ Γ) prevalid)
                → (d : (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ᵉ′ v)
                → Avoids′ b d → Avoids′ b (relabelᵉ′ Δ pe d)
avoids-relabel′ Δ pe (Me-Var′ _)     av = av
avoids-relabel′ Δ pe (Me-Top′ _)     av = av
avoids-relabel′ Δ pe (Me-TAp′ _)     av = av
avoids-relabel′ Δ pe (Me-Pro′ _ m d) (b≢y , b∉s , av) = b≢y , b∉s , avoids-relabel′ Δ pe d av
avoids-relabel′ Δ pe (Me-App′ d e)   (avd , ave) = avoids-relabel′ Δ pe d avd , avoids-relabel′ Δ pe e ave
avoids-relabel′ Δ pe (Me-Bet′ {u' = u'} L F e) (avF , ave) =
  (λ p → avoids-relabel′ Δ pe (F p) (avF p)) , avoids-relabel′ Δ pe e ave
avoids-relabel′ Δ pe (Me-Fun′ {t = t′} {u' = u'} L d F) (b∉t , avd , avF) =
  b∉t , avoids-relabel′ Δ pe d avd ,
  (λ {y} y∉ y≢b → avoids-relabel′ ((y , sub , t′) ∷ Δ) pe (F y∉) (avF y∉ y≢b))
avoids-relabel′ Δ pe (Me-FOp′ {α = β} {u' = u'} L d F) (b∉β , avd , avF) =
  b∉β , avoids-relabel′ Δ pe d avd ,
  (λ {y} y∉ y≢b → avoids-relabel′ ((y , eqv , β) ∷ Δ) pe (F y∉) (avF y∉ y≢b))

avoids-push′ : ∀ {b Γ s s′ u v} (d : Γ ∣ s ⊢ u ⟶ᵉ′ v) (pv : Γ ∣ (s ++ s′) prevalid)
             → Avoids′ b d → b ∉ fvStack s′ → Avoids′ b (pushᵉ′ d pv)
avoids-push′ {s = s} {s′} (Me-Var′ _)     pv av s′∉ = ∉-stack-++ s s′ av s′∉
avoids-push′ {s = s} {s′} (Me-Top′ _)     pv av s′∉ = ∉-stack-++ s s′ av s′∉
avoids-push′ {s = s} {s′} (Me-TAp′ _)     pv av s′∉ = ∉-stack-++ s s′ av s′∉
avoids-push′ {s = s} {s′} (Me-Pro′ _ m d) pv (b≢y , b∉s , av) s′∉ =
  b≢y , ∉-stack-++ s s′ b∉s s′∉ , av
avoids-push′ (Me-App′ d e) pv (avd , ave) s′∉ = avoids-push′ d _ avd s′∉ , ave
avoids-push′ (Me-Bet′ {u' = u'} L F e) pv (avF , ave) s′∉ =
  (λ p → avoids-push′ (F p) pv (avF p) s′∉) , ave
avoids-push′ {s′ = []} (Me-Fun′ L d F) pv av s′∉ = av
avoids-push′ {Γ} {s′ = α ∷ s″} (Me-Fun′ {t = t} {u = u} {u' = u'} L d F) pv (b∉t , avd , avF) s′∉ =
  ∉-++ˡ s′∉ , avd ,
  (λ {x} x∉ x≢b → avoids-push′ (relabelᵉ′ [] _ (F (∉-++ˡ x∉))) _
                               (avoids-relabel′ [] _ (F (∉-++ˡ x∉)) (avF (∉-++ˡ x∉) x≢b))
                               (∉-++ʳ (fv α) s′∉))
avoids-push′ {Γ} {s = α ∷ s₀} {s′} (Me-FOp′ {u = u} {u' = u'} L d F) pv (b∉α , avd , avF) s′∉ =
  b∉α , avd , (λ {x} x∉ x≢b → avoids-push′ (F (∉-++ˡ x∉)) _ (avF (∉-++ˡ x∉) x≢b) s′∉)

avoids-refl′ : ∀ {b Γ s t} (pv : Γ ∣ s prevalid) (lt : LC t) (f : fv t ⊑ dom Γ)
             → b ∉ fvStack s → b ∉ fv t → Avoids′ b (⟶ᵉ′-refl pv lt f)
avoids-refl′ pv lc-fvar f s∉ t∉ = s∉
avoids-refl′ pv lc-Top  f s∉ t∉ = s∉
avoids-refl′ pv (lc-app {u} {v} lu lv) f s∉ t∉ =
  avoids-refl′ _ lu _ (∉-++ (∉-++ʳ (fv u) t∉) s∉) (∉-++ˡ t∉) ,
  avoids-refl′ _ lv _ (λ ()) (∉-++ʳ (fv u) t∉)
avoids-refl′ {b} {Γ} {[]} pv (lc-lam {t} {b′} L lt F) f s∉ t∉ =
  ∉-++ˡ t∉ , avoids-refl′ _ lt _ (λ ()) (∉-++ˡ t∉) ,
  (λ {x} x∉ x≢b → avoids-refl′ _ (F (∉-++ˡ x∉)) _ (λ ())
                               (fv-open-mono 0 x b′ (λ eq → x≢b (sym eq)) (∉-++ʳ (fv t) t∉)))
avoids-refl′ {b} {Γ} {α ∷ s} pv (lc-lam {t} {b′} L lt F) f s∉ t∉ =
  ∉-++ˡ s∉ , avoids-refl′ _ lt _ (λ ()) (∉-++ˡ t∉) ,
  (λ {x} x∉ x≢b → avoids-refl′ _ (F (∉-++ˡ x∉)) _ (∉-++ʳ (fv α) s∉)
                               (fv-open-mono 0 x b′ (λ eq → x≢b (sym eq)) (∉-++ʳ (fv t) t∉)))
```

## Closure, through the embedding

```agda
fv-closed′ : ∀ {Γ s t t′ B} → Closed Γ B → B ∉* fvStack s → B ∉* fv t
           → Γ ∣ s ⊢ t ⟶ᵉ′ t′ → B ∉* fv t′
fv-closed′ cl s∉ t∉ d = fv-closed cl s∉ t∉ (⟶ᵉ′⊆⟶ᵉ d)

↣′-stack-closed : ∀ {Γ s Γ' s' B} → Closed Γ B → B ∉* fvStack s
                → Γ ∣ s ↣′ Γ' ∣ s' → B ∉* fvStack s'
↣′-stack-closed cl s∉ Ct-Refl′      = s∉
↣′-stack-closed cl s∉ (Ct-Ann′ c e) = ↣′-stack-closed (closed-tail cl) s∉ c
↣′-stack-closed {s = α ∷ s} cl s∉ (Ct-Stk′ c e) =
  ∉*-++ (fv-closed′ cl (λ _ ()) (∉*-++ˡ s∉) e) (↣′-stack-closed cl (∉*-++ʳ (fv α) s∉) c)
```

## What this establishes

The avoidance predicate for the variant, its stability under the four constructions the diamond
applies to copied pieces, and the closure facts for the variant's context reduction.
