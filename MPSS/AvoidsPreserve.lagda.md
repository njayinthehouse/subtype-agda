# MPSS: avoiding a name survives weakening, pushing, relabelling, and reflexivity

`Avoids x d` (`MPSS/Strengthen`) is the hypothesis the diamond's invariant places on one side's
derivations. The recursion does four things to those derivations before handing them to a
recursive call: it weakens them into a larger context (`⟶ᵉ-weaken`), pushes them under a stack
(`pushᵉ`, which relabels a `≤` binding to `≡` on the way), and, where the context reduction is
reflexive, manufactures them by `⟶ᵉ-refl`. Each preserves `Avoids`, under the evident conditions
on the material added: the pushed stack must not mention the name, and a reflexivity derivation
avoids a name its subject and stack do not mention.

Every lemma follows the definition it is about clause by clause. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.AvoidsPreserve where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Strengthen using (Avoids; ∉-++)
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.StackPush using (pushᵉ; relabelᵉ; ⟶ᵉ-refl)
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ)
open import PSS.Close using (fv-open-mono)
```

## The stack of an avoiding derivation

```agda
avoids-stack : ∀ {b Γ s u v} (d : Γ ∣ s ⊢ u ⟶ᵉ v) → Avoids b d → b ∉ fvStack s
avoids-stack (Me-Var _)               av = av
avoids-stack (Me-Top _)               av = av
avoids-stack (Me-TAp _)               av = av
avoids-stack (Me-Pro _ _ _)           (_ , av , _) = av
avoids-stack (Me-App {v = v} d e)     (avd , _) = ∉-++ʳ (fv v) (avoids-stack d avd)
avoids-stack (Me-Bet L F e)           (avF , _) = avoids-stack (F (fresh-∉ L)) (avF (fresh-∉ L))
avoids-stack (Me-Fun L d F)           _ = λ ()
avoids-stack {b} (Me-FOp {s = s} {α = α} L d F) (b∉α , _ , avF) =
  ∉-++ b∉α (avoids-stack (F z∉L) (avF z∉L z≢b))
  where
    A   = L ++ b ∷ []
    z   = fresh A
    z∉L : z ∉ L
    z∉L = ∉-++ˡ (fresh-∉ A)
    z≢b : z ≢ b
    z≢b eq = ∉-++ʳ L (fresh-∉ A) (here eq)

fvStack-++ : ∀ s s′ → fvStack (s ++ s′) ≡ fvStack s ++ fvStack s′
fvStack-++ []      s′ = refl
fvStack-++ (α ∷ s) s′ rewrite fvStack-++ s s′ = ++-assoc′ (fv α) (fvStack s) (fvStack s′)
  where
    ++-assoc′ : ∀ (xs ys zs : List Name) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
    ++-assoc′ []       ys zs = refl
    ++-assoc′ (x ∷ xs) ys zs rewrite ++-assoc′ xs ys zs = refl

∉-stack-++ : ∀ {b} s s′ → b ∉ fvStack s → b ∉ fvStack s′ → b ∉ fvStack (s ++ s′)
∉-stack-++ s s′ p q rewrite fvStack-++ s s′ = ∉-++ p q
```

## Weakening

```agda
avoids-weaken : ∀ {b} (Δ Θ : Ctx) {Γ s u v}
              → (pv : (Δ ++ Θ ++ Γ) ∣ s prevalid) (d : (Δ ++ Γ) ∣ s ⊢ u ⟶ᵉ v)
              → Avoids b d → Avoids b (⟶ᵉ-weaken Δ Θ pv d)
avoids-weaken Δ Θ pv (Me-Var _)     av = av
avoids-weaken Δ Θ pv (Me-Top _)     av = av
avoids-weaken Δ Θ pv (Me-TAp _)     av = av
avoids-weaken Δ Θ pv (Me-Pro _ m d) (b≢y , b∉s , av) = b≢y , b∉s , avoids-weaken Δ Θ pv d av
avoids-weaken Δ Θ pv (Me-App d e)   (avd , ave) =
  avoids-weaken Δ Θ _ d avd , avoids-weaken Δ Θ _ e ave
avoids-weaken Δ Θ pv (Me-Bet {u' = u'} L F e) (avF , ave) =
  (λ p → avoids-weaken Δ Θ pv (F p) (avF p)) , avoids-weaken Δ Θ _ e ave
avoids-weaken Δ Θ {Γ} pv (Me-Fun {t = t} {u = u} {u' = u'} L d F) (b∉t , avd , avF) =
  b∉t , avoids-weaken Δ Θ pv d avd ,
  (λ {y} y∉ y≢b → avoids-weaken ((y , sub , t) ∷ Δ) Θ _ (F (∉-++ˡ y∉)) (avF (∉-++ˡ y∉) y≢b))
avoids-weaken Δ Θ {Γ} pv (Me-FOp {s = s} {α = α} {u = u} {u' = u'} L d F) (b∉α , avd , avF) =
  b∉α , avoids-weaken Δ Θ _ d avd ,
  (λ {y} y∉ y≢b → avoids-weaken ((y , eqv , α) ∷ Δ) Θ _ (F (∉-++ˡ y∉)) (avF (∉-++ˡ y∉) y≢b))
```

## Relabelling

```agda
avoids-relabel : ∀ {b} (Δ : Ctx) {Γ x t α s u v}
               → (pe : ((x , eqv , α) ∷ Γ) prevalid)
               → (d : (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v)
               → Avoids b d → Avoids b (relabelᵉ Δ pe d)
avoids-relabel Δ pe (Me-Var _)     av = av
avoids-relabel Δ pe (Me-Top _)     av = av
avoids-relabel Δ pe (Me-TAp _)     av = av
avoids-relabel Δ pe (Me-Pro _ m d) (b≢y , b∉s , av) = b≢y , b∉s , avoids-relabel Δ pe d av
avoids-relabel Δ pe (Me-App d e)   (avd , ave) = avoids-relabel Δ pe d avd , avoids-relabel Δ pe e ave
avoids-relabel Δ pe (Me-Bet {u' = u'} L F e) (avF , ave) =
  (λ p → avoids-relabel Δ pe (F p) (avF p)) , avoids-relabel Δ pe e ave
avoids-relabel Δ pe (Me-Fun {t = t′} {u' = u'} L d F) (b∉t , avd , avF) =
  b∉t , avoids-relabel Δ pe d avd ,
  (λ {y} y∉ y≢b → avoids-relabel ((y , sub , t′) ∷ Δ) pe (F y∉) (avF y∉ y≢b))
avoids-relabel Δ pe (Me-FOp {α = β} {u' = u'} L d F) (b∉β , avd , avF) =
  b∉β , avoids-relabel Δ pe d avd ,
  (λ {y} y∉ y≢b → avoids-relabel ((y , eqv , β) ∷ Δ) pe (F y∉) (avF y∉ y≢b))
```

## Pushing

```agda
avoids-push : ∀ {b Γ s s′ u v} (d : Γ ∣ s ⊢ u ⟶ᵉ v) (pv : Γ ∣ (s ++ s′) prevalid)
            → Avoids b d → b ∉ fvStack s′ → Avoids b (pushᵉ d pv)
avoids-push {s = s} {s′} (Me-Var _)     pv av s′∉ = ∉-stack-++ s s′ av s′∉
avoids-push {s = s} {s′} (Me-Top _)     pv av s′∉ = ∉-stack-++ s s′ av s′∉
avoids-push {s = s} {s′} (Me-TAp _)     pv av s′∉ = ∉-stack-++ s s′ av s′∉
avoids-push {s = s} {s′} (Me-Pro _ m d) pv (b≢y , b∉s , av) s′∉ =
  b≢y , ∉-stack-++ s s′ b∉s s′∉ , avoids-push d pv av s′∉
avoids-push (Me-App d e) pv (avd , ave) s′∉ = avoids-push d _ avd s′∉ , ave
avoids-push (Me-Bet {u' = u'} L F e) pv (avF , ave) s′∉ =
  (λ p → avoids-push (F p) pv (avF p) s′∉) , ave
avoids-push {s′ = []} (Me-Fun L d F) pv av s′∉ = av
avoids-push {Γ} {s′ = α ∷ s″} (Me-Fun {t = t} {u = u} {u' = u'} L d F) pv (b∉t , avd , avF) s′∉ =
  ∉-++ˡ s′∉ , avd ,
  (λ {x} x∉ x≢b → avoids-push (relabelᵉ [] _ (F (∉-++ˡ x∉))) _
                              (avoids-relabel [] _ (F (∉-++ˡ x∉)) (avF (∉-++ˡ x∉) x≢b))
                              (∉-++ʳ (fv α) s′∉))
avoids-push {Γ} {s = α ∷ s₀} {s′} (Me-FOp {u = u} {u' = u'} L d F) pv (b∉α , avd , avF) s′∉ =
  b∉α , avd , (λ {x} x∉ x≢b → avoids-push (F (∉-++ˡ x∉)) _ (avF (∉-++ˡ x∉) x≢b) s′∉)
```

## Reflexivity

```agda
avoids-refl : ∀ {b Γ s t} (pv : Γ ∣ s prevalid) (lt : LC t) (f : fv t ⊑ dom Γ)
            → b ∉ fvStack s → b ∉ fv t → Avoids b (⟶ᵉ-refl pv lt f)
avoids-refl pv lc-fvar f s∉ t∉ = s∉
avoids-refl pv lc-Top  f s∉ t∉ = s∉
avoids-refl pv (lc-app {u} {v} lu lv) f s∉ t∉ =
  avoids-refl _ lu _ (∉-++ (∉-++ʳ (fv u) t∉) s∉) (∉-++ˡ t∉) ,
  avoids-refl _ lv _ (λ ()) (∉-++ʳ (fv u) t∉)
avoids-refl {b} {Γ} {[]} pv (lc-lam {t} {b′} L lt F) f s∉ t∉ =
  ∉-++ˡ t∉ , avoids-refl _ lt _ (λ ()) (∉-++ˡ t∉) ,
  (λ {x} x∉ x≢b → avoids-refl _ (F (∉-++ˡ x∉)) _ (λ ())
                              (fv-open-mono 0 x b′ (λ eq → x≢b (sym eq)) (∉-++ʳ (fv t) t∉)))
avoids-refl {b} {Γ} {α ∷ s} pv (lc-lam {t} {b′} L lt F) f s∉ t∉ =
  ∉-++ˡ s∉ , avoids-refl _ lt _ (λ ()) (∉-++ˡ t∉) ,
  (λ {x} x∉ x≢b → avoids-refl _ (F (∉-++ˡ x∉)) _ (∉-++ʳ (fv α) s∉)
                              (fv-open-mono 0 x b′ (λ eq → x≢b (sym eq)) (∉-++ʳ (fv t) t∉)))
```

## What this establishes

The four preservation facts, each by following the definition it is about. With these, the
diamond's invariant can take `Avoids` as a hypothesis on the inputs of a recursive call whenever
those inputs are weakened, pushed, or reflexive versions of derivations already known to avoid
the name.
