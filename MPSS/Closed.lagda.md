# MPSS: names a reduction cannot introduce

The `Me-App`/`Me-Bet` case of the diamond needs the body's join on the `Me-App` side to avoid the
parameter `x` it was found under (`MPSS/Strengthen`). That is an invariant the whole induction has
to carry, and stating it for a single name is not enough: the recursion binds further names to
terms that mention `x`, and a promotion of one of those reintroduces `x`. The invariant that is
closed under the recursion is about a *set* of names `B` that is closed upward under the context's
annotations of either kind — if an annotation mentions a name in `B`, the variable it annotates is
in `B` too. Then a term free of `B` stays free of `B` under reduction at a stack free of `B`, because
every name a reduction can introduce comes from such an annotation.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Closed where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Strengthen using (Avoids; AvoidsC)
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ)
open import PSS.Scope using (fv-open-lower; fv-open-split)
```

## Sets of names

`B ∉* V`: no name of `B` occurs in `V`.

```agda
infix 4 _∉*_
_∉*_ : List Name → List Name → Set
B ∉* V = ∀ {b} → b ∈ B → b ∉ V

∉*-++ : ∀ {B V W} → B ∉* V → B ∉* W → B ∉* (V ++ W)
∉*-++ {V = V} p q b∈ h with ∈-++⁻ V h
... | inj₁ a = p b∈ a
... | inj₂ a = q b∈ a

∉*-++ˡ : ∀ {B V W} → B ∉* (V ++ W) → B ∉* V
∉*-++ˡ p b∈ h = p b∈ (∈-++⁺ˡ h)

∉*-++ʳ : ∀ {B} V {W} → B ∉* (V ++ W) → B ∉* W
∉*-++ʳ V p b∈ h = p b∈ (∈-++⁺ʳ V h)

∉*-tail : ∀ {B z V} → B ∉* (z ∷ V) → B ∉* V
∉*-tail p b∈ h = p b∈ (there h)

∉*-⊑ : ∀ {B B′ V} → B ⊑ B′ → B′ ∉* V → B ∉* V
∉*-⊑ inc p b∈ = p (inc b∈)
```

A fresh name for a finite set of names is outside it.

```agda
∉-∉* : ∀ {B z} → z ∉ B → B ∉* (z ∷ [])
∉-∉* z∉ b∈ (here refl) = z∉ b∈
```

## Closure

```agda
Closed : Ctx → List Name → Set
Closed Γ B = ∀ {y c α b} → (y , c , α) ∈ Γ → b ∈ B → b ∈ fv α → y ∈ B

closed-tail : ∀ {Γ e B} → Closed (e ∷ Γ) B → Closed Γ B
closed-tail cl m = cl (there m)

closed-sub : ∀ {Γ B z t} → Closed Γ B → B ∉* fv t → Closed ((z , sub , t) ∷ Γ) B
closed-sub cl t∉ (here refl) b∈ h = ⊥-elim (t∉ b∈ h)
closed-sub cl t∉ (there m)   b∈ h = cl m b∈ h

closed-eqv : ∀ {Γ B z α} → Closed Γ B → B ∉* fv α → Closed ((z , eqv , α) ∷ Γ) B
closed-eqv cl α∉ (here refl) b∈ h = ⊥-elim (α∉ b∈ h)
closed-eqv cl α∉ (there m)   b∈ h = cl m b∈ h
```

Binding a fresh name to anything and adding the name to the set keeps the set closed: the new
annotation may mention `B`, and then its variable is in the new set; the old annotations cannot
mention the fresh name.

```agda
closed-add : ∀ {Γ B z v} → Γ prevalid → z ∉ dom Γ → Closed Γ B
           → Closed ((z , eqv , v) ∷ Γ) (z ∷ B)
closed-add pv z∉ cl (here refl) b∈ h = here refl
closed-add pv z∉ cl (there m) (here refl) h = ⊥-elim (z∉ (prevalid-bound-fv pv m h))
closed-add pv z∉ cl (there m) (there b∈) h = there (cl m b∈ h)
```

## Avoiding a set

```agda
Avoids* : List Name → ∀ {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ v → Set
Avoids* B d = ∀ {b} → b ∈ B → Avoids b d

AvoidsC* : List Name → ∀ {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → Set
AvoidsC* B c = ∀ {b} → b ∈ B → AvoidsC b c

avoids*-⊑ : ∀ {B B′ Γ s u v} {d : Γ ∣ s ⊢ u ⟶ᵉ v} → B ⊑ B′ → Avoids* B′ d → Avoids* B d
avoids*-⊑ inc av b∈ = av (inc b∈)

avoidsC*-⊑ : ∀ {B B′ Γ s Γ' s'} {c : Γ ∣ s ↣ Γ' ∣ s'} → B ⊑ B′ → AvoidsC* B′ c → AvoidsC* B c
avoidsC*-⊑ inc av b∈ = av (inc b∈)
```

## A reduction introduces no name of a closed set

The subject is free of `B`, the stack is free of `B`, and the context is closed under `B`. Every
name a reduct can contain comes from the source, from an annotation `Me-Pro` reads, or from a
stack entry `Me-FOp` binds; the first two are free of `B` by hypothesis and closure, the third by
hypothesis.

```agda
fv-closed : ∀ {Γ s t t′ B} → Closed Γ B → B ∉* fvStack s → B ∉* fv t
          → Γ ∣ s ⊢ t ⟶ᵉ t′ → B ∉* fv t′
fv-closed cl s∉ t∉ (Me-Var _) = t∉
fv-closed cl s∉ t∉ (Me-Top _) = t∉
fv-closed cl s∉ t∉ (Me-TAp _) = λ _ ()
fv-closed cl s∉ t∉ (Me-Pro pv m d) =
  fv-closed cl s∉ (λ b∈ h → t∉ (cl m b∈ h) (here refl)) d
fv-closed {t = app u v} cl s∉ t∉ (Me-App {u' = u′} d e) =
  ∉*-++ (fv-closed cl (∉*-++ (∉*-++ʳ (fv u) t∉) s∉) (∉*-++ˡ t∉) d)
        (fv-closed cl (λ _ ()) (∉*-++ʳ (fv u) t∉) e)
fv-closed {Γ} {s} {t = app (lam t₀ u) v} {B = B} cl s∉ t∉
          (Me-Bet {u' = u′} {v' = v′} L F e) b∈ h
  with fv-open-split 0 v′ u′ h
... | inj₁ p = bodyfree b∈ (fv-open-lower 0 (fvar z) u′ p)
  where
    A   = L ++ B
    z   = fresh A
    z∉L = ∉-++ˡ (fresh-∉ A)
    z∉B = ∉-++ʳ L (fresh-∉ A)
    u∉  : B ∉* fv (u ^ fvar z)
    u∉ b∈′ q with fv-open-split 0 (fvar z) u q
    ... | inj₁ r           = t∉ b∈′ (∈-++⁺ˡ (∈-++⁺ʳ (fv t₀) r))
    ... | inj₂ (here refl) = z∉B b∈′
    bodyfree : B ∉* fv (u′ ^ fvar z)
    bodyfree = fv-closed cl s∉ u∉ (F z∉L)
... | inj₂ p = fv-closed cl (λ _ ()) (∉*-++ʳ (fv (lam t₀ u)) t∉) e b∈ p
fv-closed {Γ} {t = lam t₀ u} {B = B} cl s∉ t∉ (Me-Fun {t' = t₁} {u' = u′} L d F) b∈ h
  with ∈-++⁻ (fv t₁) h
... | inj₁ p = fv-closed cl (λ _ ()) (∉*-++ˡ t∉) d b∈ p
... | inj₂ p = bodyfree b∈ (fv-open-lower 0 (fvar z) u′ p)
  where
    A   = L ++ B
    z   = fresh A
    z∉L = ∉-++ˡ (fresh-∉ A)
    z∉B = ∉-++ʳ L (fresh-∉ A)
    u∉  : B ∉* fv (u ^ fvar z)
    u∉ b∈′ q with fv-open-split 0 (fvar z) u q
    ... | inj₁ r           = t∉ b∈′ (∈-++⁺ʳ (fv t₀) r)
    ... | inj₂ (here refl) = z∉B b∈′
    bodyfree : B ∉* fv (u′ ^ fvar z)
    bodyfree = fv-closed (closed-sub cl (∉*-++ˡ t∉)) (λ _ ()) u∉ (F z∉L)
fv-closed {Γ} {s = α ∷ s} {t = lam t₀ u} {B = B} cl s∉ t∉
          (Me-FOp {t' = t₁} {u' = u′} L d F) b∈ h
  with ∈-++⁻ (fv t₁) h
... | inj₁ p = fv-closed cl (λ _ ()) (∉*-++ˡ t∉) d b∈ p
... | inj₂ p = bodyfree b∈ (fv-open-lower 0 (fvar z) u′ p)
  where
    A   = L ++ B
    z   = fresh A
    z∉L = ∉-++ˡ (fresh-∉ A)
    z∉B = ∉-++ʳ L (fresh-∉ A)
    u∉  : B ∉* fv (u ^ fvar z)
    u∉ b∈′ q with fv-open-split 0 (fvar z) u q
    ... | inj₁ r           = t∉ b∈′ (∈-++⁺ʳ (fv t₀) r)
    ... | inj₂ (here refl) = z∉B b∈′
    bodyfree : B ∉* fv (u′ ^ fvar z)
    bodyfree = fv-closed (closed-eqv cl (∉*-++ˡ s∉)) (∉*-++ʳ (fv α) s∉) u∉ (F z∉L)
```

## Along a context reduction

The reduced stack is free of `B` if the original was, since each entry is reduced at a tail of
the context, which is closed too, at the empty stack.

```agda
↣-stack-closed : ∀ {Γ s Γ' s' B} → Closed Γ B → B ∉* fvStack s
               → Γ ∣ s ↣ Γ' ∣ s' → B ∉* fvStack s'
↣-stack-closed cl s∉ Ct-Refl      = s∉
↣-stack-closed cl s∉ (Ct-Ann c e) = ↣-stack-closed (closed-tail cl) s∉ c
↣-stack-closed {s = α ∷ s} cl s∉ (Ct-Stk c e) =
  ∉*-++ (fv-closed cl (λ _ ()) (∉*-++ˡ s∉) e) (↣-stack-closed cl (∉*-++ʳ (fv α) s∉) c)
```

## What this establishes

`fv-closed`: at a context closed under `B` and a stack free of `B`, reduction never introduces a
name of `B`. `↣-stack-closed`: the same for the stack of a reduced configuration. Together with
`closed-add`, which is what the `Me-App`/`Me-Bet` case does to the set when it binds the fresh
parameter, these are the facts the diamond's invariant needs about names.
