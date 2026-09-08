# MPSS: chains of variant steps, and their congruences

Chains of `⟶ᵉ′` steps, with the congruence lemmas `MPSS/Peel` composes them by. Every chain here
is *non-empty* — a first step and a possibly empty rest — because the `Me-Bet` case has to feed a
first body step and a first operand step to `Me-Bet′`, and a source term cannot in general be held
still (`MPSS/Pushable`). Holding a *target* still is always possible, and that is what every
lemma below does when one of two chains runs out before the other.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import PSS.Syntax
open import PSS.Close using (open-close; fv-close)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas
open import MPSS.VariantSubst using (⟶ᵉ′-subst-float)
open import MPSS.Pushable
open import MPSS.StackPush using (prevalid-cons)
open import MPSS.Rename using (x∉-w)
```

## Chains

```agda
infixr 5 _◅′_
infix 3 _∣_⊢_⟶ᵉ′*_ _∣_⊢_⟶ᵉ′⁺_
data _∣_⊢_⟶ᵉ′*_ : Ctx → Stack → Tm → Tm → Set where
  ε′   : ∀ {Γ s a} → Γ ∣ s prevalid → Γ ∣ s ⊢ a ⟶ᵉ′* a
  _◅′_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ′ b → Γ ∣ s ⊢ b ⟶ᵉ′* c → Γ ∣ s ⊢ a ⟶ᵉ′* c

_++′_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ′* b → Γ ∣ s ⊢ b ⟶ᵉ′* c → Γ ∣ s ⊢ a ⟶ᵉ′* c
ε′ _     ++′ q = q
(d ◅′ p) ++′ q = d ◅′ (p ++′ q)

⟶ᵉ′*-prevalid : ∀ {Γ s a b} → Γ ∣ s ⊢ a ⟶ᵉ′* b → Γ ∣ s prevalid
⟶ᵉ′*-prevalid (ε′ pv)  = pv
⟶ᵉ′*-prevalid (d ◅′ _) = ⟶ᵉ′-prevalid d

-- a non-empty chain: the first step, then the rest
_∣_⊢_⟶ᵉ′⁺_ : Ctx → Stack → Tm → Tm → Set
Γ ∣ s ⊢ a ⟶ᵉ′⁺ c = ∃[ b ] ((Γ ∣ s ⊢ a ⟶ᵉ′ b) × (Γ ∣ s ⊢ b ⟶ᵉ′* c))

⁺→* : ∀ {Γ s a c} → Γ ∣ s ⊢ a ⟶ᵉ′⁺ c → Γ ∣ s ⊢ a ⟶ᵉ′* c
⁺→* (_ , d , p) = d ◅′ p

_++⁺_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ′⁺ b → Γ ∣ s ⊢ b ⟶ᵉ′⁺ c → Γ ∣ s ⊢ a ⟶ᵉ′⁺ c
(b , d , p) ++⁺ q = b , d , (p ++′ ⁺→* q)

single : ∀ {Γ s a b} → Γ ∣ s ⊢ a ⟶ᵉ′ b → Γ ∣ s ⊢ a ⟶ᵉ′⁺ b
single d = _ , d , ε′ (⟶ᵉ′-prevalid d)
```

## Application: the operator moves, then the operand

```agda
app-left* : ∀ {Γ s v a c} → Γ ∣ (v ∷ s) ⊢ a ⟶ᵉ′* c → Γ ∣ s ⊢ app a v ⟶ᵉ′* app c v
app-left* (ε′ pv)   = ε′ (prevalid-pop pv)
app-left* (d ◅′ p)  = Me-App′ d (refl-head′ (⟶ᵉ′-prevalid d)) ◅′ app-left* p

app-left⁺ : ∀ {Γ s v a c} → Γ ∣ (v ∷ s) ⊢ a ⟶ᵉ′⁺ c → Γ ∣ s ⊢ app a v ⟶ᵉ′⁺ app c v
app-left⁺ (_ , d , p) = _ , Me-App′ d (refl-head′ (⟶ᵉ′-prevalid d)) , app-left* p
```

The operator is held still; it is a target, so pushable.

```agda
app-right* : ∀ {Γ s a v v′} → Γ ∣ s prevalid → LC a → Pushable (suc (length s)) (dom Γ) a
           → LC v → fv v ⊑ dom Γ
           → Γ ∣ [] ⊢ v ⟶ᵉ′* v′ → Γ ∣ s ⊢ app a v ⟶ᵉ′* app a v′
app-right* pv la pa lv fvv (ε′ _)   = ε′ pv
app-right* pv la pa lv fvv (d ◅′ p) =
  Me-App′ (⟶ᵉ′-refl-push (Pv-Sta pv lv fvv) la pa) d
    ◅′ app-right* pv la pa (⟶ᵉ′-lc lv d) (fv-⟶ᵉ′ ⊑-refl d fvv) p

app-right⁺ : ∀ {Γ s a v v′} → Γ ∣ s prevalid → LC a → Pushable (suc (length s)) (dom Γ) a
           → LC v → fv v ⊑ dom Γ
           → Γ ∣ [] ⊢ v ⟶ᵉ′⁺ v′ → Γ ∣ s ⊢ app a v ⟶ᵉ′⁺ app a v′
app-right⁺ pv la pa lv fvv (_ , d , p) =
  _ , Me-App′ (⟶ᵉ′-refl-push (Pv-Sta pv lv fvv) la pa) d
    , app-right* pv la pa (⟶ᵉ′-lc lv d) (fv-⟶ᵉ′ ⊑-refl d fvv) p
```

## Abstraction at the empty stack: the body moves under the binder, then the annotation

The annotation of an abstraction at the empty stack is scoped, so it can be held still by plain
reflexivity while the body's chain is wrapped under the binder.

```agda
fun-body* : ∀ {Γ w a c} x → x ∉ dom Γ → LC a
          → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ′* c
          → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ᵉ′* lam w (closeRec 0 x c)
fun-body* x x∉ la (ε′ pv)  = ε′ (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
fun-body* x x∉ la (d ◅′ p) =
  wrapᵉ′-fun x x∉ la (⟶ᵉ′-lc la d) d ◅′ fun-body* x x∉ (⟶ᵉ′-lc la d) p

fun-body⁺ : ∀ {Γ w a c} x → x ∉ dom Γ → LC a
          → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ′⁺ c
          → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ᵉ′⁺ lam w (closeRec 0 x c)
fun-body⁺ x x∉ la (_ , d , p) =
  _ , wrapᵉ′-fun x x∉ la (⟶ᵉ′-lc la d) d , fun-body* x x∉ (⟶ᵉ′-lc la d) p
```

Then the annotation moves, with the body — a target — held still under each intermediate
annotation.

```agda
fun-ann* : ∀ {Γ w w′ u} (L : List Name) → LC w → fv w ⊑ dom Γ
         → (∀ {y} → y ∉ L → LC (u ^ fvar y) × Pushable 0 (y ∷ dom Γ) (u ^ fvar y))
         → Γ ∣ [] ⊢ w ⟶ᵉ′* w′ → Γ ∣ [] ⊢ lam w u ⟶ᵉ′* lam w′ u
fun-ann* L lw fw B (ε′ pv)  = ε′ pv
fun-ann* {Γ} {w} {w′} {u} L lw fw B (d ◅′ p) =
  Me-Fun′ (L ++ dom Γ) d body ◅′ fun-ann* L (⟶ᵉ′-lc lw d) (fv-⟶ᵉ′ ⊑-refl d fw) B p
  where
    pv = ⟶ᵉ′-prevalid d
    body : ∀ {y} → y ∉ (L ++ dom Γ) → ((y , sub , w) ∷ Γ) ∣ [] ⊢ (u ^ fvar y) ⟶ᵉ′ (u ^ fvar y)
    body {y} y∉ = ⟶ᵉ′-refl-push (prevalid-cons pv (∉-++ʳ L y∉) lw fw)
                                (proj₁ (B (∉-++ˡ y∉))) (proj₂ (B (∉-++ˡ y∉)))
```

## Abstraction at a non-empty stack: annotation and body move together

Here the annotation never enters the context, so it need not be scoped and cannot be held still
at the start. The two chains are zipped step by step; whichever runs out first is held still from
then on, as a target.

```agda
fop-step : ∀ {Γ s w w′ α a a′} x → x ∉ dom Γ → x ∉ fvStack s → LC a → LC a′
         → Γ ∣ [] ⊢ w ⟶ᵉ′ w′
         → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ᵉ′ a′
         → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ᵉ′ lam w′ (closeRec 0 x a′)
fop-step {Γ} {s} {w} {w′} {α} {a} {a′} x x∉Γ x∉s la la′ dw d = Me-FOp′ (dom Γ) dw fam
  where
    pv = prevalid-ctx (⟶ᵉ′-prevalid d)

    d′ : ((x , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar x) ⟶ᵉ′ a′
    d′ rewrite open-close la 0 x = d

    fam : ∀ {y} → y ∉ dom Γ
        → ((y , eqv , α) ∷ Γ) ∣ s ⊢ ((closeRec 0 x a) ^ fvar y) ⟶ᵉ′ ((closeRec 0 x a′) ^ fvar y)
    fam {y} y∉ = ⟶ᵉ′-rename-head {b = closeRec 0 x a} x y x∉Γ y∉ (x∉-w [] pv) (fv-close 0 x a) x∉s la′ d′

fop-zip* : ∀ {Γ s w w′ α a c} x → x ∉ dom Γ → x ∉ fvStack s
         → LC w → Pushable 0 (dom Γ) w → LC a → Pushable (length s) (x ∷ dom Γ) a
         → Γ ∣ [] ⊢ w ⟶ᵉ′* w′
         → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ᵉ′* c
         → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ᵉ′* lam w′ (closeRec 0 x c)
fop-zip* x x∉Γ x∉s lw pw la pa (ε′ pv) (ε′ pv′) =
  ε′ (Pv-Sta (prevalid-strengthen x∉s pv′) (head-lc (prevalid-ctx pv′)) (head-fv (prevalid-ctx pv′)))
fop-zip* x x∉Γ x∉s lw pw la pa (ε′ pv) (d ◅′ p) =
  fop-step x x∉Γ x∉s la (⟶ᵉ′-lc la d) (⟶ᵉ′-refl-push pv lw pw) d
    ◅′ fop-zip* x x∉Γ x∉s lw pw (⟶ᵉ′-lc la d) (pushable-target la d) (ε′ pv) p
fop-zip* x x∉Γ x∉s lw pw la pa (dw ◅′ q) (ε′ pv′) =
  fop-step x x∉Γ x∉s la la dw (⟶ᵉ′-refl-push pv′ la pa)
    ◅′ fop-zip* x x∉Γ x∉s (⟶ᵉ′-lc lw dw) (pushable-target lw dw) la pa q (ε′ pv′)
fop-zip* x x∉Γ x∉s lw pw la pa (dw ◅′ q) (d ◅′ p) =
  fop-step x x∉Γ x∉s la (⟶ᵉ′-lc la d) dw d
    ◅′ fop-zip* x x∉Γ x∉s (⟶ᵉ′-lc lw dw) (pushable-target lw dw) (⟶ᵉ′-lc la d) (pushable-target la d) q p

fop-zip⁺ : ∀ {Γ s w w′ α a c} x → x ∉ dom Γ → x ∉ fvStack s → LC w → LC a
         → Γ ∣ [] ⊢ w ⟶ᵉ′⁺ w′
         → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ᵉ′⁺ c
         → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ᵉ′⁺ lam w′ (closeRec 0 x c)
fop-zip⁺ x x∉Γ x∉s lw la (_ , dw , q) (_ , d , p) =
  _ , fop-step x x∉Γ x∉s la (⟶ᵉ′-lc la d) dw d
    , fop-zip* x x∉Γ x∉s (⟶ᵉ′-lc lw dw) (pushable-target lw dw) (⟶ᵉ′-lc la d) (pushable-target la d) q p
```

## β: the first step, and substituting the two remaining chains into each other

The first body step at the fresh name `x` becomes a cofinite family by renaming `x`, which for an
unbound name is the floating substitution of a variable.

```agda
bet-first : ∀ {Γ s t u w₁ v v₁} x → x ∉ dom Γ → x ∉ fv u → LC w₁
          → Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ w₁
          → Γ ∣ [] ⊢ v ⟶ᵉ′ v₁
          → Γ ∣ s ⊢ app (lam t u) v ⟶ᵉ′ ((closeRec 0 x w₁) ^ v₁)
bet-first {Γ} {s} {t} {u} {w₁} {v} {v₁} x x∉Γ x∉u lw₁ d e =
  Me-Bet′ {u' = closeRec 0 x w₁} [] fam e
  where
    pv₀ : Γ ∣ [] prevalid
    pv₀ = prevalid-nil (⟶ᵉ′-prevalid d)

    d′ : Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ ((closeRec 0 x w₁) ^ fvar x)
    d′ rewrite open-close lw₁ 0 x = d

    fam : ∀ {y} → y ∉ [] → Γ ∣ s ⊢ (u ^ fvar y) ⟶ᵉ′ ((closeRec 0 x w₁) ^ fvar y)
    fam {y} _ = result
      where
        renamed : Γ ∣ s ⊢ ((u ^ fvar x) [ x := fvar y ]) ⟶ᵉ′ (((closeRec 0 x w₁) ^ fvar x) [ x := fvar y ])
        renamed = ⟶ᵉ′-subst-float x x∉Γ lc-fvar lc-fvar d′ (Me-Var′ pv₀)

        result : Γ ∣ s ⊢ (u ^ fvar y) ⟶ᵉ′ ((closeRec 0 x w₁) ^ fvar y)
        result rewrite subst-intro {u} (lc-fvar {y}) x x∉u
                     | subst-intro {closeRec 0 x w₁} (lc-fvar {y}) x (fv-close 0 x w₁)
                     = renamed
```

The remaining body chain (at `x`) and operand chain are combined stepwise; when one runs out,
its current term is a target and is held still.

```agda
subst-chains : ∀ {Γ s a c v v′} x → x ∉ dom Γ
             → LC a → Pushable (length s) (dom Γ) a → LC v → Pushable 0 (dom Γ) v
             → Γ ∣ s ⊢ a ⟶ᵉ′* c → Γ ∣ [] ⊢ v ⟶ᵉ′* v′
             → Γ ∣ s ⊢ (a [ x := v ]) ⟶ᵉ′* (c [ x := v′ ])
subst-chains x x∉ la pa lv pv (ε′ pvs) (ε′ _) = ε′ pvs
subst-chains x x∉ la pa lv pv (d ◅′ p) (ε′ pv₀) =
  ⟶ᵉ′-subst-float x x∉ lv lv d (⟶ᵉ′-refl-push pv₀ lv pv)
    ◅′ subst-chains x x∉ (⟶ᵉ′-lc la d) (pushable-target la d) lv pv p (ε′ pv₀)
subst-chains x x∉ la pa lv pv (ε′ pvs) (e ◅′ q) =
  ⟶ᵉ′-subst-float x x∉ lv (⟶ᵉ′-lc lv e) (⟶ᵉ′-refl-push pvs la pa) e
    ◅′ subst-chains x x∉ la pa (⟶ᵉ′-lc lv e) (pushable-target lv e) (ε′ pvs) q
subst-chains x x∉ la pa lv pv (d ◅′ p) (e ◅′ q) =
  ⟶ᵉ′-subst-float x x∉ lv (⟶ᵉ′-lc lv e) d e
    ◅′ subst-chains x x∉ (⟶ᵉ′-lc la d) (pushable-target la d) (⟶ᵉ′-lc lv e) (pushable-target lv e) p q
```

## What this establishes

Non-empty chains of variant steps with concatenation, and the five ways `MPSS/Peel` extends
them: under an application on either side, under an abstraction at the empty stack in two phases,
under an abstraction at a non-empty stack by zipping, and through a β-redex by a first `Me-Bet′`
step followed by stepwise substitution.
