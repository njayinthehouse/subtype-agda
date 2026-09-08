# MPSS: an original step is a chain of variant steps

With `MPSS/EmptyStackPro`'s `⟶ᵉ′ ⊆ ⟶ᵉ`, this makes the two relations' reflexive-transitive
closures equal. The construction is by structural induction on the original derivation, using the
congruences of `MPSS/VariantChain`:

- `Me-Pro`: one `Me-Pro′` whose premise is reflexive, then the premise's chain.
- `Me-App`: the operator's chain at the unreduced operand's stack, then the operand's chain with
  the operator held still.
- `Me-Fun`: the body's chain at one fresh name, wrapped under the binder with the annotation held
  still; then the annotation's chain with the body held still.
- `Me-FOp`: the annotation's and the body's chains zipped, since neither can be held still at the
  start (the annotation is not scoped, the body is a source).
- `Me-Bet`: a first `Me-Bet′` step from the first body step and the first operand step, then the
  two remaining chains substituted into each other stepwise.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Peel where

open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)

open import PSS.Syntax
open import PSS.Close using (open-close; close-open; fv-close)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas
open import MPSS.VariantChain
open import MPSS.Pushable
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Subst.Base using (∉-stack)
```

## A helper

```agda
_++⁺*_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ′⁺ b → Γ ∣ s ⊢ b ⟶ᵉ′* c → Γ ∣ s ⊢ a ⟶ᵉ′⁺ c
(b , d , p) ++⁺* q = b , d , (p ++′ q)
```

## The theorem

```agda
to-chain : ∀ {Γ s t t′} → LC t → Γ ∣ s ⊢ t ⟶ᵉ t′ → Γ ∣ s ⊢ t ⟶ᵉ′⁺ t′

to-chain lt (Me-Var pv) = single (Me-Var′ pv)
to-chain lt (Me-Top pv) = single (Me-Top′ pv)
to-chain lt (Me-TAp pv) = single (Me-TAp′ pv)

to-chain lt (Me-Pro pv m e) =
  _ , Me-Pro′ pv m (⟶ᵉ′-refl (prevalid-nil pv) lα fα) , ⁺→* (to-chain lα e)
  where
    lα = prevalid-bound-lc (prevalid-ctx pv) m
    fα = prevalid-bound-fv (prevalid-ctx pv) m

to-chain (lc-app lu lv) (Me-App d e) =
  app-left⁺ (to-chain lu d)
    ++⁺ app-right⁺ (prevalid-pop (⟶ᵉ-prevalid d)) (⟶ᵉ-lc lu d) (pushable-targetᵒ lu d)
                   lv (prevalid-head-fv (⟶ᵉ-prevalid d)) (to-chain lv e)
```

The β case. The fresh name is chosen outside both cofinite sets, the domain, and the free names
of the body before and after.

```agda
to-chain {Γ} {s} (lc-app (lc-lam {t} {u} L₁ lt F₁) lv)
         (Me-Bet {u' = u′} {v = v} {v' = v′} L F e) = result
  where
    A    = L ++ L₁ ++ dom Γ ++ fv u ++ fv u′
    x    = fresh A
    x∉L  : x ∉ L
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉L₁ : x ∉ L₁
    x∉L₁ = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    x∉Γ  : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))
    x∉u  : x ∉ fv u
    x∉u  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))

    lux : LC (u ^ fvar x)
    lux = F₁ x∉L₁

    C = to-chain lux (F x∉L)
    D = to-chain lv e

    w₁ = proj₁ C
    C₁ : Γ ∣ s ⊢ (u ^ fvar x) ⟶ᵉ′ w₁
    C₁ = proj₁ (proj₂ C)
    Cr : Γ ∣ s ⊢ w₁ ⟶ᵉ′* (u′ ^ fvar x)
    Cr = proj₂ (proj₂ C)

    v₁ = proj₁ D
    D₁ : Γ ∣ [] ⊢ v ⟶ᵉ′ v₁
    D₁ = proj₁ (proj₂ D)
    Dr : Γ ∣ [] ⊢ v₁ ⟶ᵉ′* v′
    Dr = proj₂ (proj₂ D)

    lw₁ : LC w₁
    lw₁ = ⟶ᵉ′-lc lux C₁
    lv₁ : LC v₁
    lv₁ = ⟶ᵉ′-lc lv D₁
    lv′ : LC v′
    lv′ = ⟶ᵉ-lc lv e

    first : Γ ∣ s ⊢ app (lam t u) v ⟶ᵉ′ ((closeRec 0 x w₁) ^ v₁)
    first = bet-first x x∉Γ x∉u lw₁ C₁ D₁

    rest : Γ ∣ s ⊢ (w₁ [ x := v₁ ]) ⟶ᵉ′* ((u′ ^ fvar x) [ x := v′ ])
    rest = subst-chains x x∉Γ lw₁ (pushable-target lux C₁) lv₁ (pushable-target lv D₁) Cr Dr

    eq₁ : ((closeRec 0 x w₁) ^ v₁) ≡ (w₁ [ x := v₁ ])
    eq₁ = trans (subst-intro {closeRec 0 x w₁} lv₁ x (fv-close 0 x w₁))
                (subst (λ q → (q [ x := v₁ ]) ≡ (w₁ [ x := v₁ ])) (sym (open-close lw₁ 0 x)) refl)

    rest′ : Γ ∣ s ⊢ ((closeRec 0 x w₁) ^ v₁) ⟶ᵉ′* (u′ ^ v′)
    rest′ rewrite eq₁ | subst-intro {u′} lv′ x x∉u′ = rest

    result : Γ ∣ s ⊢ app (lam t u) v ⟶ᵉ′⁺ (u′ ^ v′)
    result = _ , first , rest′
```

The abstraction cases.

```agda
to-chain {Γ} (lc-lam {t} {u} L₁ lt F₁) (Me-Fun {t' = t′} {u' = u′} L d F) = result
  where
    A    = L ++ L₁ ++ dom Γ ++ fv u ++ fv u′
    x    = fresh A
    x∉L  : x ∉ L
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉L₁ : x ∉ L₁
    x∉L₁ = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    x∉Γ  : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))
    x∉u  : x ∉ fv u
    x∉u  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))

    ft : fv t ⊑ dom Γ
    ft = head-fv (prevalid-ctx (⟶ᵉ-prevalid (F x∉L)))

    phase₁ : Γ ∣ [] ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ᵉ′⁺ lam t (closeRec 0 x (u′ ^ fvar x))
    phase₁ = fun-body⁺ x x∉Γ (F₁ x∉L₁) (to-chain (F₁ x∉L₁) (F x∉L))

    phase₁′ : Γ ∣ [] ⊢ lam t u ⟶ᵉ′⁺ lam t u′
    phase₁′ = subst₂ (λ a b → Γ ∣ [] ⊢ lam t a ⟶ᵉ′⁺ lam t b)
                     (close-open 0 x u x∉u) (close-open 0 x u′ x∉u′) phase₁

    B : ∀ {y} → y ∉ (L ++ L₁) → LC (u′ ^ fvar y) × Pushable 0 (y ∷ dom Γ) (u′ ^ fvar y)
    B {y} y∉ = ⟶ᵉ-lc (F₁ (∉-++ʳ L y∉)) (F (∉-++ˡ y∉))
             , pushable-targetᵒ (F₁ (∉-++ʳ L y∉)) (F (∉-++ˡ y∉))

    phase₂ : Γ ∣ [] ⊢ lam t u′ ⟶ᵉ′* lam t′ u′
    phase₂ = fun-ann* (L ++ L₁) lt ft B (⁺→* (to-chain lt d))

    result : Γ ∣ [] ⊢ lam t u ⟶ᵉ′⁺ lam t′ u′
    result = phase₁′ ++⁺* phase₂

to-chain {Γ} {α ∷ s} (lc-lam {t} {u} L₁ lt F₁) (Me-FOp {t' = t′} {u' = u′} L d F) = result
  where
    A    = L ++ L₁ ++ dom Γ ++ fv u ++ fv u′ ++ fvStack s
    x    = fresh A
    x∉L  : x ∉ L
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉L₁ : x ∉ L₁
    x∉L₁ = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    x∉Γ  : x ∉ dom Γ
    x∉Γ  = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))
    x∉u  : x ∉ fv u
    x∉u  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A))))
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))))
    x∉s  : x ∉ fvStack s
    x∉s  = ∉-++ʳ (fv u′) (∉-++ʳ (fv u) (∉-++ʳ (dom Γ) (∉-++ʳ L₁ (∉-++ʳ L (fresh-∉ A)))))

    zipped : Γ ∣ (α ∷ s) ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ᵉ′⁺ lam t′ (closeRec 0 x (u′ ^ fvar x))
    zipped = fop-zip⁺ x x∉Γ x∉s lt (F₁ x∉L₁) (to-chain lt d) (to-chain (F₁ x∉L₁) (F x∉L))

    result : Γ ∣ (α ∷ s) ⊢ lam t u ⟶ᵉ′⁺ lam t′ u′
    result = subst₂ (λ a b → Γ ∣ (α ∷ s) ⊢ lam t a ⟶ᵉ′⁺ lam t′ b)
                    (close-open 0 x u x∉u) (close-open 0 x u′ x∉u′) zipped
```

## Consequences

```agda
⟶ᵉ⊆⟶ᵉ′* : ∀ {Γ s t t′} → LC t → Γ ∣ s ⊢ t ⟶ᵉ t′ → Γ ∣ s ⊢ t ⟶ᵉ′* t′
⟶ᵉ⊆⟶ᵉ′* lt d = ⁺→* (to-chain lt d)
```

## What this establishes

`to-chain`, hence `⟶ᵉ ⊆ ⟶ᵉ′*` on locally closed subjects, with `⟶ᵉ′ ⊆ ⟶ᵉ` from
`MPSS/EmptyStackPro`: the original relation and the variant generate the same
reflexive-transitive closure. The variant differs from the original only in forbidding, inside one
step, the interaction of an unfolded definition with the pending operands; that interaction is
recovered in the next step. Consequently the machine relation `⊲` of `MPSS/Subtyping`, which is
closed under chains of `⟶ᵉ` steps on both sides, is the same relation whether built over `⟶ᵉ` or
over `⟶ᵉ′` (`MPSS/VariantMachine`).
