# Lemma 5.1 — minimal promotion is unique

One of the items owed against arXiv v1's §5. Minimal promotion is deterministic: a term has at
most one minimal promotion in a given extended context.

The rules of `⟶mp` look overlapping but are not. `mp-nf` demands `¬ NF u` while every other rule
applies only to normal forms; `mp-fun` and `mp-funop` are separated by the stack; and `mp-fun`
cannot compete with `mp-top` on `λt.Top`, because its premise would need `Top ⟶mp _`, which no
rule derives.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module PSS.MinimalUnique where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Close using (close-open)
open import PSS.Confluence using (nf-unique)
open import PSS.Algorithms using (_∣_⊢_⟶mp_; mp-nf; mp-var; mp-app; mp-fun; mp-funop; mp-top)
```

## Nothing promotes out of `Top`

```agda
Top-no-mp : ∀ {Γ s w} → ¬ (Γ ∣ s ⊢ Top ⟶mp w)
Top-no-mp (mp-nf ¬nf _ _ _) = ¬nf nf-Top
```

## Bounds are unique in a prevalid context

```agda
∈-dom' : ∀ {Γ x t} → x ≤ t ∈ Γ → x ∈ dom Γ
∈-dom' (here refl) = here refl
∈-dom' (there m)   = there (∈-dom' m)

bound-unique : ∀ {Γ s x t₁ t₂} → Γ ∣ s prevalid → x ≤ t₁ ∈ Γ → x ≤ t₂ ∈ Γ → t₁ ≡ t₂
bound-unique pv m₁ m₂ = go (ctx pv) m₁ m₂
  where
    ctx : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ [] prevalid
    ctx P-Ctx1              = P-Ctx1
    ctx p@(P-Ctx2 _ _ _ _)  = p
    ctx (P-Ctx3 p _ _)      = ctx p

    go : ∀ {Γ x t₁ t₂} → Γ ∣ [] prevalid → x ≤ t₁ ∈ Γ → x ≤ t₂ ∈ Γ → t₁ ≡ t₂
    go _ (here refl) (here refl)                = refl
    go (P-Ctx2 _ x∉ _ _) (here refl) (there n)  = ⊥-elim (x∉ (∈-dom' n))
    go (P-Ctx2 _ x∉ _ _) (there m) (here refl)  = ⊥-elim (x∉ (∈-dom' m))
    go (P-Ctx2 p _ _ _)  (there m) (there n)    = go p m n
```

## Opened bodies determine the body

```agda
open-inj : ∀ {u v x} → x ∉ fv u → x ∉ fv v → (u ^ fvar x) ≡ (v ^ fvar x) → u ≡ v
open-inj {u} {v} {x} x∉u x∉v e =
  trans (sym (close-open 0 x u x∉u)) (trans (cong (closeRec 0 x) e) (close-open 0 x v x∉v))
```

## Lemma 5.1

```agda
Lem-5·1 : ∀ {Γ s u v₁ v₂} → LC u
        → Γ ∣ s ⊢ u ⟶mp v₁ → Γ ∣ s ⊢ u ⟶mp v₂ → v₁ ≡ v₂

Lem-5·1 lu (mp-nf _ _ c₁ n₁) (mp-nf _ _ c₂ n₂) = nf-unique lu c₁ c₂ n₁ n₂

Lem-5·1 lu (mp-nf ¬nf _ _ _) (mp-var _ _)      = ⊥-elim (¬nf (nf-ne ne-var))
Lem-5·1 lu (mp-var _ _) (mp-nf ¬nf _ _ _)      = ⊥-elim (¬nf (nf-ne ne-var))
Lem-5·1 lu (mp-nf ¬nf _ _ _) (mp-app ne nv _)  = ⊥-elim (¬nf (nf-ne (ne-app ne nv)))
Lem-5·1 lu (mp-app ne nv _) (mp-nf ¬nf _ _ _)  = ⊥-elim (¬nf (nf-ne (ne-app ne nv)))
Lem-5·1 lu (mp-nf ¬nf _ _ _) (mp-fun _ nf _)   = ⊥-elim (¬nf nf)
Lem-5·1 lu (mp-fun _ nf _) (mp-nf ¬nf _ _ _)   = ⊥-elim (¬nf nf)
Lem-5·1 lu (mp-nf ¬nf _ _ _) (mp-funop _ nf _) = ⊥-elim (¬nf nf)
Lem-5·1 lu (mp-funop _ nf _) (mp-nf ¬nf _ _ _) = ⊥-elim (¬nf nf)
Lem-5·1 lu (mp-nf ¬nf _ _ _) (mp-top _ nf)     = ⊥-elim (¬nf nf)
Lem-5·1 lu (mp-top _ nf) (mp-nf ¬nf _ _ _)     = ⊥-elim (¬nf nf)

Lem-5·1 lu (mp-var pv m₁) (mp-var _ m₂) = bound-unique pv m₁ m₂

Lem-5·1 (lc-app lf la) (mp-app _ _ d₁) (mp-app _ _ d₂) =
  cong (λ z → app z _) (Lem-5·1 lf d₁ d₂)

Lem-5·1 (lc-lam L₀ lt F₀) (mp-fun {u' = c₁} L₁ _ F₁) (mp-fun {u' = c₂} L₂ _ F₂) =
  cong (lam _) (open-inj x∉c₁ x∉c₂ (Lem-5·1 (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)))
  where
    A   = L₀ ++ L₁ ++ L₂ ++ fv c₁ ++ fv c₂
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L₁ r₁
    r₃  = ∉-++ʳ L₂ r₂
    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ r₁
    x∉L₂ = ∉-++ˡ r₂
    x∉c₁ : x ∉ fv c₁
    x∉c₁ = ∉-++ˡ r₃
    x∉c₂ : x ∉ fv c₂
    x∉c₂ = ∉-++ʳ (fv c₁) r₃

Lem-5·1 (lc-lam L₀ lt F₀) (mp-funop {u' = c₁} L₁ _ F₁) (mp-funop {u' = c₂} L₂ _ F₂) =
  cong (lam _) (open-inj x∉c₁ x∉c₂ (Lem-5·1 (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)))
  where
    A   = L₀ ++ L₁ ++ L₂ ++ fv c₁ ++ fv c₂
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L₁ r₁
    r₃  = ∉-++ʳ L₂ r₂
    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ r₁
    x∉L₂ = ∉-++ˡ r₂
    x∉c₁ : x ∉ fv c₁
    x∉c₁ = ∉-++ˡ r₃
    x∉c₂ : x ∉ fv c₂
    x∉c₂ = ∉-++ʳ (fv c₁) r₃

Lem-5·1 lu (mp-top _ _) (mp-top _ _) = refl

Lem-5·1 (lc-lam L₀ lt F₀) (mp-fun L₁ _ F₁) (mp-top _ _) =
  ⊥-elim (Top-no-mp (F₁ (∉-++ʳ L₀ (fresh-∉ (L₀ ++ L₁)))))
Lem-5·1 (lc-lam L₀ lt F₀) (mp-top _ _) (mp-fun L₂ _ F₂) =
  ⊥-elim (Top-no-mp (F₂ (∉-++ʳ L₀ (fresh-∉ (L₀ ++ L₂)))))
Lem-5·1 (lc-lam L₀ lt F₀) (mp-funop L₁ _ F₁) (mp-top _ _) =
  ⊥-elim (Top-no-mp (F₁ (∉-++ʳ L₀ (fresh-∉ (L₀ ++ L₁)))))
Lem-5·1 (lc-lam L₀ lt F₀) (mp-top _ _) (mp-funop L₂ _ F₂) =
  ⊥-elim (Top-no-mp (F₂ (∉-++ʳ L₀ (fresh-∉ (L₀ ++ L₂)))))
```

## What this establishes

**Lemma 5.1**: minimal promotion is a partial function. The proof turns on the four disjointness
arguments listed at the head of the module, plus `nf-unique` for the `mp-nf` case, uniqueness of
bounds in a prevalid context for `mp-var`, and injectivity of opening for the two binder cases.
