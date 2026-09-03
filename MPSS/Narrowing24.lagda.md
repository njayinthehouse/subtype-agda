# MPSS: narrowing an annotation in a promotion

> **Lemma 24 (Narrowing of context in subtyping reductions).** If `Γ, x≤t, Γ′; nil ⊢ u ⟶ˢ v` and
> `Γ;nil ⊢ t ⟶ᵉ t′`, and both `u` and `v` are well-formed in `Γ, x≤t′, Γ′`, and `Γ ⊢ t′ wf`, then
> there is `v′` with `Γ, x≤t′, Γ′; nil ⊢ u ⟶ˢ v′`, `Γ, x≤t′, Γ′; nil ⊢ v ⟶ˢ v′`, and
> `Γ, x≤t′, Γ′ ⊢ v′ wf`.

Unlike its equivalence counterpart (Lemma 25) this one cannot be an equality: `Ms-Pro` *does*
read subtype annotations, so a promotion of `x` lands on `t` before narrowing and on `t′` after,
and the two are only joined by a further step. Hence the existential.

Two departures from the printed statement, both forced and both benign:

- **Any stack, not just `nil`.** The induction passes through `Ms-App`, which takes its premise at
  a pushed stack, so the statement has to be available there.
- **Scoping instead of well-formedness.** The paper's well-formedness hypotheses are used only to
  know the terms are scoped — reflexivity of `⟶ˢ` needs that, which is the repair
  `MPSS/ReflFails` forces. Scoping is what well-formedness gives (`wf-fv`), so this is the same
  hypothesis in weaker form, and the well-formedness of `v′` that the paper also concludes is
  omitted, since nothing downstream of it is mechanized yet.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Narrowing24 where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Narrowing using (prevalid-narrowˢ; prevalid-narrow; dom-narrow;
                                  narrow-transfer; ann-lc; ann-fv)
open import MPSS.Preserve using (fv-⟶ᵉ; fv-⟶ᵉ-dom)
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
open import MPSS.StackPush using (⟶ˢ-refl; ⟶ᵉ-refl; pushᵉ; fv-open-cons)
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.Narrow using (⟶ᵉ-transfer)
open import MPSS.Wrap using (wrapˢ-fun; wrapˢ-fop; wrapᵉ-fun; wrapᵉ-fop)
open import PSS.Scope using (fv-open-lower; fv-open-split)
open import PSS.Close using (close-open; fv-close)
open import PSS.Syntax using (closeRec)
```

## Promotion preserves scoping

`Ms-Pro` replaces a variable by an annotation, which prevalidity scopes; `Ms-Equ` defers to
`fv-⟶ᵉ`.

```agda
fv-⟶ˢ : ∀ {Γ s t t′ N} → dom Γ ⊑ N → Γ ∣ s ⊢ t ⟶ˢ t′ → fv t ⊑ N → fv t′ ⊑ N
fv-⟶ˢ dn (Ms-Pro pv m) ft = λ h → dn (prevalid-bound-fv (prevalid-ctx pv) m h)
fv-⟶ˢ dn (Ms-Top _)    ft = λ ()
fv-⟶ˢ dn (Ms-Equ _ e)  ft = fv-⟶ᵉ dn e ft

fv-⟶ˢ {t = app u v} dn (Ms-App {u' = u′} d) ft h with ∈-++⁻ (fv u′) h
... | inj₁ p = fv-⟶ˢ dn d (λ q → ft (∈-++⁺ˡ q)) p
... | inj₂ p = ft (∈-++⁺ʳ (fv u) p)

fv-⟶ˢ {Γ} {t = lam a b} {N = N} dn (Ms-Fun {t = t₀} {u = u} {u' = u′} L F) ft h
  with ∈-++⁻ (fv a) h
... | inj₁ p = ft (∈-++⁺ˡ p)
... | inj₂ p = body p
  where
    A    = L ++ fv u′
    x    = fresh A
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ L (fresh-∉ A)

    dn′ : dom ((x , sub , t₀) ∷ Γ) ⊑ (x ∷ N)
    dn′ (here refl) = here refl
    dn′ (there q)   = there (dn q)

    ftb : fv (u ^ fvar x) ⊑ (x ∷ N)
    ftb q with fv-open-split 0 (fvar x) u q
    ... | inj₁ r           = there (ft (∈-++⁺ʳ (fv a) r))
    ... | inj₂ (here refl) = here refl

    inner : fv (u′ ^ fvar x) ⊑ (x ∷ N)
    inner = fv-⟶ˢ dn′ (F x∉L) ftb

    body : ∀ {y} → y ∈ fv u′ → y ∈ N
    body {y} q with inner (fv-open-lower 0 (fvar x) u′ q)
    ... | here refl = ⊥-elim (x∉u′ q)
    ... | there r   = r

fv-⟶ˢ {Γ} {t = lam a b} {N = N} dn (Ms-FOp {α = α} {u = u} {u' = u′} L F) ft h
  with ∈-++⁻ (fv a) h
... | inj₁ p = ft (∈-++⁺ˡ p)
... | inj₂ p = body p
  where
    A    = L ++ fv u′
    x    = fresh A
    x∉L  = ∉-++ˡ (fresh-∉ A)
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ L (fresh-∉ A)

    dn′ : dom ((x , eqv , α) ∷ Γ) ⊑ (x ∷ N)
    dn′ (here refl) = here refl
    dn′ (there q)   = there (dn q)

    ftb : fv (u ^ fvar x) ⊑ (x ∷ N)
    ftb q with fv-open-split 0 (fvar x) u q
    ... | inj₁ r           = there (ft (∈-++⁺ʳ (fv a) r))
    ... | inj₂ (here refl) = here refl

    inner : fv (u′ ^ fvar x) ⊑ (x ∷ N)
    inner = fv-⟶ˢ dn′ (F x∉L) ftb

    body : ∀ {y} → y ∈ fv u′ → y ∈ N
    body {y} q with inner (fv-open-lower 0 (fvar x) u′ q)
    ... | here refl = ⊥-elim (x∉u′ q)
    ... | there r   = r

fv-⟶ˢ-dom : ∀ {Γ s t t′} → Γ ∣ s ⊢ t ⟶ˢ t′ → fv t ⊑ dom Γ → fv t′ ⊑ dom Γ
fv-⟶ˢ-dom = fv-⟶ˢ (λ h → h)
```

## Lemma 24

The step `t ⟶ᵉ t′` is needed at the narrowed context. Taking it at the empty stack suffices,
since `pushᵉ` lifts it to any stack and weakening carries it over the entries the binder cases
add.

```agda
EStep : Tm → Tm → Ctx → Set
EStep t t′ Γ′ = Γ′ ∣ [] ⊢ t ⟶ᵉ t′

EStep-ext : ∀ {t t′ Γ′ z c w} → ((z , c , w) ∷ Γ′) prevalid
          → EStep t t′ Γ′ → EStep t t′ ((z , c , w) ∷ Γ′)
EStep-ext {z = z} {c} {w} pv est = ⟶ᵉ-weaken [] ((z , c , w) ∷ []) (Pv-Nil pv) est

Lem-24 : ∀ (Δ : Ctx) {Γ x t t′ s u v}
       → EStep t t′ (Δ ++ (x , sub , t′) ∷ Γ)
       → LC t′ → fv t′ ⊑ dom Γ
       → LC u → fv u ⊑ dom (Δ ++ (x , sub , t′) ∷ Γ)
       → (Δ ++ (x , sub , t) ∷ Γ) ∣ s ⊢ u ⟶ˢ v
       → ∃[ v′ ] ( ((Δ ++ (x , sub , t′) ∷ Γ) ∣ s ⊢ u ⟶ˢ v′)
                 × ((Δ ++ (x , sub , t′) ∷ Γ) ∣ s ⊢ v ⟶ᵉ v′) )
```

`Ms-Pro` is the case with content. On a variable other than `x` the entry survives and the two
sides already agree; on `x` itself the old side lands on `t` and the new on `t′`, and the given
step joins them.

```agda
Lem-24 Δ {Γ} {x} {t} {t′} est lt′ ft′ lu fu (Ms-Pro {x = y} {t = ty} pv m)
  with ∈-++⁻ Δ m
... | inj₁ p = ty , Ms-Pro pv′ m′ , ⟶ᵉ-refl pv′ lty fty
  where
    pv′ = prevalid-narrowˢ Δ lt′ ft′ pv
    m′  = ∈-++⁺ˡ p
    lty = prevalid-bound-lc (prevalid-ctx pv′) m′
    fty = prevalid-bound-fv (prevalid-ctx pv′) m′
... | inj₂ (here refl) = t′ , Ms-Pro pv′ m′ , pushᵉ {s = []} est pv′
  where
    pv′ = prevalid-narrowˢ Δ lt′ ft′ pv
    m′  = ∈-++⁺ʳ Δ (here refl)
... | inj₂ (there p) = ty , Ms-Pro pv′ m′ , ⟶ᵉ-refl pv′ lty fty
  where
    pv′ = prevalid-narrowˢ Δ lt′ ft′ pv
    m′  = ∈-++⁺ʳ Δ (there p)
    lty = prevalid-bound-lc (prevalid-ctx pv′) m′
    fty = prevalid-bound-fv (prevalid-ctx pv′) m′
```

`Ms-Top` and `Ms-Equ` transfer, the latter because narrowing a subtype annotation is invisible to
equivalence reduction.

```agda
Lem-24 Δ est lt′ ft′ lu fu (Ms-Top pv) =
  Top , Ms-Top pv′ , Me-Top pv′
  where pv′ = prevalid-narrowˢ Δ lt′ ft′ pv

Lem-24 Δ {Γ} {x} {t} {t′} est lt′ ft′ lu fu (Ms-Equ pv e) =
  _ , Ms-Equ pv′ e′ , ⟶ᵉ-refl pv′ (⟶ᵉ-lc lu e′) (fv-⟶ᵉ-dom e′ fu)
  where
    pv′ = prevalid-narrowˢ Δ lt′ ft′ pv
    e′  = ⟶ᵉ-transfer (narrow-transfer Δ lt′ ft′) e
```

The congruence cases recurse and rebuild.

```agda
Lem-24 Δ est lt′ ft′ (lc-app lu lw) fu (Ms-App {v = w} d)
  with Lem-24 Δ est lt′ ft′ lu (λ h → fu (∈-++⁺ˡ h)) d
... | v′ , p , q = app v′ w , Ms-App p
                 , Me-App q (⟶ᵉ-refl (prevalid-nil pvW)
                                     (prevalid-head-lc pvW) (prevalid-head-fv pvW))
  where pvW = ⟶ˢ-prevalid p
```

Both binder cases join the bodies at one fresh name, close the join, and wrap.

```agda
Lem-24 Δ {Γ} {x} {t} {t′} {u = lam a b} est lt′ ft′ (lc-lam L₀ la F₀) fu
       (Ms-Fun {t = a} {u = b} {u' = b′} L F) = result
  where
    Γn = Δ ++ (x , sub , t′) ∷ Γ

    A  = L₀ ++ L ++ dom Γn ++ fv b ++ fv b′
    z  = fresh A
    a∉ = fresh-∉ A
    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ (dom Γn) r₂

    z∉L₀ = ∉-++ˡ a∉
    z∉L  = ∉-++ˡ r₁
    z∉Γ : z ∉ dom Γn
    z∉Γ  = ∉-++ˡ r₂
    z∉b : z ∉ fv b
    z∉b  = ∉-++ˡ r₃
    z∉b′ : z ∉ fv b′
    z∉b′ = ∉-++ʳ (fv b) r₃

    pvz : ((z , sub , a) ∷ Γn) prevalid
    pvz = Pv-Ctx (prevalid-narrow′) z∉Γ la (λ h → fu (∈-++⁺ˡ h))
      where
        prevalid-narrow′ : Γn prevalid
        prevalid-narrow′ =
          prevalid-narrow-aux (prevalid-ctx (⟶ˢ-prevalid (F z∉L)))
          where
            prevalid-narrow-aux : ((z , sub , a) ∷ (Δ ++ (x , sub , t) ∷ Γ)) prevalid
                                → Γn prevalid
            prevalid-narrow-aux (Pv-Ctx pv _ _ _) = prevalid-narrow Δ lt′ ft′ pv

    ih = Lem-24 ((z , sub , a) ∷ Δ) (EStep-ext pvz est) lt′ ft′
                (F₀ z∉L₀) (fv-open-cons {b = b} z (λ h → fu (∈-++⁺ʳ (fv a) h)))
                (F z∉L)

    w  = proj₁ ih
    lb : LC (b ^ fvar z)
    lb = F₀ z∉L₀
    lb′ : LC (b′ ^ fvar z)
    lb′ = ⟶ˢ-lc lb (F z∉L)
    lw : LC w
    lw = ⟶ˢ-lc lb (proj₁ (proj₂ ih))

    result : ∃[ v′ ] ((Γn ∣ [] ⊢ lam a b ⟶ˢ v′) × (Γn ∣ [] ⊢ lam a b′ ⟶ᵉ v′))
    result = lam a (closeRec 0 z w)
           , subst (λ q → Γn ∣ [] ⊢ lam a q ⟶ˢ lam a (closeRec 0 z w))
                   (close-open 0 z b z∉b)
                   (wrapˢ-fun z z∉Γ lb lw (proj₁ (proj₂ ih)))
           , subst (λ q → Γn ∣ [] ⊢ lam a q ⟶ᵉ lam a (closeRec 0 z w))
                   (close-open 0 z b′ z∉b′)
                   (wrapᵉ-fun z z∉Γ lb′ lw (proj₂ (proj₂ ih)))

Lem-24 Δ {Γ} {x} {t} {t′} {s = α ∷ s} est lt′ ft′ (lc-lam L₀ la F₀) fu
       (Ms-FOp {t = a} {u = b} {u' = b′} L F) = result
  where
    Γn = Δ ++ (x , sub , t′) ∷ Γ

    pvS : (Δ ++ (x , sub , t) ∷ Γ) ∣ (α ∷ s) prevalid
    pvS = ⟶ˢ-prevalid (Ms-FOp {t = a} {u = b} {u' = b′} L F)

    pvSn : Γn ∣ (α ∷ s) prevalid
    pvSn = prevalid-narrowˢ Δ lt′ ft′ pvS

    A  = L₀ ++ L ++ dom Γn ++ fv b ++ fv b′ ++ fvStack s
    z  = fresh A
    a∉ = fresh-∉ A
    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L r₁
    r₃ = ∉-++ʳ (dom Γn) r₂
    r₄ = ∉-++ʳ (fv b) r₃

    z∉L₀ = ∉-++ˡ a∉
    z∉L  = ∉-++ˡ r₁
    z∉Γ : z ∉ dom Γn
    z∉Γ  = ∉-++ˡ r₂
    z∉b : z ∉ fv b
    z∉b  = ∉-++ˡ r₃
    z∉b′ : z ∉ fv b′
    z∉b′ = ∉-++ˡ r₄
    z∉s : z ∉ fvStack s
    z∉s  = ∉-++ʳ (fv b′) r₄

    pvz : ((z , eqv , α) ∷ Γn) prevalid
    pvz = Pv-EqA (prevalid-ctx pvSn) z∉Γ (prevalid-head-lc pvSn) (prevalid-head-fv pvSn)

    ih = Lem-24 ((z , eqv , α) ∷ Δ) (EStep-ext pvz est) lt′ ft′
                (F₀ z∉L₀) (fv-open-cons {b = b} z (λ h → fu (∈-++⁺ʳ (fv a) h)))
                (F z∉L)

    w  = proj₁ ih
    lb : LC (b ^ fvar z)
    lb = F₀ z∉L₀
    lb′ : LC (b′ ^ fvar z)
    lb′ = ⟶ˢ-lc lb (F z∉L)
    lw : LC w
    lw = ⟶ˢ-lc lb (proj₁ (proj₂ ih))

    result : ∃[ v′ ] ((Γn ∣ (α ∷ s) ⊢ lam a b ⟶ˢ v′) × (Γn ∣ (α ∷ s) ⊢ lam a b′ ⟶ᵉ v′))
    result = lam a (closeRec 0 z w)
           , subst (λ q → Γn ∣ (α ∷ s) ⊢ lam a q ⟶ˢ lam a (closeRec 0 z w))
                   (close-open 0 z b z∉b)
                   (wrapˢ-fop z z∉Γ z∉s lb lw (proj₁ (proj₂ ih)))
           , subst (λ q → Γn ∣ (α ∷ s) ⊢ lam a q ⟶ᵉ lam a (closeRec 0 z w))
                   (close-open 0 z b′ z∉b′)
                   (wrapᵉ-fop z z∉Γ z∉s lb′ lw la (λ h → fu (∈-++⁺ˡ h))
                              (proj₂ (proj₂ ih)))
```

## What this establishes

`fv-⟶ˢ` — promotion keeps a term scoped, stated against an ambient name list as `fv-⟶ᵉ` is. This
is the missing ingredient for Lemma 24, whose non-promoting cases close by reflexivity of `⟶ˢ`,
and reflexivity needs exactly this scoping.
