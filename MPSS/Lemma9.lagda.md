# MPSS: Lemma 9

> **Lemma 9.** Let `Γ;s` be an extended context and `Γ′` a logical context such that
> `Γ, Γ′[x\α]; nil` is prevalid. Let `u`, `v`, `t`, `α` be terms such that both `u[x\α]` and
> `v[x\α]` are well-formed in `Γ, Γ′[x\α]`. If `Γ, x≤t, Γ′; nil ⊢ u ⟶≤ v` and `Γ ⊢ α ≤*wf t`,
> then `Γ, Γ′[x\α] ⊢ u[x\α] ≤*wf v[x\α]`.

The paper's proof splits on whether the derivation is `Co[x] ⟶≤ Co[t]`; `MPSS/Lemma2930` decides
that split on the terms and returns the covariant context in the affirmative case. What is left
is to feed each branch to the right rule.

**On the paper's "Else" branch.** It concludes with "By rule `Ws-Lft`" — there is no such rule.
The step carries a *promotion*, so the rule that applies is `Ws-Lf2`, and `Ws-Lf2` needs both
terms well-formed. The paper does supply that ("Because both terms are well-formed by
assumption") but attaches it to the following `Ws-Sub` instead. Both premises are among the
lemma's own hypotheses, so the gap is only in the citation; `Ws-Lf2` is what is used below.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Lemma9 where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Rename using (substCtx; x∉-domΓ; prevalid-suffix)
open import MPSS.Assumed using (Conj-8)
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug)
open import MPSS.CoPair using (CoPair; coOf; co-src; co-tgt)
open import MPSS.Lemma2930 using (Lem-29-30)

open import PSS.Syntax using (subst-fresh; subst-fvar-≡)
```

## Substitution on covariant contexts

```agda
substCo : Name → Tm → CoCtx → CoCtx
substCo x α ∙            = ∙
substCo x α (co-fun t C) = co-fun (t [ x := α ]) (substCo x α C)
substCo x α (co-app C v) = co-app (substCo x α C) (v [ x := α ])

plug-subst : ∀ C x α w → (plug C w) [ x := α ] ≡ plug (substCo x α C) (w [ x := α ])
plug-subst ∙            x α w = refl
plug-subst (co-fun t C) x α w = cong (lam (t [ x := α ])) (plug-subst C x α w)
plug-subst (co-app C v) x α w = cong (λ q → app q (v [ x := α ])) (plug-subst C x α w)
```

## Lemma 9

```agda
Lem-9 : Conj-8 → ∀ (Δ : Ctx) {Γ x t α u v}
      → LC α → LC t → fv α ⊑ dom Γ
      → (substCtx x α Δ ++ Γ) ⊢ (u [ x := α ]) wf
      → (substCtx x α Δ ++ Γ) ⊢ (v [ x := α ]) wf
      → (substCtx x α Δ ++ Γ) ⊢ α ⊑*wf[ sub-m ] t
      → (Δ ++ (x , sub , t) ∷ Γ) ∣ [] ⊢ u ⟶ˢ v
      → (substCtx x α Δ ++ Γ) ⊢ (u [ x := α ]) ⊑*wf[ sub-m ] (v [ x := α ])
Lem-9 conj8 Δ {Γ} {x} {t} {α} {u} {v} lα lt fα wu wv α≤t d
  with Lem-29-30 Δ {α = α} lα fα d
```

**Off the covariant pattern.** The substituted derivation is a promotion, so `Ws-Lf2` consumes it
directly and `Ws-Sub` lifts the result.

```agda
... | inj₂ st = Ws-Sub wu (Ws-Lf2 wu st wv (Ws-Rfl (wf⇒prevalid wu))) wv
```

**On it.** The source is `Co[x]` and the target `Co[t]`, so substituting turns them into
`Co[x\α][α]` and `Co[x\α][t]` — the latter because `x` does not occur in `t`, `t` being an
annotation scoped in the part of the context before it. Conjecture 8 relates the two.

```agda
... | inj₁ c = transport (conj8 C′ lα lt α≤t wu′ wv′)
  where
    ctx : (Δ ++ (x , sub , t) ∷ Γ) prevalid
    ctx = prevalid-ctx (⟶ˢ-prevalid d)

    x∉t : x ∉ fv t
    x∉t h = x∉-domΓ Δ ctx (head-fv (prevalid-suffix Δ ctx) h)

    C′ : CoCtx
    C′ = substCo x α (coOf c)

    eu : (u [ x := α ]) ≡ plug C′ α
    eu = trans (cong (_[ x := α ]) (co-src c))
               (trans (plug-subst (coOf c) x α (fvar x))
                      (cong (plug C′) (subst-fvar-≡ {x} α)))

    ev : (v [ x := α ]) ≡ plug C′ t
    ev = trans (cong (_[ x := α ]) (co-tgt c))
               (trans (plug-subst (coOf c) x α t)
                      (cong (plug C′) (subst-fresh {t} x α x∉t)))

    wu′ : (substCtx x α Δ ++ Γ) ⊢ plug C′ α wf
    wu′ = subst (λ q → (substCtx x α Δ ++ Γ) ⊢ q wf) eu wu

    wv′ : (substCtx x α Δ ++ Γ) ⊢ plug C′ t wf
    wv′ = subst (λ q → (substCtx x α Δ ++ Γ) ⊢ q wf) ev wv

    transport : (substCtx x α Δ ++ Γ) ⊢ plug C′ α ⊑*wf[ sub-m ] plug C′ t
              → (substCtx x α Δ ++ Γ) ⊢ (u [ x := α ]) ⊑*wf[ sub-m ] (v [ x := α ])
    transport h rewrite eu | ev = h
```

## What this establishes

Lemma 9, modulo Conjecture 8 alone. Note where the substitution lands: `(fvar x) [x\α]` is `α`,
so the covariant branch is exactly Conjecture 8's statement with `Co[x\α]` for the context, `α`
for the smaller term and `t` for the larger — which is why the conjecture is stated over covariant
contexts in the first place.
