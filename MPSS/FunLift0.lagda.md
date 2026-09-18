# MPSS: `FunLift` under one operand, from Conjecture 8 at the pair (operand, annotation)

`MPSS/Conj8Push` rests Conjecture 8 on two obligations. This module discharges the first of them,
`FunLift`, in the case the recursion turns on — an abstraction `λx≤t.u` whose body promotes under
`x ≤ t`, applied to one operand `v` and nothing more — from Conjecture 8 *at the single pair*
`(v, t)`, `C8At Γ v t` of `MPSS/Conj8Pair`. It is `MPSS/CONJ8.md` §7's sketch, mechanized:

- both applications β-reduce, through well-formed terms, to `u ^ v` and `u' ^ v`
  (`Prop-17ʷ`, the chain form of Proposition 17), and a layer absorbs those steps on either side;
- the operand is below the annotation, `v ≤*wf t`, by inversion on the application's
  well-formedness (Lemmas 10, 15, 16);
- `u ^ v` and `u' ^ v` are well-formed by Lemma 7 for the substitution `x := v`, and
  `u ^ v ≤*wf u' ^ v` is Lemma 9 for it — both from the conjecture at `(v, t)` only.

So the recursion of the conjecture is explicit and pair by pair: lifting a promotion of `λx≤t.u`
under `v` asks for the conjecture at `(v, t)`, where `t` is, by the same inversion, the domain of
whatever the abstraction is below.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.FunLift0 where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import MPSS.WellFormed
open import MPSS.Static using (Lem-15; Lem-16; ⊑*wf⇒wfʳ)
open import MPSS.Unconditional using (Lem-10)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Prop17Chain using (_⊢_⟶ᵉ*wf_; εʷ; step; push-chain; Prop-17ʷ)
open import MPSS.Conj8Pair using (C8At; Lem-9ᵖ; Lem-7ᵖ)

open import PSS.Syntax using (subst-intro; ∉-++ˡ; ∉-++ʳ; fresh; fresh-∉)
```

## A chain of equivalence steps through well-formed terms, read as a layer in either direction

```agda
chain-≤ : ∀ {Γ a c} → Γ ⊢ a wf → Γ ⊢ a ⟶ᵉ*wf c → Γ ⊢ a ⊑*wf[ sub-m ] c
chain-≤ wa (εʷ _)        = Ws-Sub wa (Ws-Rfl (wf⇒prevalid wa)) wa
chain-≤ wa (step e wb p) =
  Ws-Trs (Ws-Sub wa (Ws-Lf1 e (Ws-Rfl (wf⇒prevalid wa))) wb) wb (chain-≤ wb p)

chain-≥ : ∀ {Γ a c} → Γ ⊢ a wf → Γ ⊢ a ⟶ᵉ*wf c → Γ ⊢ c ⊑*wf[ sub-m ] a
chain-≥ wa p = push-chain (Ws-Sub wa (Ws-Rfl (wf⇒prevalid wa)) wa) p
```

## The operand is below the annotation

```agda
operand≤ : ∀ {Γ t u v} → Γ ⊢ app (lam t u) v wf → Γ ⊢ v ⊑*wf[ sub-m ] t
operand≤ (Wf-App d₁ d₂) with ⊑*wf⇒wfˡ d₁ | ⊑*wf⇒wfʳ d₁
... | Wf-Fun _ _ wt | Wf-Fun _ _ wz =
  Ws-Trs d₂ wz (Ws-Sub wz (Lem-16 (Lem-15 (Lem-10 d₁))) wt)
```

## `FunLift` under one operand

```agda
FunLift₀ : ∀ {Γ t u u' v} (L : List Name)
         → (∀ {x} → x ∉ L → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar x) ⟶ˢ (u' ^ fvar x))
         → C8At Γ v t
         → Γ ⊢ app (lam t u) v wf → Γ ⊢ app (lam t u') v wf
         → Γ ⊢ app (lam t u) v ⊑*wf[ sub-m ] app (lam t u') v
FunLift₀ {Γ} {t} {u} {u'} {v} L F c8 wa@(Wf-App d₁ d₂) wa'@(Wf-App d₁' _)
  with ⊑*wf⇒wfˡ d₁ | ⊑*wf⇒wfˡ d₁'
... | wf@(Wf-Fun L₁ F₁ wt) | wf'@(Wf-Fun L₂ F₂ _) =
  Ws-Trs (Ws-Trs (chain-≤ wa β) wuv mid) wu'v (chain-≥ wa' β')
  where
    A    = L ++ L₁ ++ L₂ ++ fv u ++ fv u' ++ dom Γ
    z    = fresh A
    z∉   = fresh-∉ A
    z∉L  : z ∉ L
    z∉L  = ∉-++ˡ z∉
    z∉L₁ : z ∉ L₁
    z∉L₁ = ∉-++ˡ (∉-++ʳ L z∉)
    z∉L₂ : z ∉ L₂
    z∉L₂ = ∉-++ˡ (∉-++ʳ L₁ (∉-++ʳ L z∉))
    z∉u  : z ∉ fv u
    z∉u  = ∉-++ˡ (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L z∉)))
    z∉u' : z ∉ fv u'
    z∉u' = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L z∉))))

    wv  = ⊑*wf⇒wfˡ d₂
    lv  = wf⇒lc wv
    lt  = wf⇒lc wt
    fvv = wf-fv wv
    v≤t = operand≤ wa

    wuv : Γ ⊢ (u ^ v) wf
    wuv = subst (λ q → Γ ⊢ q wf) (sym (subst-intro {u} lv z z∉u))
                (Lem-7ᵖ c8 lv lt fvv wv v≤t [] (F₁ z∉L₁))

    wu'v : Γ ⊢ (u' ^ v) wf
    wu'v = subst (λ q → Γ ⊢ q wf) (sym (subst-intro {u'} lv z z∉u'))
                 (Lem-7ᵖ c8 lv lt fvv wv v≤t [] (F₂ z∉L₂))

    mid : Γ ⊢ (u ^ v) ⊑*wf[ sub-m ] (u' ^ v)
    mid = subst₂ (λ p q → Γ ⊢ p ⊑*wf[ sub-m ] q)
                 (sym (subst-intro {u} lv z z∉u)) (sym (subst-intro {u'} lv z z∉u'))
                 (Lem-9ᵖ [] (c8 []) lv lt fvv
                         (subst (λ q → Γ ⊢ q wf) (subst-intro {u} lv z z∉u) wuv)
                         (subst (λ q → Γ ⊢ q wf) (subst-intro {u'} lv z z∉u') wu'v)
                         v≤t (F z∉L))

    β  : Γ ⊢ app (lam t u) v ⟶ᵉ*wf (u ^ v)
    β  = Prop-17ʷ wa (E-App (wf⇒lc wf) lv) wuv

    β' : Γ ⊢ app (lam t u') v ⟶ᵉ*wf (u' ^ v)
    β' = Prop-17ʷ wa' (E-App (wf⇒lc wf') lv) wu'v
```

## What this establishes

`FunLift₀ : C8At Γ v t → …`: a promotion under `λx≤t`, lifted under the operand `v`, from
Conjecture 8 at the pair `(v, t)` in the contexts that extend `Γ`. With `operand≤` the pair is
always an instance the conjecture applies to.
