# MPSS: Figure 4 implies the stack-reading well-formedness, from a Conjecture-8-like hypothesis

`CONJ8.md` §28 asks whether every terminating term that Figure 4 accepts (`Γ ⊢ t wf`,
`MPSS/WellFormed`) is well-formed by the stack-reading judgement of `MPSS/StackWf`
(`Γ ∣ [] ⊢ t wfˢ`). This module proves the implication from one hypothesis, which is the hard core
of the question, and proves everything around it.

**Assumed** (module parameters; nothing is postulated):

- `SN : Ctx → Tm → Set`, read "terminating in `Γ`", abstract, closed under immediate subterms:
  `sn-app-l`, `sn-app-r`, `sn-lam-a`, and `sn-lam-b` — the body of a terminating abstraction,
  opened at any name outside some finite list, is terminating under the parameter's bound;
- `C8ˢ`: for a terminating application `f a`, if `f ≤*wfˢ lam d Top` and `a ≤*wfˢ d` at the empty
  stack, then `f ≤*wfˢ lam d Top` at the stack `a ∷ []`. This is Conjecture 8 for one operand, in
  the stack-indexed form ((D) of §28).

**Proved**, from these: `fig4⇒wfˢ : WfCtxˢ Γ → SN Γ t → Γ ⊢ t wf → Γ ∣ [] ⊢ t wfˢ`. The hypothesis
`WfCtxˢ Γ` — every annotation of `Γ` is `wfˢ` at the empty stack in the context below its entry —
is needed because `Wc-PrS` and `Wc-PrE` ask the annotation of a variable well-formed and Figure
4's `Wf-PrS`, `Wf-PrE` do not. The induction hypothesis is used on subterms of `t` only.

Also proved here, with nothing assumed: weakening of the three stack-reading judgements
(`wfˢ-weaken`), which `WfCtxˢ` needs at a lookup.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Fig4ToStackWf where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import MPSS.WellFormed
open import MPSS.StackWf
open import MPSS.StackWfNarrow using (wfˢ-fv)
open import MPSS.StackWfPromotion using (reach-lam-wfˢ)
open import MPSS.StackPush using (prevalid-cons)
open import MPSS.Weakening using (∈-weaken; dom-⊑; ⊲-weaken)
open import MPSS.Static using (⊑*wf⇒wfʳ)
open import MPSS.Unconditional using (Thm-3wf)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Congruence using (subᴸ; trsᴸ)
open import MPSS.VariantTransfer using (Thm-3ᴸ)
open import MPSS.EvalChain using (chain⇒≤)
```

## Weakening of the stack-reading judgements

As `wf-weaken` of `MPSS/Weakening`, with the prevalidity of the enlarged configuration as the
hypothesis. At `Wc-App` the operand goes onto the stack, locally closed and scoped because it is
well-formed; at `Wc-FOp` it comes off the stack into the context.

```agda
wfˢ-weaken   : ∀ (Δ Θ : Ctx) {Γ s t}
             → (Δ ++ Θ ++ Γ) ∣ s prevalid
             → (Δ ++ Γ) ∣ s ⊢ t wfˢ
             → (Δ ++ Θ ++ Γ) ∣ s ⊢ t wfˢ
≤wfˢ-weaken  : ∀ (Δ Θ : Ctx) {Γ s u t}
             → (Δ ++ Θ ++ Γ) ∣ s prevalid
             → (Δ ++ Γ) ∣ s ⊢ u ≤wfˢ t
             → (Δ ++ Θ ++ Γ) ∣ s ⊢ u ≤wfˢ t
≤*wfˢ-weaken : ∀ (Δ Θ : Ctx) {Γ s u t}
             → (Δ ++ Θ ++ Γ) ∣ s prevalid
             → (Δ ++ Γ) ∣ s ⊢ u ≤*wfˢ t
             → (Δ ++ Θ ++ Γ) ∣ s ⊢ u ≤*wfˢ t

wfˢ-weaken Δ Θ pv (Wc-Top _)       = Wc-Top pv
wfˢ-weaken Δ Θ pv (Wc-PrS _ m wt)  = Wc-PrS pv (∈-weaken Δ Θ m) (wfˢ-weaken Δ Θ pv wt)
wfˢ-weaken Δ Θ pv (Wc-PrE _ m wα)  = Wc-PrE pv (∈-weaken Δ Θ m) (wfˢ-weaken Δ Θ pv wα)
wfˢ-weaken Δ Θ {Γ} pv (Wc-Fun {t = t} {u = u} L F wt) =
  Wc-Fun (L ++ dom (Δ ++ Θ ++ Γ)) body (wfˢ-weaken Δ Θ pv wt)
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ∣ [] ⊢ (u ^ fvar y) wfˢ
    body {y} y∉ = wfˢ-weaken ((y , sub , t) ∷ Δ) Θ (Pv-Nil pv′) (F (∉-++ˡ y∉))
      where
        inner : ((y , sub , t) ∷ Δ ++ Γ) prevalid
        inner = prevalid-ctx (wfˢ⇒prevalid (F (∉-++ˡ y∉)))
        pv′ : ((y , sub , t) ∷ Δ ++ Θ ++ Γ) prevalid
        pv′ = Pv-Ctx (prevalid-ctx pv) (∉-++ʳ L y∉) (head-lc inner)
                     (λ h → dom-⊑ Δ Θ (head-fv inner h))
wfˢ-weaken Δ Θ {Γ} pv (Wc-FOp {s = s} {δ = δ} {u = u} L F wt) =
  Wc-FOp (L ++ dom (Δ ++ Θ ++ Γ)) body (wfˢ-weaken Δ Θ (prevalid-nil pv) wt)
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , eqv , δ) ∷ Δ ++ Θ ++ Γ) ∣ s ⊢ (u ^ fvar y) wfˢ
    body {y} y∉ =
      wfˢ-weaken ((y , eqv , δ) ∷ Δ) Θ
                 (prevalid-cons (prevalid-pop pv) (∉-++ʳ L y∉)
                                (prevalid-head-lc pv) (prevalid-head-fv pv))
                 (F (∉-++ˡ y∉))
wfˢ-weaken Δ Θ pv (Wc-App d₁ d₂) =
  Wc-App (≤*wfˢ-weaken Δ Θ (Pv-Sta pv (wfˢ⇒lc wv) (λ h → dom-⊑ Δ Θ (wfˢ-fv wv h))) d₁)
         (≤*wfˢ-weaken Δ Θ (prevalid-nil pv) d₂)
  where
    wv = proj₁ (≤*wfˢ⇒both d₂)

≤wfˢ-weaken Δ Θ pv (Wc-Rule wu wt d) =
  Wc-Rule (wfˢ-weaken Δ Θ pv wu) (wfˢ-weaken Δ Θ pv wt) (⊲-weaken Δ Θ pv d)

≤*wfˢ-weaken Δ Θ pv (Wc-Sub d)     = Wc-Sub (≤wfˢ-weaken Δ Θ pv d)
≤*wfˢ-weaken Δ Θ pv (Wc-Trs d₁ d₂) = Wc-Trs (≤*wfˢ-weaken Δ Θ pv d₁) (≤*wfˢ-weaken Δ Θ pv d₂)

wfˢ-weaken₁ : ∀ {Γ x a w t}
            → ((x , a , w) ∷ Γ) prevalid
            → Γ ∣ [] ⊢ t wfˢ
            → ((x , a , w) ∷ Γ) ∣ [] ⊢ t wfˢ
wfˢ-weaken₁ {x = x} {a} {w} pv d = wfˢ-weaken [] ((x , a , w) ∷ []) (Pv-Nil pv) d
```

## Contexts whose annotations are well-formed

Each annotation is `wfˢ` at the empty stack in the context below its entry. At a lookup it is
weakened to the whole context.

```agda
data WfCtxˢ : Ctx → Set where
  wcˢ-nil  : WfCtxˢ []
  wcˢ-cons : ∀ {Γ x a t} → WfCtxˢ Γ → Γ ∣ [] ⊢ t wfˢ → WfCtxˢ ((x , a , t) ∷ Γ)

WfCtxˢ-lookup : ∀ {Γ x a t} → Γ prevalid → WfCtxˢ Γ → (x , a , t) ∈ Γ → Γ ∣ [] ⊢ t wfˢ
WfCtxˢ-lookup pv (wcˢ-cons wc w) (here refl) = wfˢ-weaken₁ pv w
WfCtxˢ-lookup pv (wcˢ-cons wc w) (there m)   =
  wfˢ-weaken₁ pv (WfCtxˢ-lookup (tail-prevalid pv) wc m)
```

## The theorem

```agda
module Fig4⇒wfˢ
  (SN : Ctx → Tm → Set)
  (sn-app-l : ∀ {Γ f a} → SN Γ (app f a) → SN Γ f)
  (sn-app-r : ∀ {Γ f a} → SN Γ (app f a) → SN Γ a)
  (sn-lam-a : ∀ {Γ t u} → SN Γ (lam t u) → SN Γ t)
  (sn-lam-b : ∀ {Γ t u} → SN Γ (lam t u)
            → ∃[ L ] (∀ {x} → x ∉ L → SN ((x , sub , t) ∷ Γ) (u ^ fvar x)))
  (C8ˢ : ∀ {Γ f a d} → SN Γ (app f a)
       → Γ ∣ [] ⊢ f ≤*wfˢ lam d Top
       → Γ ∣ [] ⊢ a ≤*wfˢ d
       → Γ ∣ (a ∷ []) ⊢ f ≤*wfˢ lam d Top)
  where
```

By induction on the Figure 4 derivation. `fig4ˡ` is the induction hypothesis at the left end of a
well-subtyping, which is where `Wf-App` keeps the derivations for the operator and the operand.

- `Wf-PrS`, `Wf-PrE`: the annotation is well-formed by `WfCtxˢ-lookup`.
- `Wf-Fun`: the annotation by the induction hypothesis; the body by the induction hypothesis in
  the context extended by the annotation, which keeps `WfCtxˢ`.
- `Wf-App`, for `f a` with `Γ ⊢ f ≤*wf lam d Top` and `Γ ⊢ a ≤*wf d`. `f` and `a` are `wfˢ` by the
  induction hypothesis, and the two premises are one-layer machine derivations by `Thm-3wf`. The
  bound `d` is not a subterm of `f a`, so nothing is known about it beyond Figure 4.
  `reach-lam-wfˢ` of `MPSS/StackWfPromotion` replaces it by a `⟶ᵉ*`-reduct `d′` that is `wfˢ`,
  with `f ≤ lam d′ Top`; `a ≤ d′` follows through `d ≤ d′` by `Thm-3ᴸ`. Now both premises of `C8ˢ`
  hold for `d′`, its conclusion is the first premise of `Wc-App`, and its second premise is the
  second.

```agda
  fig4⇒wfˢ : ∀ {Γ t} → WfCtxˢ Γ → SN Γ t → Γ ⊢ t wf → Γ ∣ [] ⊢ t wfˢ
  fig4ˡ    : ∀ {Γ v t m} → WfCtxˢ Γ → SN Γ v → Γ ⊢ v ⊑*wf[ m ] t → Γ ∣ [] ⊢ v wfˢ

  fig4ˡ wc sn (Ws-Sub w _ _) = fig4⇒wfˢ wc sn w
  fig4ˡ wc sn (Ws-Trs d _ _) = fig4ˡ wc sn d

  fig4⇒wfˢ wc sn (Wf-Top pv)   = Wc-Top (Pv-Nil pv)
  fig4⇒wfˢ wc sn (Wf-PrS pv m) = Wc-PrS (Pv-Nil pv) m (WfCtxˢ-lookup pv wc m)
  fig4⇒wfˢ wc sn (Wf-PrE pv m) = Wc-PrE (Pv-Nil pv) m (WfCtxˢ-lookup pv wc m)

  fig4⇒wfˢ wc sn (Wf-Fun L F wt) with sn-lam-b sn
  ... | L′ , snb =
    Wc-Fun (L ++ L′)
           (λ x∉ → fig4⇒wfˢ (wcˢ-cons wc wt′) (snb (∉-++ʳ L x∉)) (F (∉-++ˡ x∉)))
           wt′
    where
      wt′ = fig4⇒wfˢ wc (sn-lam-a sn) wt

  fig4⇒wfˢ {Γ} wc sn (Wf-App {u = f} {v = a} {t = d} d₁ d₂) = result
    where
      wf-f = fig4ˡ wc (sn-app-l sn) d₁
      wf-a = fig4ˡ wc (sn-app-r sn) d₂
      pv   = wfˢ⇒prevalid wf-f

      ann : ∀ {t u} → Γ ⊢ lam t u wf → Γ ⊢ t wf
      ann (Wf-Fun _ _ w) = w

      wd = ann (⊑*wf⇒wfʳ d₁)
      ld = wf⇒lc wd
      fd = wf-fv wd

      result : Γ ∣ [] ⊢ app f a wfˢ
      result with reach-lam-wfˢ ld fd wf-f (Thm-3wf d₁)
      ... | d′ , p , wd′ , f≤ =
        Wc-App (C8ˢ sn (Wc-Sub (Wc-Rule wf-f wλ′ f≤)) (Wc-Sub (Wc-Rule wf-a wd′ a≤)))
               (Wc-Sub (Wc-Rule wf-a wd′ a≤))
        where
          ld′ = wfˢ⇒lc wd′

          a≤ : Γ ∣ [] ⊢ a ≤ d′
          a≤ = Thm-3ᴸ (trsᴸ (subᴸ (wfˢ⇒lc wf-a) ld (Thm-3wf d₂)) ld (subᴸ ld ld′ (chain⇒≤ p)))

          wλ′ : Γ ∣ [] ⊢ lam d′ Top wfˢ
          wλ′ = Wc-Fun (dom Γ)
                       (λ x∉ → Wc-Top (Pv-Nil (Pv-Ctx (prevalid-ctx pv) x∉ ld′ (wfˢ-fv wd′))))
                       wd′
```

## What this establishes

`fig4⇒wfˢ`: in a context whose annotations are `wfˢ` (`WfCtxˢ`), a term that Figure 4 accepts and
that satisfies `SN` is `wfˢ` at the empty stack.

Assumed, as parameters of the module `Fig4⇒wfˢ`: the predicate `SN` with its four closure
properties under immediate subterms (`sn-app-l`, `sn-app-r`, `sn-lam-a`, `sn-lam-b`), and `C8ˢ`.
`SN` is abstract: the proof reads nothing of it but these closure properties, and passes it to
`C8ˢ` at each application. Everything else is proved: weakening of the stack-reading judgements
(`wfˢ-weaken`), the lookup in a `WfCtxˢ` context, the replacement of the bound of an operator by a
well-formed reduct (`reach-lam-wfˢ`, `MPSS/StackWfPromotion`), and the induction. So the question
of §28 is reduced to `C8ˢ` for a notion of termination closed under subterms: from
`f ≤*wfˢ lam d Top` and `a ≤*wfˢ d` at the empty stack, to `f ≤*wfˢ lam d Top` at the stack `a ∷ []`.
