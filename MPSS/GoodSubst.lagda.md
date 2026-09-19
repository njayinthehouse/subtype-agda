# MPSS: good substitutions, and the semantic form of a well-formedness derivation

Second module of the reducibility argument's fundamental lemma (`MPSS/CONJ8.md` §17), under the
parameter of `MPSS/GoodAt` (every well-formed term is ranked — false in full MPSS; see there).

- A substitution `θ : Γ ⇒ Γ′` (`MPSS/Morphism`) is **good** when every `x ≤ t ∈ Γ` has `xθ` good
  at `tθ` in `Γ′`, and every `≡`-bound name has a well-formed image. The identity is good on a
  context with well-formed annotations (`WfCtx`) — this is where that premise is used. A good
  substitution lifts under a binder, extends by a good term for the bound name (`mor-inst`), and
  extends at the head by an operand good at the annotation (`mor-head`).
- `SW Γ m` is what the fundamental lemma makes of a derivation of `Γ ⊢ m wf`: at each
  application, the operator and the operand are good at the domain's abstraction and the domain
  under every good substitution; at each abstraction, the same for the body. It is a datatype so
  that the lemma for one promotion can invert it while recursing on the promotion alone.
  `img`: under a good substitution the image is well-formed (Lemma 7, in this form).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

open import MPSS.WellFormed
open import MPSS.DomainOrder using (Ranked)

module MPSS.GoodSubst (rk : ∀ {Γ T} → Γ ⊢ T wf → Ranked Γ T) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import MPSS.GoodAt rk
open import MPSS.Morphism
open import MPSS.WfCtx using (WfCtx; wc-nil; wc-sub; wc-eqv; WfCtx⇒prevalid)
open import MPSS.Weakening using (wf-weaken)
open import MPSS.Narrow using (wf-fv)
open import MPSS.Rename using (head-∉)
open import PSS.Syntax
  using (subst-fvar-≡; subst-fvar-≢; subst-fresh; ∉-++ˡ; ∉-++ʳ)
```

## Good substitutions

```agda
record Mor (Γ : Ctx) (θ : Sub) (Γ′ : Ctx) : Set where
  field
    mor  : Γ ⊢ θ ⇒ Γ′
    pvs  : Γ prevalid
    subs : ∀ {x t} → x ≤ t ∈ Γ → G Γ′ (act θ (fvar x)) (act θ t)
    eqvs : ∀ {x β} → x ≐ β ∈ Γ → Γ′ ⊢ act θ (fvar x) wf

  pvt : Γ′ prevalid
  pvt = prevalid-ctx (m-pv mor (Pv-Nil pvs))

open Mor public
```

The identity, on a context with well-formed annotations.

```agda
ann-wf : ∀ {Γ x a t} → WfCtx Γ → (x , a , t) ∈ Γ → Γ ⊢ t wf
ann-wf c@(wc-sub c′ _ w) (here refl) = wf-weaken [] (_ ∷ []) (WfCtx⇒prevalid c) w
ann-wf c@(wc-eqv c′ _ w) (here refl) = wf-weaken [] (_ ∷ []) (WfCtx⇒prevalid c) w
ann-wf c@(wc-sub c′ _ _) (there h)   = wf-weaken [] (_ ∷ []) (WfCtx⇒prevalid c) (ann-wf c′ h)
ann-wf c@(wc-eqv c′ _ _) (there h)   = wf-weaken [] (_ ∷ []) (WfCtx⇒prevalid c) (ann-wf c′ h)

mor-id : ∀ {Γ} → WfCtx Γ → Mor Γ [] Γ
mor-id c = record
  { mor  = m-id
  ; pvs  = pv
  ; subs = λ h → G-var pv h (ann-wf c h)
  ; eqvs = λ h → Wf-PrE pv h
  }
  where pv = WfCtx⇒prevalid c
```

Under a binder.

```agda
mor-up : ∀ {Γ θ Γ′ z t} (M : Mor Γ θ Γ′) → z ∉ names (mor M)
       → ((z , sub , t) ∷ Γ) prevalid → Γ′ ⊢ act θ t wf
       → Mor ((z , sub , t) ∷ Γ) θ ((z , sub , act θ t) ∷ Γ′)
mor-up {Γ} {θ} {Γ′} {z} {t} M z∉ pv wt = record
  { mor  = m′
  ; pvs  = pv
  ; subs = sb
  ; eqvs = eq
  }
  where
    m′  = up z t (mor M) z∉ pv
    pv′ : ((z , sub , act θ t) ∷ Γ′) prevalid
    pv′ = prevalid-ctx (m-pv m′ (Pv-Nil pv))
    e   = (z , sub , act θ t)

    sb : ∀ {x t₁} → x ≤ t₁ ∈ ((z , sub , t) ∷ Γ) → G (e ∷ Γ′) (act θ (fvar x)) (act θ t₁)
    sb (here refl) =
      subst (λ q → G (e ∷ Γ′) q (act θ t)) (sym (act-fvar (mor M) z∉))
            (G-var pv′ (here refl) (wf-weaken [] (e ∷ []) pv′ wt))
    sb (there h)   = G-weaken (e ∷ []) pv′ (subs M h)

    eq : ∀ {x β} → x ≐ β ∈ ((z , sub , t) ∷ Γ) → (e ∷ Γ′) ⊢ act θ (fvar x) wf
    eq (there h) = wf-weaken [] (e ∷ []) pv′ (eqvs M h)
```

Extending by a good term for a bound name, into an extension of the target.

```agda
mor-inst : ∀ {Γ θ Γ′ z t v} (M : Mor Γ θ Γ′) (Δ : Ctx)
         → z ∉ names (mor M) → z ∉ dom (Δ ++ Γ′)
         → ((z , sub , t) ∷ Γ) prevalid → (Δ ++ Γ′) prevalid
         → G (Δ ++ Γ′) v (act θ t)
         → Mor ((z , sub , t) ∷ Γ) (θ ++ (z , v) ∷ []) (Δ ++ Γ′)
mor-inst {Γ} {θ} {Γ′} {z} {t} {v} M Δ z∉ z∉Δ pv pvΔ gv = record
  { mor  = inst (mor M) Δ z∉ z∉Δ pv pvΔ lv (wf-fv wv)
  ; pvs  = pv
  ; subs = sb
  ; eqvs = eq
  }
  where
    wv = G-wf gv
    lv = wf⇒lc wv
    θ′ = θ ++ (z , v) ∷ []
    z∉Γ = head-∉ pv

    keep : ∀ {y a w} → (y , a , w) ∈ Γ → (act θ′ (fvar y) ≡ act θ (fvar y)) × (act θ′ w ≡ act θ w)
    keep {y} {a} {w} h =
        act-snoc-fresh (mor M) z∉ (fvar y) (λ { (here p) → z∉Γ (subst (_∈ dom Γ) (sym p) (∈-dom h)) })
      , act-snoc-fresh (mor M) z∉ w (λ q → z∉Γ (prevalid-bound-fv (tail-prevalid pv) h q))

    sb : ∀ {x t₁} → x ≤ t₁ ∈ ((z , sub , t) ∷ Γ) → G (Δ ++ Γ′) (act θ′ (fvar x)) (act θ′ t₁)
    sb (here refl) =
      subst₂ (G (Δ ++ Γ′))
             (sym (trans (act-++ θ ((z , v) ∷ []) (fvar z))
                         (trans (cong (_[ z := v ]) (act-fvar (mor M) z∉)) (subst-fvar-≡ {z} v))))
             (sym (act-snoc-fresh (mor M) z∉ t (λ q → z∉Γ (head-fv pv q))))
             gv
    sb (there h) =
      subst₂ (G (Δ ++ Γ′)) (sym (proj₁ (keep h))) (sym (proj₂ (keep h)))
             (G-weaken Δ pvΔ (subs M h))

    eq : ∀ {x β} → x ≐ β ∈ ((z , sub , t) ∷ Γ) → (Δ ++ Γ′) ⊢ act θ′ (fvar x) wf
    eq (there h) =
      subst (λ q → (Δ ++ Γ′) ⊢ q wf) (sym (proj₁ (keep h))) (wf-weaken [] Δ pvΔ (eqvs M h))
```

Extending at the head by an operand good at the annotation — the substitution a consumed
abstraction makes.

```agda
mor-head : ∀ {Γ θ Γ′ z t α} (M : Mor Γ θ Γ′)
         → ((z , sub , t) ∷ Γ) prevalid → LC α → fv α ⊑ dom Γ
         → G Γ′ (act θ α) (act θ t)
         → Mor ((z , sub , t) ∷ Γ) ((z , α) ∷ θ) Γ′
mor-head {Γ} {θ} {Γ′} {z} {t} {α} M pv lα fα gα = record
  { mor  = m-sub [] lα fα (mor M)
  ; pvs  = pv
  ; subs = sb
  ; eqvs = eq
  }
  where
    z∉Γ = head-∉ pv

    keepv : ∀ {y a w} → (y , a , w) ∈ Γ → (fvar y) [ z := α ] ≡ fvar y
    keepv {y} h = subst-fvar-≢ {z} {y} α (λ p → z∉Γ (subst (_∈ dom Γ) (sym p) (∈-dom h)))

    keepw : ∀ {y a w} → (y , a , w) ∈ Γ → w [ z := α ] ≡ w
    keepw {w = w} h = subst-fresh {w} z α (λ q → z∉Γ (prevalid-bound-fv (tail-prevalid pv) h q))

    sb : ∀ {x t₁} → x ≤ t₁ ∈ ((z , sub , t) ∷ Γ) → G Γ′ (act θ ((fvar x) [ z := α ])) (act θ (t₁ [ z := α ]))
    sb (here refl) =
      subst₂ (G Γ′) (cong (act θ) (sym (subst-fvar-≡ {z} α)))
             (cong (act θ) (sym (subst-fresh {t} z α (λ q → z∉Γ (head-fv pv q)))))
             gα
    sb (there h) =
      subst₂ (G Γ′) (cong (act θ) (sym (keepv h))) (cong (act θ) (sym (keepw h))) (subs M h)

    eq : ∀ {x β} → x ≐ β ∈ ((z , sub , t) ∷ Γ) → Γ′ ⊢ act θ ((fvar x) [ z := α ]) wf
    eq (there h) = subst (λ q → Γ′ ⊢ q wf) (cong (act θ) (sym (keepv h))) (eqvs M h)
```

## The semantic form of a well-formedness derivation

```agda
Sem≤ : Ctx → Tm → Tm → Set
Sem≤ Γ a b = ∀ {θ Γ′} → Mor Γ θ Γ′ → G Γ′ (act θ a) (act θ b)

data SW (Γ : Ctx) : Tm → Set where
  sw-var : ∀ {x} → Γ ⊢ fvar x wf
         → (∀ {θ Γ′} → Mor Γ θ Γ′ → Γ′ ⊢ act θ (fvar x) wf) → SW Γ (fvar x)
  sw-top : Γ prevalid → SW Γ Top
  sw-lam : ∀ {t u} (L : List Name) → SW Γ t
         → (∀ {z} → z ∉ L → SW ((z , sub , t) ∷ Γ) (u ^ fvar z)) → SW Γ (lam t u)
  sw-app : ∀ {f v d} → Γ ⊢ app f v wf → SW Γ f → SW Γ v
         → Sem≤ Γ f (lam d Top) → Sem≤ Γ v d → SW Γ (app f v)

sw-orig : ∀ {Γ m} → SW Γ m → Γ ⊢ m wf
sw-orig (sw-var w _)        = w
sw-orig (sw-top pv)         = Wf-Top pv
sw-orig (sw-lam L swt body) = Wf-Fun L (λ z∉ → sw-orig (body z∉)) (sw-orig swt)
sw-orig (sw-app w _ _ _ _)  = w

act-lamTop : ∀ θ d → act θ (lam d Top) ≡ lam (act θ d) Top
act-lamTop θ d = trans (act-lam θ d Top) (cong (lam (act θ d)) (act-Top θ))

img : ∀ {Γ m θ Γ′} → SW Γ m → Mor Γ θ Γ′ → Γ′ ⊢ act θ m wf
img (sw-var _ f) M = f M
img {θ = θ} (sw-top _) M = subst (λ q → _ ⊢ q wf) (sym (act-Top θ)) (Wf-Top (pvt M))
img {Γ} {θ = θ} {Γ′} (sw-lam {t} {u} L swt body) M =
  subst (λ q → Γ′ ⊢ q wf) (sym (act-lam θ t u))
        (Wf-Fun (L ++ names (mor M))
                (λ {z} z∉ → subst (λ q → ((z , sub , act θ t) ∷ Γ′) ⊢ q wf)
                                  (act-open (mor M) (∉-++ʳ L z∉) u)
                                  (img (body (∉-++ˡ z∉))
                                       (mor-up M (∉-++ʳ L z∉) (wf⇒prevalid (sw-orig (body (∉-++ˡ z∉)))) wt)))
                wt)
  where wt = img swt M
img {θ = θ} {Γ′} (sw-app {f} {v} {d} _ swf swv semf semv) M =
  subst (λ q → Γ′ ⊢ q wf) (sym (act-app θ f v))
        (Wf-App (subst (λ q → Γ′ ⊢ act θ f ≤*wf q) (act-lamTop θ d) (G-≤ (semf M)))
                (G-≤ (semv M)))
```

## What this establishes

Good substitutions with the four ways of making one, and `SW` with `img`. The lemma for a
promotion and the fundamental lemma are `MPSS/Fundamental`'s.
