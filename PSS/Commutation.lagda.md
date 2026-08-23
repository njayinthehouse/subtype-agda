# System λ⊲: Theorem 4.5 — `⟶≤` and `⟶≡` strongly commute

The paper's main technical contribution, and what all of §4 rests on.

> If `t₀ ⟶≡ t₁` and `Γ ∣ s ⊢ t₀ ⟶≤ t₂`, then for every reduced extended context
> `Γ ∣ s ↣ Γ' ∣ s'` there is a `t₃` with `t₂ ⟶≡ t₃` and `Γ' ∣ s' ⊢ t₁ ⟶≤ t₃`.

Two things make it work where Hutchins' original did not. The context reduces *along with* the
term — without that, `Srs-Prom` cannot be completed in one step, because the bound found in `Γ`
is the unreduced one. And this system's `Cr-Beta` drops the subtype requirement on redexes that
the original imposed, which is what lets the pathological case close.

Stated over the pointwise `CtxRed`/`StkRed` of `PSS.Scope`; the `↣` form is a corollary.

```agda
{-# OPTIONS --safe #-}

module PSS.Commutation where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed using (fvStack; prevalid-strengthen; prevalid-bound;
                                 prevalid-bound-lc; prevalid-pop)
open import PSS.Close
open import PSS.Equivalence
open import PSS.Diamond
open import PSS.Promotion
open import PSS.Scope
open import PSS.Rename
```

## Two facts about promotion

Every promotion derivation carries prevalidity of its own extended context, and promotion
preserves local closure. `Srs-FunOp` is again the case needing the freshness argument.

```agda
⟶≤-prevalid : ∀ {Γ s u u'} → Γ ∣ s ⊢ u ⟶≤ u' → Γ ∣ s prevalid
⟶≤-prevalid (Srs-Prom pv _) = pv
⟶≤-prevalid (Srs-Top pv)    = pv
⟶≤-prevalid (Srs-Eq pv _)   = pv
⟶≤-prevalid (Srs-App d)     = prevalid-pop (⟶≤-prevalid d)
⟶≤-prevalid (Srs-Fun L F)   = strip (⟶≤-prevalid (F (fresh-∉ L)))
  where
    strip : ∀ {Γ x t} → ((x , t) ∷ Γ) ∣ [] prevalid → Γ ∣ [] prevalid
    strip (P-Ctx2 p _ _ _) = p
⟶≤-prevalid (Srs-FunOp {Γ} {s} {α} L F) =
  P-Ctx3 (prevalid-strengthen x∉stk pv) (prevalid-bound-lc pv) (prevalid-bound pv)
  where
    x     = fresh (L ++ fvStack s)
    x∉L   = ∉-++ˡ (fresh-∉ (L ++ fvStack s))
    x∉stk = ∉-++ʳ L (fresh-∉ (L ++ fvStack s))
    pv    = ⟶≤-prevalid (F x∉L)

⟶≤-lc : ∀ {Γ s u u'} → LC u → Γ ∣ s ⊢ u ⟶≤ u' → LC u'
⟶≤-lc lu (Srs-Prom pv mem)              = prevalid-entry-lc (prevalid-nil pv) mem
⟶≤-lc lu (Srs-Top _)                    = lc-Top
⟶≤-lc lu (Srs-Eq _ e)                   = ⟶≡-lc lu e
⟶≤-lc (lc-app lu lv) (Srs-App d)        = lc-app (⟶≤-lc lu d) lv
⟶≤-lc (lc-lam L₀ la F₀) (Srs-Fun L F)   =
  lc-lam (L₀ ++ L) la (λ {y} y∉ → ⟶≤-lc (F₀ (∉-++ˡ y∉)) (F (∉-++ʳ L₀ y∉)))
⟶≤-lc (lc-lam L₀ la F₀) (Srs-FunOp L F) =
  lc-lam (L₀ ++ L) la (λ {y} y∉ → ⟶≤-lc (F₀ (∉-++ˡ y∉)) (F (∉-++ʳ L₀ y∉)))

fv-stack-head : ∀ {Γ s v} → Γ ∣ (v ∷ s) prevalid → fv v ⊑ dom Γ
fv-stack-head (P-Ctx3 _ _ f) = f
```

## The theorem

```agda
Thm-4·5 : ∀ {Γ s Γ' s' t₀ t₁ t₂}
        → LC t₀
        → CtxRed Γ Γ'
        → StkRed s s'
        → t₀ ⟶≡ t₁
        → Γ ∣ s ⊢ t₀ ⟶≤ t₂
        → ∃[ t₃ ] ((t₂ ⟶≡ t₃) × (Γ' ∣ s' ⊢ t₁ ⟶≤ t₃))
```

**Anything promotes to `Top`**, and `Top` is already joined. **`Srs-Eq`** puts both edges in
`⟶≡`, so the diamond closes the square.

```agda
Thm-4·5 lt cr sr e (Srs-Top pv) =
  Top , Cr-Top , Srs-Top (prevalid-red pv cr sr)

Thm-4·5 lt cr sr e (Srs-Eq pv f) with ⟶≡-diamond lt e f
... | t₃ , p , q = t₃ , q , Srs-Eq (prevalid-red pv cr sr) p
```

**`Srs-Prom`** — the source is a variable, so the equivalence edge is `Cr-Var`. The bound is
looked up in `Γ'`, where it appears reduced, and that reduct completes the square. This is the
case the reduced context exists for.

```agda
Thm-4·5 lt cr sr Cr-Var (Srs-Prom pv mem) with CtxRed-lookup cr mem
... | t' , mem' , st = t' , st , Srs-Prom (prevalid-red pv cr sr) mem'
```

**Congruence against `Srs-App`** — push the operand and recurse; the operand's reduction is
what extends `StkRed`.

```agda
Thm-4·5 (lc-app lu lv) cr sr (Cr-App {u} {u₁} {v} {v₁} e₁ e₂) (Srs-App d)
  with Thm-4·5 lu cr (sr-cons sr e₂) e₁ d
... | u₃ , p , q = app u₃ v₁ , Cr-App p e₂ , Srs-App q
```

**`Top` applied** — the operator can only promote to `Top`, so both edges land there.

```agda
Thm-4·5 lt cr sr Cr-TopApp (Srs-App (Srs-Top pv)) =
  Top , Cr-TopApp , Srs-Top (prevalid-red (prevalid-pop pv) cr sr)
Thm-4·5 lt cr sr Cr-TopApp (Srs-App (Srs-Eq pv Cr-Top)) =
  Top , Cr-TopApp , Srs-Top (prevalid-red (prevalid-pop pv) cr sr)
```

**The pathological case** — the equivalence edge contracts the redex while the promotion edge
pushed the operand into the context. Three shapes for the operator's promotion; the third is
the one Hutchins' system could not close.

```agda
Thm-4·5 lt cr sr (Cr-Beta L₁ F₁ sv) (Srs-App (Srs-Top pv)) =
  Top , Cr-TopApp , Srs-Top (prevalid-red (prevalid-pop pv) cr sr)

Thm-4·5 (lc-app llam lv) cr sr (Cr-Beta {a} {b} {b₁} {v} {v₁} L₁ F₁ sv)
        (Srs-App (Srs-Eq pv f))
  with ⟶≡-diamond (lc-app llam lv)
                  (Cr-Beta {a} {b} {b₁} {v} {v₁} L₁ F₁ sv)
                  (Cr-App f (⟶≡-refl lv))
... | t₃ , p , q = t₃ , q , Srs-Eq (prevalid-red (prevalid-pop pv) cr sr) p

Thm-4·5 {Γ} {s} {Γ'} {s'} (lc-app (lc-lam {a} {b} L₀ la F₀) lv) cr sr
        (Cr-Beta {_} {_} {b₁} {v} {v₁} L₁ F₁ sv)
        (Srs-App inner@(Srs-FunOp {_} {_} {_} {_} {_} {b'} L' F')) =
  (b₃ ^ v₁)
  , Cr-Beta {a} {b'} {b₃} {v} {v₁} [] (λ {y} _ → close-rename {b'} {w} x y lw x∉b' sw) sv
  , right
  where
    A  = L₀ ++ L₁ ++ L' ++ fv b₁ ++ fv b' ++ fv v₁ ++ fvStack s'
    x  = fresh A
    a∉ = fresh-∉ A

    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L₁ r₁
    r₃ = ∉-++ʳ L' r₂
    r₄ = ∉-++ʳ (fv b₁) r₃
    r₅ = ∉-++ʳ (fv b') r₄

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ r₁
    x∉L' = ∉-++ˡ r₂

    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ r₃
    x∉b' : x ∉ fv b'
    x∉b' = ∉-++ˡ r₄
    x∉v₁ : x ∉ fv v₁
    x∉v₁ = ∉-++ˡ r₅
    x∉s' : x ∉ fvStack s'
    x∉s' = ∉-++ʳ (fv v₁) r₅

    lv₁ : LC v₁
    lv₁ = ⟶≡-lc lv sv

    fvv₁ : fv v₁ ⊑ dom Γ'
    fvv₁ h = subst (_ ∈_) (sym (CtxRed-dom cr))
                   (fv-stack-head (⟶≤-prevalid inner) (fv-⟶≡ sv h))

    ih = Thm-4·5 (F₀ x∉L₀) (cr-cons cr sv) sr (F₁ x∉L₁) (F' x∉L')

    w  = proj₁ ih
    sw = proj₁ (proj₂ ih)
    dw = proj₂ (proj₂ ih)

    lw : LC w
    lw = ⟶≡-lc (⟶≤-lc (F₀ x∉L₀) (F' x∉L')) sw

    b₃ = closeRec 0 x w

    dw' : ((x , v₁) ∷ Γ') ∣ s' ⊢ (b₁ ^ fvar x) ⟶≤ (b₃ ^ fvar x)
    dw' rewrite open-close lw 0 x = dw

    right₀ : Γ' ∣ substStack x v₁ s' ⊢ (b₁ ^ v₁) ⟶≤ (b₃ ^ v₁)
    right₀ rewrite subst-intro {b₁} lv₁ x x∉b₁
                 | subst-intro {b₃} lv₁ x (fv-close 0 x w)
                 = ⟶≤-subst x [] lv₁ x∉v₁ fvv₁ dw'

    right : Γ' ∣ s' ⊢ (b₁ ^ v₁) ⟶≤ (b₃ ^ v₁)
    right = subst (λ σ → Γ' ∣ σ ⊢ (b₁ ^ v₁) ⟶≤ (b₃ ^ v₁))
                  (substStack-id x v₁ s' x∉s') right₀
```

**Congruence under a binder** — unapplied and applied. Both join the bodies by the induction
hypothesis at one fresh name, close the join into a body, and rename to produce the cofinite
family the promotion rule demands.

```agda
Thm-4·5 {Γ} {_} {Γ'} (lc-lam {a} {b} L₀ la F₀) cr sr-nil
        (Cr-Fun {_} {a₁} {_} {b₁} L₁ sa F₁)
        (Srs-Fun {_} {_} {_} {b'} L' F') =
  lam a₁ b₃
  , Cr-Fun {a} {a₁} {b'} {b₃} [] sa (λ {y} _ → close-rename {b'} {w} x y lw x∉b' sw)
  , Srs-Fun (x ∷ dom Γ') right
  where
    A  = L₀ ++ L₁ ++ L' ++ fv b₁ ++ fv b' ++ fv a₁
    x  = fresh A
    a∉ = fresh-∉ A

    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L₁ r₁
    r₃ = ∉-++ʳ L' r₂
    r₄ = ∉-++ʳ (fv b₁) r₃

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ r₁
    x∉L' = ∉-++ˡ r₂

    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ r₃
    x∉b' : x ∉ fv b'
    x∉b' = ∉-++ˡ r₄
    x∉a₁ : x ∉ fv a₁
    x∉a₁ = ∉-++ʳ (fv b') r₄

    ih = Thm-4·5 (F₀ x∉L₀) (cr-cons cr sa) sr-nil (F₁ x∉L₁) (F' x∉L')

    w  = proj₁ ih
    sw = proj₁ (proj₂ ih)
    dw = proj₂ (proj₂ ih)

    lw : LC w
    lw = ⟶≡-lc (⟶≤-lc (F₀ x∉L₀) (F' x∉L')) sw

    b₃ = closeRec 0 x w

    right : ∀ {y} → y ∉ (x ∷ dom Γ')
          → ((y , a₁) ∷ Γ') ∣ [] ⊢ (b₁ ^ fvar y) ⟶≤ (b₃ ^ fvar y)
    right {y} y∉ =
      ⟶≤-rename-head {Γ'} {[]} {b₁} {w} {a₁} x y
                     (∉-tail y∉) (λ p → y∉ (here p)) x∉a₁ x∉b₁ lw dw (λ ())

Thm-4·5 {Γ} {_} {Γ'} (lc-lam {a} {b} L₀ la F₀) cr (sr-cons {s₀} {s₀'} {δ} {δ'} sr₀ sδ)
        (Cr-Fun {_} {a₁} {_} {b₁} L₁ sa F₁)
        (Srs-FunOp {_} {_} {_} {_} {_} {b'} L' F') =
  lam a₁ b₃
  , Cr-Fun {a} {a₁} {b'} {b₃} [] sa (λ {y} _ → close-rename {b'} {w} x y lw x∉b' sw)
  , Srs-FunOp (x ∷ dom Γ') right
  where
    A  = L₀ ++ L₁ ++ L' ++ fv b₁ ++ fv b' ++ fv δ' ++ fvStack s₀'
    x  = fresh A
    a∉ = fresh-∉ A

    r₁ = ∉-++ʳ L₀ a∉
    r₂ = ∉-++ʳ L₁ r₁
    r₃ = ∉-++ʳ L' r₂
    r₄ = ∉-++ʳ (fv b₁) r₃
    r₅ = ∉-++ʳ (fv b') r₄

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ r₁
    x∉L' = ∉-++ˡ r₂

    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ r₃
    x∉b' : x ∉ fv b'
    x∉b' = ∉-++ˡ r₄
    x∉δ' : x ∉ fv δ'
    x∉δ' = ∉-++ˡ r₅
    x∉s₀' : x ∉ fvStack s₀'
    x∉s₀' = ∉-++ʳ (fv δ') r₅

    ih = Thm-4·5 (F₀ x∉L₀) (cr-cons cr sδ) sr₀ (F₁ x∉L₁) (F' x∉L')

    w  = proj₁ ih
    sw = proj₁ (proj₂ ih)
    dw = proj₂ (proj₂ ih)

    lw : LC w
    lw = ⟶≡-lc (⟶≤-lc (F₀ x∉L₀) (F' x∉L')) sw

    b₃ = closeRec 0 x w

    right : ∀ {y} → y ∉ (x ∷ dom Γ')
          → ((y , δ') ∷ Γ') ∣ s₀' ⊢ (b₁ ^ fvar y) ⟶≤ (b₃ ^ fvar y)
    right {y} y∉ =
      ⟶≤-rename-head {Γ'} {s₀'} {b₁} {w} {δ'} x y
                     (∉-tail y∉) (λ p → y∉ (here p)) x∉δ' x∉b₁ lw dw x∉s₀'
```

## The `↣` form

```agda
red⇒↣ : ∀ {Γ Γ' s s'} → CtxRed Γ Γ' → StkRed s s' → Γ ∣ s ↣ Γ' ∣ s'
red⇒↣ cr (sr-cons sr st)     = Ctx-Stack (red⇒↣ cr sr) st
red⇒↣ cr-nil sr-nil          = Ctx-Refl
red⇒↣ (cr-cons cr st) sr-nil = Ctx-Annotation (red⇒↣ cr sr-nil) st

Thm-4·5-↣ : ∀ {Γ s Γ' s' t₀ t₁ t₂}
          → LC t₀
          → t₀ ⟶≡ t₁
          → Γ ∣ s ⊢ t₀ ⟶≤ t₂
          → Γ ∣ s ↣ Γ' ∣ s'
          → ∃[ t₃ ] ((t₂ ⟶≡ t₃) × (Γ' ∣ s' ⊢ t₁ ⟶≤ t₃))
Thm-4·5-↣ lt e d r =
  Thm-4·5 lt (↣-ctx (prevalid-nil (⟶≤-prevalid d)) r)
             (↣-stk (prevalid-stkLC (⟶≤-prevalid d)) r) e d
```

## What this establishes

**Theorem 4.5.** The load-bearing lemma named in `../PLAN.md`. Transitivity elimination
(Theorem 4.4) follows, and with it no-supertype-of-`Top` (4.3), progress (4.1) and preservation
(4.2).
