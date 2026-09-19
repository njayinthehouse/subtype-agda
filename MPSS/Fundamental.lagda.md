# MPSS: the fundamental lemma of the reducibility argument

Third module (`MPSS/CONJ8.md` §17), under the parameter of `MPSS/GoodAt` — every well-formed term
is ranked, which is false in full MPSS; see there for what that means for the result.

- **The promotion lemma** (`STEP`), by induction on `Γᵉ ∣ s ⊢ p ⟶ˢ p′`: under a good substitution
  `θ`, the spine `(p s)θ` is good at `(p′ s)θ`. The reductions run in a context `Γᵉ` that has `≡`
  where the well-formedness context `Γˢ` has `≤` (a consumed abstraction binds its parameter to
  the operand); `θ` relates both to the same target and acts the same on terms.
- **The fundamental lemma** (`FL-wf`, `FL-sub`), by induction on derivations: a derivation of
  `Γ ⊢ m wf` gives `SW Γ m`, and one of `Γ ⊢ a ≤*wf b` gives `aθ` good at `bθ` for every good `θ`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

open import MPSS.WellFormed
open import MPSS.DomainOrder using (Ranked)

module MPSS.Fundamental (rk : ∀ {Γ T} → Γ ⊢ T wf → Ranked Γ T) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import MPSS.GoodAt rk
open import MPSS.GoodSubst rk
open import MPSS.Morphism
open import MPSS.Conjecture8 using (op-wf)
open import MPSS.Conjecture8Star using (app-wf-mid)
open import MPSS.Conj8Reduction using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_; arg-wf)
open import MPSS.CoFun using (FunCongr)
open import MPSS.Prop17Chain using (Prop-17ʷ; _⊢_⟶ᵉ*wf_; εʷ; step)
open import MPSS.Unconditional using (Lem-10)
open import MPSS.Weakening using (wf-weaken; ⊑*wf-weaken)
open import MPSS.Rename using (substStack-id)
import MPSS.Narrow
open import PSS.Syntax using (subst-intro; fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ)
```

## Small things

```agda
forget : ∀ {Γ a c} → Γ ⊢ a ⟶ᵉ*wf c → Γ ∣ [] ⊢ a ⟶ᵉ* c
forget (εʷ _)       = εᵉ
forget (step e _ p) = e ◅ᵉ forget p

_◅◅ᵉ_ : ∀ {Γ a b c} → Γ ∣ [] ⊢ a ⟶ᵉ* b → Γ ∣ [] ⊢ b ⟶ᵉ* c → Γ ∣ [] ⊢ a ⟶ᵉ* c
εᵉ       ◅◅ᵉ q = q
(e ◅ᵉ p) ◅◅ᵉ q = e ◅ᵉ (p ◅◅ᵉ q)

split-eqv : ∀ {Γ a b} → Γ ⊢ a ⊑wf[ eqv-m ] b → ∃[ c ] ((Γ ∣ [] ⊢ a ⟶ᵉ* c) × (Γ ∣ [] ⊢ b ⟶ᵉ* c))
split-eqv (Ws-Rfl _)   = _ , εᵉ , εᵉ
split-eqv (Ws-Lf1 e d) with split-eqv d
... | c , L , R = c , e ◅ᵉ L , R
split-eqv (Ws-Rgh d e) with split-eqv d
... | c , L , R = c , L , e ◅ᵉ R

stack-top : ∀ {Γ α s} → Γ ∣ (α ∷ s) prevalid → LC α × (fv α ⊑ dom Γ)
stack-top (Pv-Sta _ lα fα) = lα , fα

G-sp : ∀ {Γ} P P′ S {P₁ P′₁ S₁} → P ≡ P₁ → P′ ≡ P′₁ → S ≡ S₁
     → G Γ (app* P S) (app* P′ S) → G Γ (app* P₁ S₁) (app* P′₁ S₁)
G-sp P P′ S refl refl refl g = g

wf-sp : ∀ {Γ} P S {P₁ S₁} → P ≡ P₁ → S ≡ S₁ → Γ ⊢ app* P S wf → Γ ⊢ app* P₁ S₁ wf
wf-sp P S refl refl w = w

ops-sp : ∀ {Γ P P₁ S S₁} → P ≡ P₁ → S ≡ S₁ → Ops Γ P S → Ops Γ P₁ S₁
ops-sp refl refl o = o
```

The operand an abstraction is applied to is good at the abstraction's annotation: it is good at
a domain, and the two are equivalent (Lemma 10).

```agda
op-at-ann : ∀ {Γ T U A S} → Ops Γ (lam T U) (A ∷ S) → G Γ A T
op-at-ann (o-cons e gα _) with ⊑*wf⇒wfˡ e | split-eqv (Lem-10 e)
... | Wf-Fun _ _ wT | c , L , R = G-cast gα R L wT
```

Two spines headed by β-redexes on the same operand are good if the spines of the contracta are.

```agda
β-close : ∀ {Γ T U U′ A B B₀} S
        → Γ ⊢ app* (app (lam T U) A) S wf → Ops Γ (lam T U′) (A ∷ S)
        → B ≡ U ^ A → B₀ ≡ U′ ^ A → Γ ⊢ B wf → Γ ⊢ B₀ wf
        → (Γ ⊢ app* B S wf → Ops Γ B₀ S → G Γ (app* B S) (app* B₀ S))
        → G Γ (app* (app (lam T U) A) S) (app* (app (lam T U′) A) S)
β-close S wA (o-cons _ _ ops₁) refl refl wB wB₀ k =
  head-close S wA L (ops-wf ops₁) R (k (spine-reduct-wf S wA L wB) (ops-reduct R wB₀ ops₁))
  where
    wH  = spine-head S wA
    wH′ = ops-head ops₁
    L = forget (Prop-17ʷ wH  (E-App (wf⇒lc (op-wf wH))  (wf⇒lc (arg-wf wH)))  wB)
    R = forget (Prop-17ʷ wH′ (E-App (wf⇒lc (op-wf wH′)) (wf⇒lc (arg-wf wH′))) wB₀)
```

## The two contexts of a promotion

```agda
record Link (Γᵉ Γˢ : Ctx) : Set where
  field
    link≤   : ∀ {x t} → x ≤ t ∈ Γᵉ → x ≤ t ∈ Γˢ
    linkdom : dom Γᵉ ⊑ dom Γˢ
open Link

link-id : ∀ {Γ} → Link Γ Γ
link-id = record { link≤ = λ h → h ; linkdom = λ h → h }

link-sub : ∀ {Γᵉ Γˢ z t} → Link Γᵉ Γˢ → Link ((z , sub , t) ∷ Γᵉ) ((z , sub , t) ∷ Γˢ)
link-sub lk = record
  { link≤   = λ { (here p) → here p ; (there h) → there (link≤ lk h) }
  ; linkdom = λ { (here p) → here p ; (there h) → there (linkdom lk h) } }

link-eqv : ∀ {Γᵉ Γˢ z t α} → Link Γᵉ Γˢ → Link ((z , eqv , α) ∷ Γᵉ) ((z , sub , t) ∷ Γˢ)
link-eqv lk = record
  { link≤   = λ { (there h) → there (link≤ lk h) }
  ; linkdom = λ { (here p) → here p ; (there h) → there (linkdom lk h) } }
```

## The promotion lemma

```agda
top-case : ∀ {Γ P T} S → T ≡ Top → Γ ⊢ app* P S wf → Ops Γ T S → G Γ (app* P S) (app* T S)
top-case []      refl w ops = G-top w
top-case (v ∷ S) refl w ops = ops-top ops

STEP : ∀ {Γᵉ Γˢ s p p′ θ Γ′}
     → Γᵉ ∣ s ⊢ p ⟶ˢ p′
     → (mᵉ : Γᵉ ⊢ θ ⇒ Γ′) (M : Mor Γˢ θ Γ′) → Link Γᵉ Γˢ
     → SW Γˢ p → SW Γˢ p′
     → Γ′ ⊢ app* (act θ p) (actS θ s) wf → Ops Γ′ (act θ p′) (actS θ s)
     → G Γ′ (app* (act θ p) (actS θ s)) (app* (act θ p′) (actS θ s))

STEP (Ms-Pro pv m) mᵉ M lk swp swp′ wA ops = spine-good (subs M (link≤ lk m)) ops

STEP {s = s} {θ = θ} (Ms-Top pv) mᵉ M lk swp swp′ wA ops = top-case (actS θ s) (act-Top θ) wA ops

STEP {s = s} {θ = θ} (Ms-Equ pv e) mᵉ M lk swp swp′ wA ops =
  G-join wA (frame-e (actS θ s) (m-e mᵉ e) ◅ᵉ εᵉ) εᵉ (ops-wf ops)

STEP {s = s} {θ = θ} {Γ′} (Ms-App {u = u} {u′} {v} d) mᵉ M lk
     (sw-app _ swu _ _ _) (sw-app {d = dd} _ swu′ _ semf semv) wA ops =
  G-sp (app (act θ u) (act θ v)) (app (act θ u′) (act θ v)) (actS θ s) (sym eqP) (sym eqP′) refl
       (G-sp (act θ u) (act θ u′) (actS θ (v ∷ s)) refl refl eqS ih)
  where
    eqS  = actS-cons θ v s
    eqP  = act-app θ u v
    eqP′ = act-app θ u′ v
    e′   : Γ′ ⊢ act θ u′ ≤*wf lam (act θ dd) Top
    e′   = subst (λ q → Γ′ ⊢ act θ u′ ≤*wf q) (act-lamTop θ dd) (G-≤ (semf M))
    ops₂ : Ops Γ′ (act θ u′) (act θ v ∷ actS θ s)
    ops₂ = o-cons e′ (semv M) (ops-sp eqP′ refl ops)
    ih   = STEP d mᵉ M lk swu swu′
                (wf-sp (act θ u) (act θ v ∷ actS θ s) refl (sym eqS)
                       (wf-sp (act θ (app u v)) (actS θ s) eqP refl wA))
                (ops-sp refl (sym eqS) ops₂)

STEP {Γᵉ} {Γˢ} {θ = θ} {Γ′} st@(Ms-FOp {s = s} {α} {t} {u} {u′} L F) mᵉ M lk
     (sw-lam Lp swt bp) (sw-lam Lp′ _ bp′) wA ops =
  G-sp (lam (act θ t) (act θ u)) (lam (act θ t) (act θ u′)) (act θ α ∷ actS θ s)
       (sym eqP) (sym eqP′) (sym eqS) (β-close (actS θ s) wA₁ ops₁ eqB eqB₀ wB wB₀ k)
  where
    A   = L ++ Lp ++ Lp′ ++ fv u ++ fv u′ ++ fvStack s
    z   = fresh A
    z∉  = fresh-∉ A
    z∉L  = ∉-++ˡ z∉
    z∉p  = ∉-++ˡ (∉-++ʳ L z∉)
    z∉p′ = ∉-++ˡ (∉-++ʳ Lp (∉-++ʳ L z∉))
    z∉u  = ∉-++ˡ (∉-++ʳ Lp′ (∉-++ʳ Lp (∉-++ʳ L z∉)))
    z∉u′ = ∉-++ˡ (∉-++ʳ (fv u) (∉-++ʳ Lp′ (∉-++ʳ Lp (∉-++ʳ L z∉))))
    z∉s  = ∉-++ʳ (fv u′) (∉-++ʳ (fv u) (∉-++ʳ Lp′ (∉-++ʳ Lp (∉-++ʳ L z∉))))

    eqS  = actS-cons θ α s
    eqP  = act-lam θ t u
    eqP′ = act-lam θ t u′
    wA₁  = wf-sp (act θ (lam t u)) (actS θ (α ∷ s)) eqP eqS wA
    ops₁ = ops-sp eqP′ eqS ops

    lα = proj₁ (stack-top (⟶ˢ-prevalid st))
    fα = proj₂ (stack-top (⟶ˢ-prevalid st))

    θ′  = (z , α) ∷ θ
    mᵉ′ : ((z , eqv , α) ∷ Γᵉ) ⊢ θ′ ⇒ Γ′
    mᵉ′ = m-eqv [] lα fα mᵉ
    M′  : Mor ((z , sub , t) ∷ Γˢ) θ′ Γ′
    M′  = mor-head M (wf⇒prevalid (sw-orig (bp z∉p))) lα (λ h → linkdom lk (fα h)) (op-at-ann ops₁)

    eqB  : act θ′ (u ^ fvar z) ≡ act θ u ^ act θ α
    eqB  = trans (cong (act θ) (sym (subst-intro {u} lα z z∉u))) (act-openT mᵉ u α)
    eqB₀ : act θ′ (u′ ^ fvar z) ≡ act θ u′ ^ act θ α
    eqB₀ = trans (cong (act θ) (sym (subst-intro {u′} lα z z∉u′))) (act-openT mᵉ u′ α)
    wB   = img (bp z∉p) M′
    wB₀  = img (bp′ z∉p′) M′

    eqS′ : actS θ s ≡ actS θ′ s
    eqS′ = cong (actS θ) (sym (substStack-id z α s z∉s))

    k : Γ′ ⊢ app* (act θ′ (u ^ fvar z)) (actS θ s) wf → Ops Γ′ (act θ′ (u′ ^ fvar z)) (actS θ s)
      → G Γ′ (app* (act θ′ (u ^ fvar z)) (actS θ s)) (app* (act θ′ (u′ ^ fvar z)) (actS θ s))
    k w o = G-sp (act θ′ (u ^ fvar z)) (act θ′ (u′ ^ fvar z)) (actS θ′ s) refl refl (sym eqS′)
                 (STEP (F z∉L) mᵉ′ M′ (link-eqv lk) (bp z∉p) (bp′ z∉p′)
                       (wf-sp (act θ′ (u ^ fvar z)) (actS θ s) refl eqS′ w) (ops-sp refl eqS′ o))

STEP {Γᵉ} {Γˢ} {θ = θ} {Γ′} (Ms-Fun {t = t} {u} {u′} L F) mᵉ M lk
     (sw-lam Lp swt bp) (sw-lam Lp′ _ bp′) wA ops =
  G-sp (lam (act θ t) (act θ u)) (lam (act θ t) (act θ u′)) [] (sym eqP) (sym eqP′) (sym eqS)
       (G-intro wA₁ wA₀ le third)
  where
    eqS  = actS-nil θ
    eqP  = act-lam θ t u
    eqP′ = act-lam θ t u′
    wA₁  = wf-sp (act θ (lam t u)) (actS θ []) eqP eqS wA
    wA₀  = ops-wf (ops-sp {S₁ = []} eqP′ eqS ops)
    wT   = img swt M

    N = L ++ Lp ++ Lp′ ++ names mᵉ ++ names (mor M)

    module Fresh {z} (z∉ : z ∉ N) where
      z∉L  = ∉-++ˡ z∉
      z∉p  = ∉-++ˡ (∉-++ʳ L z∉)
      z∉p′ = ∉-++ˡ (∉-++ʳ Lp (∉-++ʳ L z∉))
      z∉e  = ∉-++ˡ (∉-++ʳ Lp′ (∉-++ʳ Lp (∉-++ʳ L z∉)))
      z∉m  = ∉-++ʳ (names mᵉ) (∉-++ʳ Lp′ (∉-++ʳ Lp (∉-++ʳ L z∉)))
      pvᵉ  = prevalid-ctx (⟶ˢ-prevalid (F z∉L))
      pvˢ  = wf⇒prevalid (sw-orig (bp z∉p))

    fam : ∀ {z} → z ∉ N → ((z , sub , act θ t) ∷ Γ′) ⊢ (act θ u ^ fvar z) ≤*wf (act θ u′ ^ fvar z)
    fam {z} z∉ =
      subst₂ (λ a b → ((z , sub , act θ t) ∷ Γ′) ⊢ a ≤*wf b)
             (act-open mᵉ z∉e u) (act-open mᵉ z∉e u′) (G-≤ ih)
      where
        open Fresh z∉
        M↑ = mor-up M z∉m pvˢ wT
        ih = G-sp (act θ (u ^ fvar z)) (act θ (u′ ^ fvar z)) (actS θ []) {S₁ = []} refl refl eqS
               (STEP (F z∉L) (up z t mᵉ z∉e pvᵉ) M↑ (link-sub lk) (bp z∉p) (bp′ z∉p′)
                     (wf-sp (act θ (u ^ fvar z)) [] refl (sym eqS) (img (bp z∉p) M↑))
                     (ops-sp refl (sym eqS) (o-nil (img (bp′ z∉p′) M↑))))

    le : Γ′ ⊢ lam (act θ t) (act θ u) ≤*wf lam (act θ t) (act θ u′)
    le = FunCongr N fam wA₁ wA₀

    third : ∀ (Δ : Ctx) {v d} → (Δ ++ Γ′) ⊢ app (lam (act θ t) (act θ u′)) v wf
          → (Δ ++ Γ′) ⊢ lam (act θ t) (act θ u′) ≤*wf lam d Top
          → G (Δ ++ Γ′) v d
          → G (Δ ++ Γ′) (app (lam (act θ t) (act θ u)) v) (app (lam (act θ t) (act θ u′)) v)
    third Δ {v} {d} w e gv =
      β-close [] wAv opsv eqB eqB₀ (img (bp z∉p) M₂) (img (bp′ z∉p′) M₂) k
      where
        A′  = N ++ dom (Δ ++ Γ′) ++ fv u ++ fv u′
        z   = fresh A′
        z∉A = fresh-∉ A′
        open Fresh {z} (∉-++ˡ z∉A)
        z∉Δ  = ∉-++ˡ (∉-++ʳ N z∉A)
        z∉u  = ∉-++ˡ (∉-++ʳ (dom (Δ ++ Γ′)) (∉-++ʳ N z∉A))
        z∉u′ = ∉-++ʳ (fv u) (∉-++ʳ (dom (Δ ++ Γ′)) (∉-++ʳ N z∉A))

        pvΔ  = wf⇒prevalid w
        opsv : Ops (Δ ++ Γ′) (lam (act θ t) (act θ u′)) (v ∷ [])
        opsv = o-cons e gv (o-nil w)
        gv′  = op-at-ann opsv
        wv   = G-wf gv
        lv   = wf⇒lc wv
        θ₂   = θ ++ (z , v) ∷ []
        M₂   = mor-inst M Δ z∉m z∉Δ pvˢ pvΔ gv′
        mᵉ₂  = inst mᵉ Δ z∉e z∉Δ pvᵉ pvΔ lv (MPSS.Narrow.wf-fv wv)
        eqB  = act-open-snoc mᵉ z∉e lv u z∉u
        eqB₀ = act-open-snoc mᵉ z∉e lv u′ z∉u′
        leΔ  = ⊑*wf-weaken [] Δ pvΔ le
        wAv  = app-wf-mid leΔ (wf-weaken [] Δ pvΔ wA₁) w
        eqS₂ = actS-nil θ₂

        k : (Δ ++ Γ′) ⊢ act θ₂ (u ^ fvar z) wf → Ops (Δ ++ Γ′) (act θ₂ (u′ ^ fvar z)) []
          → G (Δ ++ Γ′) (act θ₂ (u ^ fvar z)) (act θ₂ (u′ ^ fvar z))
        k w′ o′ = G-sp (act θ₂ (u ^ fvar z)) (act θ₂ (u′ ^ fvar z)) (actS θ₂ []) {S₁ = []} refl refl eqS₂
                    (STEP (F z∉L) mᵉ₂ M₂ (link-sub lk) (bp z∉p) (bp′ z∉p′)
                          (wf-sp (act θ₂ (u ^ fvar z)) [] refl (sym eqS₂) w′) (ops-sp refl (sym eqS₂) o′))
```

## A layer under a good substitution

Inside a layer only the ends and the promotion points are well-formed, so the image of a layer
is kept as chains of equivalence steps between good promotions, and assembled once the ends are
known well-formed.

```agda
data LayG (Γ : Ctx) : Tm → Tm → Set where
  lg-join : ∀ {A B C} → Γ ∣ [] ⊢ A ⟶ᵉ* C → Γ ∣ [] ⊢ B ⟶ᵉ* C → LayG Γ A B
  lg-prom : ∀ {A P P₀ B} → Γ ∣ [] ⊢ A ⟶ᵉ* P → G Γ P P₀ → LayG Γ P₀ B → LayG Γ A B

lg-lf1 : ∀ {Γ A A₁ B} → Γ ∣ [] ⊢ A ⟶ᵉ A₁ → LayG Γ A₁ B → LayG Γ A B
lg-lf1 e (lg-join L R)   = lg-join (e ◅ᵉ L) R
lg-lf1 e (lg-prom L g r) = lg-prom (e ◅ᵉ L) g r

lg-rgh : ∀ {Γ A B B₁} → LayG Γ A B₁ → Γ ∣ [] ⊢ B ⟶ᵉ B₁ → LayG Γ A B
lg-rgh (lg-join L R)   e = lg-join L (e ◅ᵉ R)
lg-rgh (lg-prom L g r) e = lg-prom L g (lg-rgh r e)

assembleG : ∀ {Γ A B} → Γ ⊢ A wf → Γ ⊢ B wf → LayG Γ A B → G Γ A B
assembleG wA wB (lg-join L R)   = G-join wA L R wB
assembleG wA wB (lg-prom L g r) = G-expand* wA L (G-trans g (assembleG (G-wfʳ g) wB r))
```

## The fundamental lemma

```agda
FL-wf  : ∀ {Γ m} → Γ ⊢ m wf → SW Γ m
FL-sub : ∀ {Γ a b} → Γ ⊢ a ≤*wf b → SW Γ a × Sem≤ Γ a b
FL-lay : ∀ {Γ a b θ Γ′} → Γ ⊢ a ⊑wf[ sub-m ] b → Mor Γ θ Γ′ → LayG Γ′ (act θ a) (act θ b)

FL-wf w@(Wf-PrS pv m)  = sw-var w (λ M → G-wf (subs M m))
FL-wf w@(Wf-PrE pv m)  = sw-var w (λ M → eqvs M m)
FL-wf (Wf-Top pv)      = sw-top pv
FL-wf (Wf-Fun L F w)   = sw-lam L (FL-wf w) (λ z∉ → FL-wf (F z∉))
FL-wf w@(Wf-App d₁ d₂) =
  sw-app w (proj₁ (FL-sub d₁)) (proj₁ (FL-sub d₂)) (proj₂ (FL-sub d₁)) (proj₂ (FL-sub d₂))

FL-sub (Ws-Sub wu d wv)  =
  FL-wf wu , λ M → assembleG (img (FL-wf wu) M) (img (FL-wf wv) M) (FL-lay d M)
FL-sub (Ws-Trs d₁ w d₂) =
  proj₁ (FL-sub d₁) , λ M → G-trans (proj₂ (FL-sub d₁) M) (proj₂ (FL-sub d₂) M)

FL-lay (Ws-Rfl pv) M = lg-join εᵉ εᵉ
FL-lay {θ = θ} {Γ′} (Ws-Lf1 {v = v} {v' = v′} e d) M =
  lg-lf1 (subst (λ q → Γ′ ∣ q ⊢ act θ v ⟶ᵉ act θ v′) (actS-nil θ) (m-e (mor M) e)) (FL-lay d M)
FL-lay {θ = θ} {Γ′} (Ws-Rgh {t = t} {t' = t′} d e) M =
  lg-rgh (FL-lay d M) (subst (λ q → Γ′ ∣ q ⊢ act θ t ⟶ᵉ act θ t′) (actS-nil θ) (m-e (mor M) e))
FL-lay {a = a} {θ = θ} {Γ′} (Ws-Lf2 {v' = a₀} wa st wa₀ d) M =
  lg-prom εᵉ
    (G-sp (act θ a) (act θ a₀) (actS θ []) {S₁ = []} refl refl (actS-nil θ)
          (STEP st (mor M) M link-id swa swa₀
                (wf-sp (act θ a) [] refl (sym (actS-nil θ)) (img swa M))
                (ops-sp refl (sym (actS-nil θ)) (o-nil (img swa₀ M)))))
    (FL-lay d M)
  where
    swa  = FL-wf wa
    swa₀ = FL-wf wa₀
```

## What this establishes

Under the parameter that every well-formed term is ranked: a well-subtyping derivation
`Γ ⊢ a ≤*wf b` gives, for every good substitution `θ : Γ ⇒ Γ′`, that `aθ` is good at `bθ` — in
particular `Γ′ ⊢ aθ ≤*wf bθ`, and the same under any good operand, hereditarily — and a
well-formedness derivation has a well-formed image (`img ∘ FL-wf`: Lemma 7 for good
substitutions, with no appeal to Conjecture 8). `MPSS/Conj8Ranked` draws Conjecture 8 from it.
