# System λ⊲: Lemma 2.4 and narrowing of the extended context

**Lemma 2.4** — the diagrammatic reading of `⊲`. A subtyping derivation is exactly a promotion
chain out of the source meeting an equivalence chain out of the target:

> `Γ ∣ s ⊢ u ≤ t` iff there is a `w` with `Γ ∣ s ⊢ u ⟶≤* w` and `t ⟶≡* w`.

With that, **narrowing** (Lemmas B.12 and B.18: the extended context may be reduced under a
subtyping derivation) becomes a structural induction on the promotion chain, each step
discharged by Theorem 4.5. Going through the derivation directly instead would not be
structural — the tail has to be corrected by `push≡`, which does not shrink it.

Both narrowing lemmas of the paper are the single statement over `CtxRed`/`StkRed`.

```agda
{-# OPTIONS --safe #-}

module PSS.Narrowing where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.Equivalence
open import PSS.WellFormed
open import PSS.Scope
open import PSS.Commutation
open import PSS.Transitivity using (wf⇒lc)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
```

## Reduction chains

```agda
infix 3 _⟶≡*_
data _⟶≡*_ : Tm → Tm → Set where
  εₑ   : ∀ {t} → t ⟶≡* t
  _◅ₑ_ : ∀ {t u v} → t ⟶≡ u → u ⟶≡* v → t ⟶≡* v

infix 3 _∣_⊢_⟶≤*_
data _∣_⊢_⟶≤*_ : Ctx → Stack → Tm → Tm → Set where
  εₚ   : ∀ {Γ s t} → Γ ∣ s ⊢ t ⟶≤* t
  _◅ₚ_ : ∀ {Γ s t u v} → Γ ∣ s ⊢ t ⟶≤ u → Γ ∣ s ⊢ u ⟶≤* v → Γ ∣ s ⊢ t ⟶≤* v

_++ₑ_ : ∀ {t u v} → t ⟶≡* u → u ⟶≡* v → t ⟶≡* v
εₑ        ++ₑ c = c
(e ◅ₑ c₁) ++ₑ c = e ◅ₑ (c₁ ++ₑ c)
```

## Lemma 2.4

```agda
⊲⇒diag : ∀ {Γ s u t} → Γ ∣ s ⊢ u ≤ t
       → ∃[ w ] ((Γ ∣ s ⊢ u ⟶≤* w) × (t ⟶≡* w))
⊲⇒diag (As-Refl pv)     = _ , εₚ , εₑ
⊲⇒diag (As-Left-1 st d) with ⊲⇒diag d
... | w , chain , c     = w , st ◅ₚ chain , c
⊲⇒diag (As-Right d e)   with ⊲⇒diag d
... | w , chain , c     = w , chain , e ◅ₑ c

diag⇒⊲ : ∀ {Γ s u t w} → Γ ∣ s prevalid
       → Γ ∣ s ⊢ u ⟶≤* w → t ⟶≡* w → Γ ∣ s ⊢ u ≤ t
diag⇒⊲ pv (st ◅ₚ chain) c = As-Left-1 st (diag⇒⊲ pv chain c)
diag⇒⊲ pv εₚ εₑ           = As-Refl pv
diag⇒⊲ pv εₚ (e ◅ₑ c)     = As-Right (diag⇒⊲ pv εₚ c) e
```

## Stripping an equivalence step along a promotion chain

The engine of narrowing: Theorem 4.5 applied down the chain, carrying the equivalence step
forward. Structural in the chain, so no size measure is needed.

```agda
⟶≤*-strip : ∀ {Γ s Γ' s' u u₀ w}
          → LC u
          → CtxRed Γ Γ' → StkRed s s'
          → u ⟶≡ u₀
          → Γ ∣ s ⊢ u ⟶≤* w
          → ∃[ w' ] ((w ⟶≡* w') × (Γ' ∣ s' ⊢ u₀ ⟶≤* w'))
⟶≤*-strip lu cr sr e εₚ = _ , (e ◅ₑ εₑ) , εₚ
⟶≤*-strip lu cr sr e (st ◅ₚ chain) with Thm-4·5 lu cr sr e st
... | t₃ , p , q with ⟶≤*-strip (⟶≤-lc lu st) cr sr p chain
...   | w' , c , chain' = w' , c , (q ◅ₚ chain')
```

## Narrowing — Lemmas B.12 and B.18

```agda
⊲-narrow : ∀ {Γ s Γ' s' u t}
         → LC u
         → CtxRed Γ Γ' → StkRed s s'
         → Γ ∣ s ⊢ u ≤ t → Γ' ∣ s' ⊢ u ≤ t
⊲-narrow lu cr sr d with ⊲⇒diag d
... | w , chain , c with ⟶≤*-strip lu cr sr (⟶≡-refl lu) chain
...   | w' , c' , chain' =
        diag⇒⊲ (prevalid-red (chain-prevalid d) cr sr) chain' (c ++ₑ c')
  where
    chain-prevalid : ∀ {Γ s u t} → Γ ∣ s ⊢ u ≤ t → Γ ∣ s prevalid
    chain-prevalid (As-Refl pv)     = pv
    chain-prevalid (As-Left-1 st _) = ⟶≤-prevalid st
    chain-prevalid (As-Right d _)   = chain-prevalid d
```

## Narrowing well-formedness — Lemmas B.11 and B.17

Narrowing a *bound* is not free: `W-Var` records that the bound is well-formed, and after
reduction that has to be re-established. Lemma B.11 therefore carries the hypothesis that the
bound "preserves well-formedness" (Definition B.1). Here that hypothesis travels in the
reduction relation itself, one witness per changed entry.

```agda
WfStep : Tm → Tm → Set
WfStep t t' = ∀ {Γ₀ s₀} → Γ₀ ∣ s₀ ⊢ t wf → Γ₀ ∣ s₀ ⊢ t' wf

data CtxRedW : Ctx → Ctx → Set where
  crw-nil  : CtxRedW [] []
  crw-cons : ∀ {Γ Γ' x t t'} → CtxRedW Γ Γ' → t ⟶≡ t' → WfStep t t'
           → CtxRedW ((x , t) ∷ Γ) ((x , t') ∷ Γ')

data StkRedW : Stack → Stack → Set where
  srw-nil  : StkRedW [] []
  srw-cons : ∀ {s s' α α'} → StkRedW s s' → α ⟶≡ α' → WfStep α α'
           → StkRedW (α ∷ s) (α' ∷ s')

forgetC : ∀ {Γ Γ'} → CtxRedW Γ Γ' → CtxRed Γ Γ'
forgetC crw-nil            = cr-nil
forgetC (crw-cons cr e _)  = cr-cons (forgetC cr) e

forgetS : ∀ {s s'} → StkRedW s s' → StkRed s s'
forgetS srw-nil            = sr-nil
forgetS (srw-cons sr e _)  = sr-cons (forgetS sr) e

CtxRedW-refl : ∀ {Γ} → Γ ∣ [] prevalid → CtxRedW Γ Γ
CtxRedW-refl P-Ctx1            = crw-nil
CtxRedW-refl (P-Ctx2 p _ lt _) = crw-cons (CtxRedW-refl p) (⟶≡-refl lt) (λ h → h)

StkRedW-refl : ∀ {s} → StkLC s → StkRedW s s
StkRedW-refl slc-nil          = srw-nil
StkRedW-refl (slc-cons lα sl) = srw-cons (StkRedW-refl sl) (⟶≡-refl lα) (λ h → h)

CtxRedW-lookup : ∀ {Γ Γ' y t} → CtxRedW Γ Γ' → (y , t) ∈ Γ
               → ∃[ t' ] (((y , t') ∈ Γ') × (WfStep t t'))
CtxRedW-lookup (crw-cons cr e h) (here refl) = _ , here refl , h
CtxRedW-lookup (crw-cons cr e h) (there m)   with CtxRedW-lookup cr m
... | t' , m' , h' = t' , there m' , h'
```

The three judgements narrow together, each by structural induction on its own derivation. The
subtyping premise inside `Wf-Rule` is handled by `⊲-narrow`.

```agda
wf-narrow   : ∀ {Γ s Γ' s' u} → CtxRedW Γ Γ' → StkRedW s s'
            → Γ ∣ s ⊢ u wf → Γ' ∣ s' ⊢ u wf
≤wf-narrow  : ∀ {Γ s Γ' s' u t} → CtxRedW Γ Γ' → StkRedW s s'
            → Γ ∣ s ⊢ u ≤wf t → Γ' ∣ s' ⊢ u ≤wf t
≤*wf-narrow : ∀ {Γ s Γ' s' u t} → CtxRedW Γ Γ' → StkRedW s s'
            → Γ ∣ s ⊢ u ≤*wf t → Γ' ∣ s' ⊢ u ≤*wf t

wf-narrow cr sr (W-Top pv) = W-Top (prevalid-red pv (forgetC cr) (forgetS sr))
wf-narrow cr sr (W-Var pv mem wt) with CtxRedW-lookup cr mem
... | t' , mem' , h =
      W-Var (prevalid-red pv (forgetC cr) (forgetS sr)) mem' (h (wf-narrow cr sr wt))
wf-narrow cr srw-nil (W-Fun L F wa) =
  W-Fun L (λ {x} x∉ → wf-narrow (crw-cons cr (⟶≡-refl (wf⇒lc wa)) (λ h → h)) srw-nil (F x∉))
          (wf-narrow cr srw-nil wa)
wf-narrow cr (srw-cons sr e h) (W-FunOp L F wa) =
  W-FunOp L (λ {x} x∉ → wf-narrow (crw-cons cr e h) sr (F x∉))
            (wf-narrow cr srw-nil wa)
wf-narrow cr sr (W-App {v = v} d₁ d₂) =
  W-App (≤*wf-narrow cr (srw-cons sr (⟶≡-refl lv) (λ h → h)) d₁)
        (≤*wf-narrow cr srw-nil d₂)
  where
    lv : LC v
    lv = ≤*wf⇒lcˡ′ d₂
      where
        ≤*wf⇒lcˡ′ : ∀ {Γ₀ s₀ a b} → Γ₀ ∣ s₀ ⊢ a ≤*wf b → LC a
        ≤*wf⇒lcˡ′ (Wf-Sub (Wf-Rule wa _ _)) = wf⇒lc wa
        ≤*wf⇒lcˡ′ (Wf-Trans d _ _)          = ≤*wf⇒lcˡ′ d

≤wf-narrow cr sr (Wf-Rule wu wt d) =
  Wf-Rule (wf-narrow cr sr wu) (wf-narrow cr sr wt)
          (⊲-narrow (wf⇒lc wu) (forgetC cr) (forgetS sr) d)

≤*wf-narrow cr sr (Wf-Sub d)          = Wf-Sub (≤wf-narrow cr sr d)
≤*wf-narrow cr sr (Wf-Trans d₁ d₂ wu) =
  Wf-Trans (≤*wf-narrow cr sr d₁) (≤*wf-narrow cr sr d₂) (wf-narrow cr sr wu)
```

## What this establishes

Lemma 2.4 in both directions, narrowing of the extended context in a subtyping derivation
(Lemmas B.12 and B.18) and in a well-formedness derivation (B.11 and B.17), each unified over
`CtxRed`/`StkRed` rather than split into a context version and a stack version.

**Next:** Lemma B.5 (substitution preserves well-formedness), then B.4 and Theorem 4.2.
