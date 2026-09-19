# MPSS, candidate C: scoping, and narrowing of the stack-reading judgements

For the judgements of `MPSS/StackWf`: a well-formed term has its free variables in the domain of
the context (`wfˢ-fv`), and the three judgements are preserved when annotations of the context and
entries of the operand stack are reduced (`wfˢ-narrow`, `≤wfˢ-narrow`, `≤*wfˢ-narrow`). This is
`PSS/Narrowing` (`WfStep`, `CtxRedW`, `StkRedW`, `wf-narrow`) over MPSS's machine.

Two differences from v1. An entry is reduced by a chain of `⟶ᵉ` steps (the chain type of
`MPSS/Strip`), since an evaluation step is a chain and not one step (`MPSS/EvalChain`); the
witness that well-formedness is kept is attached to the whole chain, because the terms inside the
chain are not known to be well-formed. And `⟶ᵉ` reads the context, so each chain is taken at a
fixed configuration: an annotation's chain at the context below it, a stack entry's chain at the
whole context, both at the empty stack. These are the configurations at which `Ct-Ann` and `Ct-Stk`
of `MPSS/CtxReduction` take their steps, so a pair of reductions is a sequence of `↣`, and the
machine relation inside `Wc-Rule` follows it by `≤-↣` of `MPSS/MachineNarrow`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfNarrow where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import MPSS.Subtyping
open import MPSS.StackWf
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-ctx)
open import MPSS.CtxPrevalid using (↣-prevalid)
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_; ⟶ᵉ*-lc)
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Preserve using (fv-⟶ᵉ-dom)
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.MachineNarrow using (≤-↣)
open import PSS.Scope using (fv-open-lower)
```

## Well-formed terms are scoped

As `wf-fv` of `MPSS/Narrow`: under a binder, the body is opened at a name fresh for it, and that
name is removed from the domain again.

```agda
wfˢ-fv    : ∀ {Γ s t} → Γ ∣ s ⊢ t wfˢ → fv t ⊑ dom Γ
≤*wfˢ-fvˡ : ∀ {Γ s u t} → Γ ∣ s ⊢ u ≤*wfˢ t → fv u ⊑ dom Γ

wfˢ-fv (Wc-PrS _ m _) (here refl) = ∈-dom m
wfˢ-fv (Wc-PrE _ m _) (here refl) = ∈-dom m
wfˢ-fv (Wc-Top _)     ()
wfˢ-fv {Γ} (Wc-Fun {t = t} {u = u} L F d) h with ∈-++⁻ (fv t) h
... | inj₁ p = wfˢ-fv d p
... | inj₂ p = body p
  where
    x   = fresh (L ++ fv u)
    x∉L = ∉-++ˡ (fresh-∉ (L ++ fv u))
    x∉u : x ∉ fv u
    x∉u = ∉-++ʳ L (fresh-∉ (L ++ fv u))

    body : ∀ {y} → y ∈ fv u → y ∈ dom Γ
    body {y} q with wfˢ-fv (F x∉L) (fv-open-lower 0 (fvar x) u q)
    ... | here refl = ⊥-elim (x∉u q)
    ... | there r   = r
wfˢ-fv {Γ} (Wc-FOp {t = t} {u = u} L F d) h with ∈-++⁻ (fv t) h
... | inj₁ p = wfˢ-fv d p
... | inj₂ p = body p
  where
    x   = fresh (L ++ fv u)
    x∉L = ∉-++ˡ (fresh-∉ (L ++ fv u))
    x∉u : x ∉ fv u
    x∉u = ∉-++ʳ L (fresh-∉ (L ++ fv u))

    body : ∀ {y} → y ∈ fv u → y ∈ dom Γ
    body {y} q with wfˢ-fv (F x∉L) (fv-open-lower 0 (fvar x) u q)
    ... | here refl = ⊥-elim (x∉u q)
    ... | there r   = r
wfˢ-fv (Wc-App {u = u} d₁ d₂) h with ∈-++⁻ (fv u) h
... | inj₁ p = ≤*wfˢ-fvˡ d₁ p
... | inj₂ p = ≤*wfˢ-fvˡ d₂ p

≤*wfˢ-fvˡ (Wc-Sub (Wc-Rule w _ _)) = wfˢ-fv w
≤*wfˢ-fvˡ (Wc-Trs d _)             = ≤*wfˢ-fvˡ d
```

## Chains: scoping, weakening

```agda
⟶ᵉ*-fv : ∀ {Γ s a b} → Γ ∣ s ⊢ a ⟶ᵉ* b → fv a ⊑ dom Γ → fv b ⊑ dom Γ
⟶ᵉ*-fv (ε _)   f = f
⟶ᵉ*-fv (d ◅ p) f = ⟶ᵉ*-fv p (fv-⟶ᵉ-dom d f)

chain-weaken : ∀ {Γ x c t a b} → ((x , c , t) ∷ Γ) prevalid
             → Γ ∣ [] ⊢ a ⟶ᵉ* b → ((x , c , t) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ* b
chain-weaken pv (ε _) = ε (Pv-Nil pv)
chain-weaken {x = x} {c} {t} pv (e ◅ p) =
  ⟶ᵉ-weaken [] ((x , c , t) ∷ []) (Pv-Nil pv) e ◅ chain-weaken pv p
```

## Reductions that keep well-formedness

`WfStep t t′`: at every configuration, if `t` is well-formed then so is `t′`. As in v1, the
context and the stack are reduced by two relations, so that a stack reduction can be inverted at
`Wc-FOp`. An annotation's chain is at the context below the entry; a stack entry's chain is at the
whole context.

```agda
WfStep : Tm → Tm → Set
WfStep t t′ = ∀ {Γ₀ s₀} → Γ₀ ∣ s₀ ⊢ t wfˢ → Γ₀ ∣ s₀ ⊢ t′ wfˢ

data CtxRedW : Ctx → Ctx → Set where
  crw-nil  : CtxRedW [] []
  crw-cons : ∀ {Γ Γ′ x c t t′} → CtxRedW Γ Γ′ → Γ ∣ [] ⊢ t ⟶ᵉ* t′ → WfStep t t′
           → CtxRedW ((x , c , t) ∷ Γ) ((x , c , t′) ∷ Γ′)

data StkRedW (Γ : Ctx) : Stack → Stack → Set where
  srw-nil  : StkRedW Γ [] []
  srw-cons : ∀ {s s′ α α′} → StkRedW Γ s s′ → Γ ∣ [] ⊢ α ⟶ᵉ* α′ → WfStep α α′
           → StkRedW Γ (α ∷ s) (α′ ∷ s′)

CtxRedW-refl : ∀ {Γ} → Γ prevalid → CtxRedW Γ Γ
CtxRedW-refl Pv-Emp            = crw-nil
CtxRedW-refl (Pv-Ctx pv _ _ _) = crw-cons (CtxRedW-refl pv) (ε (Pv-Nil pv)) (λ h → h)
CtxRedW-refl (Pv-EqA pv _ _ _) = crw-cons (CtxRedW-refl pv) (ε (Pv-Nil pv)) (λ h → h)

StkRedW-refl : ∀ {Γ} → Γ prevalid → (s : Stack) → StkRedW Γ s s
StkRedW-refl pv []      = srw-nil
StkRedW-refl pv (α ∷ s) = srw-cons (StkRedW-refl pv s) (ε (Pv-Nil pv)) (λ h → h)

StkRedW-weaken : ∀ {Γ x c t s s′} → ((x , c , t) ∷ Γ) prevalid
               → StkRedW Γ s s′ → StkRedW ((x , c , t) ∷ Γ) s s′
StkRedW-weaken pv srw-nil           = srw-nil
StkRedW-weaken pv (srw-cons sr p h) = srw-cons (StkRedW-weaken pv sr) (chain-weaken pv p) h

CtxRedW-lookup : ∀ {Γ Γ′ y c t} → CtxRedW Γ Γ′ → (y , c , t) ∈ Γ
               → ∃[ t′ ] (((y , c , t′) ∈ Γ′) × WfStep t t′)
CtxRedW-lookup (crw-cons cr p h) (here refl) = _ , here refl , h
CtxRedW-lookup (crw-cons cr p h) (there m) with CtxRedW-lookup cr m
... | t′ , m′ , h′ = t′ , there m′ , h′
```

## Sequences of context reductions

`Ct-Ann` and `Ct-Stk` take one `⟶ᵉ` step per entry, so a chain on one entry is a sequence of `↣`,
the rest of the configuration held fixed.

```agda
infixr 5 _◅ᶜ_
infix 3 _∣_↣*_∣_
data _∣_↣*_∣_ : Ctx → Stack → Ctx → Stack → Set where
  εᶜ   : ∀ {Γ s} → Γ ∣ s ↣* Γ ∣ s
  _◅ᶜ_ : ∀ {Γ s Γ₁ s₁ Γ′ s′} → Γ ∣ s ↣ Γ₁ ∣ s₁ → Γ₁ ∣ s₁ ↣* Γ′ ∣ s′ → Γ ∣ s ↣* Γ′ ∣ s′

_++ᶜ_ : ∀ {Γ s Γ₁ s₁ Γ′ s′} → Γ ∣ s ↣* Γ₁ ∣ s₁ → Γ₁ ∣ s₁ ↣* Γ′ ∣ s′ → Γ ∣ s ↣* Γ′ ∣ s′
εᶜ       ++ᶜ q = q
(c ◅ᶜ p) ++ᶜ q = c ◅ᶜ (p ++ᶜ q)

⊑-dom : ∀ {Γ s Γ′ s′} {N : List Name} → Γ ∣ s ↣ Γ′ ∣ s′ → N ⊑ dom Γ → N ⊑ dom Γ′
⊑-dom {N = N} c f = subst (λ D → N ⊑ D) (↣-dom c) f

↣*-prevalid : ∀ {Γ s Γ′ s′} → Γ ∣ s prevalid → Γ ∣ s ↣* Γ′ ∣ s′ → Γ′ ∣ s′ prevalid
↣*-prevalid pv εᶜ        = pv
↣*-prevalid pv (c ◅ᶜ cs) = ↣*-prevalid (↣-prevalid pv c) cs

≤-↣* : ∀ {Γ s Γ′ s′ u t} → LC u → LC t → fv u ⊑ dom Γ → fv t ⊑ dom Γ
     → Γ ∣ s ↣* Γ′ ∣ s′
     → Γ ∣ s ⊢ u ≤ t
     → Γ′ ∣ s′ ⊢ u ≤ t
≤-↣* lu lt fu ft εᶜ        d = d
≤-↣* lu lt fu ft (c ◅ᶜ cs) d = ≤-↣* lu lt (⊑-dom c fu) (⊑-dom c ft) cs (≤-↣ lu lt fu ft c d)
```

Holding the head fixed, by a reflexive step (`⟶ᵉ-refl`), for which the head has to be locally
closed and scoped in the context at which the step is taken:

```agda
lift-ann : ∀ {Γ s Γ′ s′ x c t} → Γ prevalid → LC t → fv t ⊑ dom Γ
         → Γ ∣ s ↣* Γ′ ∣ s′
         → ((x , c , t) ∷ Γ) ∣ s ↣* ((x , c , t) ∷ Γ′) ∣ s′
lift-ann pv l f εᶜ        = εᶜ
lift-ann pv l f (c ◅ᶜ cs) =
  Ct-Ann c (⟶ᵉ-refl (Pv-Nil pv) l f) ◅ᶜ lift-ann (↣-ctx c pv) l (⊑-dom c f) cs

lift-stk : ∀ {Γ s Γ′ s′ α} → Γ prevalid → LC α → fv α ⊑ dom Γ
         → Γ ∣ s ↣* Γ′ ∣ s′
         → Γ ∣ (α ∷ s) ↣* Γ′ ∣ (α ∷ s′)
lift-stk pv l f εᶜ        = εᶜ
lift-stk pv l f (c ◅ᶜ cs) =
  Ct-Stk c (⟶ᵉ-refl (Pv-Nil pv) l f) ◅ᶜ lift-stk (↣-ctx c pv) l (⊑-dom c f) cs
```

Reducing the head along a chain:

```agda
head-ann : ∀ {Γ s x c t t′} → Γ ∣ [] ⊢ t ⟶ᵉ* t′
         → ((x , c , t) ∷ Γ) ∣ s ↣* ((x , c , t′) ∷ Γ) ∣ s
head-ann (ε _)   = εᶜ
head-ann (e ◅ p) = Ct-Ann Ct-Refl e ◅ᶜ head-ann p

head-stk : ∀ {Γ s α α′} → Γ ∣ [] ⊢ α ⟶ᵉ* α′
         → Γ ∣ (α ∷ s) ↣* Γ ∣ (α′ ∷ s)
head-stk (ε _)   = εᶜ
head-stk (e ◅ p) = Ct-Stk Ct-Refl e ◅ᶜ head-stk p
```

A context reduction, at the empty stack. The head's chain is at the unreduced tail, so the head
is reduced first and then held fixed while the tail is reduced.

```agda
ctx-seq : ∀ {Γ Γ′} → Γ prevalid → CtxRedW Γ Γ′ → Γ ∣ [] ↣* Γ′ ∣ []
ctx-seq pv crw-nil           = εᶜ
ctx-seq pv (crw-cons cr p h) =
  head-ann p
  ++ᶜ lift-ann (tail-prevalid pv) (⟶ᵉ*-lc (head-lc pv) p) (⟶ᵉ*-fv p (head-fv pv))
               (ctx-seq (tail-prevalid pv) cr)
```

A stack reduction, the context held fixed; and a sequence at the empty stack, under a stack. The
stack entries' chains are at the unreduced context, so the stack is reduced before the context,
as in `MPSS/MachineNarrow`.

```agda
stk-seq : ∀ {Γ s s′} → Γ ∣ s prevalid → StkRedW Γ s s′ → Γ ∣ s ↣* Γ ∣ s′
stk-seq pv              srw-nil           = εᶜ
stk-seq (Pv-Sta pv l f) (srw-cons sr p h) =
  lift-stk (prevalid-ctx pv) l f (stk-seq pv sr) ++ᶜ head-stk p

under-stack : ∀ {Γ Γ′ s} → Γ ∣ s prevalid → Γ ∣ [] ↣* Γ′ ∣ [] → Γ ∣ s ↣* Γ′ ∣ s
under-stack (Pv-Nil _)      cs = cs
under-stack (Pv-Sta pv l f) cs = lift-stk (prevalid-ctx pv) l f (under-stack pv cs)

red-seq : ∀ {Γ Γ′ s s′} → Γ ∣ s prevalid → CtxRedW Γ Γ′ → StkRedW Γ s s′ → Γ ∣ s ↣* Γ′ ∣ s′
red-seq pv cr sr =
  let ss = stk-seq pv sr
  in ss ++ᶜ under-stack (↣*-prevalid pv ss) (ctx-seq (prevalid-ctx pv) cr)

red-prevalid : ∀ {Γ Γ′ s s′} → CtxRedW Γ Γ′ → StkRedW Γ s s′ → Γ ∣ s prevalid → Γ′ ∣ s′ prevalid
red-prevalid cr sr pv = ↣*-prevalid pv (red-seq pv cr sr)
```

## Narrowing

The three judgements together, each by structural induction on its derivation, as `wf-narrow` of
`PSS/Narrowing`. At `Wc-FOp` the chain of the consumed stack entry becomes the chain of the
parameter's annotation — both are at `Γ ∣ []` — and the rest of the stack reduction is weakened
by the parameter. The machine relation inside `Wc-Rule` is carried by `≤-↣*`, with local closure
from `wfˢ⇒lc` and scoping from `wfˢ-fv`.

```agda
wfˢ-narrow   : ∀ {Γ s Γ′ s′ u} → CtxRedW Γ Γ′ → StkRedW Γ s s′
             → Γ ∣ s ⊢ u wfˢ → Γ′ ∣ s′ ⊢ u wfˢ
≤wfˢ-narrow  : ∀ {Γ s Γ′ s′ u t} → CtxRedW Γ Γ′ → StkRedW Γ s s′
             → Γ ∣ s ⊢ u ≤wfˢ t → Γ′ ∣ s′ ⊢ u ≤wfˢ t
≤*wfˢ-narrow : ∀ {Γ s Γ′ s′ u t} → CtxRedW Γ Γ′ → StkRedW Γ s s′
             → Γ ∣ s ⊢ u ≤*wfˢ t → Γ′ ∣ s′ ⊢ u ≤*wfˢ t

wfˢ-narrow cr sr (Wc-Top pv) = Wc-Top (red-prevalid cr sr pv)
wfˢ-narrow cr sr (Wc-PrS pv m wt) with CtxRedW-lookup cr m
... | t′ , m′ , h = Wc-PrS (red-prevalid cr sr pv) m′ (h (wfˢ-narrow cr sr wt))
wfˢ-narrow cr sr (Wc-PrE pv m wα) with CtxRedW-lookup cr m
... | α′ , m′ , h = Wc-PrE (red-prevalid cr sr pv) m′ (h (wfˢ-narrow cr sr wα))
wfˢ-narrow cr srw-nil (Wc-Fun L F wa) =
  Wc-Fun L (λ {x} x∉ → wfˢ-narrow (crw-cons cr (ε (wfˢ⇒prevalid wa)) (λ h → h)) srw-nil (F x∉))
           (wfˢ-narrow cr srw-nil wa)
wfˢ-narrow cr (srw-cons sr p h) (Wc-FOp L F wa) =
  Wc-FOp L (λ {x} x∉ → wfˢ-narrow (crw-cons cr p h)
                                   (StkRedW-weaken (prevalid-ctx (wfˢ⇒prevalid (F x∉))) sr)
                                   (F x∉))
           (wfˢ-narrow cr srw-nil wa)
wfˢ-narrow cr sr (Wc-App d₁ d₂) =
  Wc-App (≤*wfˢ-narrow cr (srw-cons sr (ε pv₀) (λ h → h)) d₁)
         (≤*wfˢ-narrow cr srw-nil d₂)
  where
    pv₀ = wfˢ⇒prevalid (proj₁ (≤*wfˢ⇒both d₂))

≤wfˢ-narrow cr sr (Wc-Rule wu wt d) =
  Wc-Rule (wfˢ-narrow cr sr wu) (wfˢ-narrow cr sr wt)
          (≤-↣* (wfˢ⇒lc wu) (wfˢ⇒lc wt) (wfˢ-fv wu) (wfˢ-fv wt)
                (red-seq (wfˢ⇒prevalid wu) cr sr) d)

≤*wfˢ-narrow cr sr (Wc-Sub d)     = Wc-Sub (≤wfˢ-narrow cr sr d)
≤*wfˢ-narrow cr sr (Wc-Trs d₁ d₂) = Wc-Trs (≤*wfˢ-narrow cr sr d₁) (≤*wfˢ-narrow cr sr d₂)
```

## What this establishes

`wfˢ-fv`: a term well-formed at `Γ ∣ s` has its free variables in `dom Γ`. `wfˢ-narrow`,
`≤wfˢ-narrow`, `≤*wfˢ-narrow`: the three judgements of candidate C are preserved when annotations
and stack entries are reduced by chains of `⟶ᵉ` steps, each chain carrying a `WfStep` witness for
its two ends — v1's Lemmas B.11 and B.17, in the single form of `PSS/Narrowing`. Nothing is
assumed. What is spent: `≤-↣` (`MPSS/MachineNarrow`) along the sequence of context reductions
`red-seq`, `↣-prevalid` (`MPSS/CtxPrevalid`), `⟶ᵉ-refl` (`MPSS/StackPush`) and `⟶ᵉ-weaken`
(`MPSS/Weakening`).
