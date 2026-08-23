# System λ⊲: scoping under reduction and context reduction

Theorem 4.5 quantifies over *reduced* extended contexts `Γ ∣ s ↣ Γ' ∣ s'`, and three promotion
rules require the target to be prevalid. So prevalidity has to survive context reduction —
which holds because **`⟶≡` never invents a free variable**.

Also here: looking a bound up through a context reduction, which is what Theorem 4.5's
`Srs-Prom` case turns on.

A structural note. Prevalidity peels the *stack* first (`P-Ctx3`) and only then the *context*
(`P-Ctx2`), whereas Figure 3's `↣` interleaves the two freely. Rather than fight that, `↣` is
factored into pointwise relations on the context and the stack separately, and prevalidity is
rebuilt from those in its own order.

```agda
{-# OPTIONS --safe #-}

module PSS.Scope where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.Equivalence
```

## Opening and free variables

Opening never *removes* a free variable, and never adds anything beyond the free variables of
the term plugged in.

```agda
fv-open-lower : ∀ k w t → fv t ⊑ fv (openRec k w t)
fv-open-lower k w (bvar i)  ()
fv-open-lower k w (fvar x)  h = h
fv-open-lower k w Top       ()
fv-open-lower k w (lam t b) h with ∈-++⁻ (fv t) h
... | inj₁ p = ∈-++⁺ˡ (fv-open-lower k w t p)
... | inj₂ p = ∈-++⁺ʳ (fv (openRec k w t)) (fv-open-lower (suc k) w b p)
fv-open-lower k w (app f a) h with ∈-++⁻ (fv f) h
... | inj₁ p = ∈-++⁺ˡ (fv-open-lower k w f p)
... | inj₂ p = ∈-++⁺ʳ (fv (openRec k w f)) (fv-open-lower k w a p)

fv-open-split : ∀ k w t {y} → y ∈ fv (openRec k w t) → (y ∈ fv t) ⊎ (y ∈ fv w)
fv-open-split k w (bvar i) {y} h = go (k ≟ i)
  where
    go : Dec (k ≡ i) → (y ∈ fv (bvar i)) ⊎ (y ∈ fv w)
    go (yes refl) = inj₂ (subst (λ z → y ∈ fv z) (open-bvar-≡ {k} w) h)
    go (no  k≢i)  = ⊥-elim (empty (subst (λ z → y ∈ fv z) (open-bvar-≢ {k} {i} w k≢i) h))
      where
        empty : y ∈ fv (bvar i) → _
        empty ()
fv-open-split k w (fvar x)  h = inj₁ h
fv-open-split k w Top       ()
fv-open-split k w (lam t b) {y} h with ∈-++⁻ (fv (openRec k w t)) h
... | inj₁ p with fv-open-split k w t p
...   | inj₁ q = inj₁ (∈-++⁺ˡ q)
...   | inj₂ q = inj₂ q
fv-open-split k w (lam t b) {y} h | inj₂ p with fv-open-split (suc k) w b p
...   | inj₁ q = inj₁ (∈-++⁺ʳ (fv t) q)
...   | inj₂ q = inj₂ q
fv-open-split k w (app f a) {y} h with ∈-++⁻ (fv (openRec k w f)) h
... | inj₁ p with fv-open-split k w f p
...   | inj₁ q = inj₁ (∈-++⁺ˡ q)
...   | inj₂ q = inj₂ q
fv-open-split k w (app f a) {y} h | inj₂ p with fv-open-split k w a p
...   | inj₁ q = inj₁ (∈-++⁺ʳ (fv f) q)
...   | inj₂ q = inj₂ q
```

## `⟶≡` does not invent free variables

The binder cases go through a fresh name: the cofinite premise gives the containment for the
*opened* bodies, and choosing a name outside `fv u'` transfers it to the bodies themselves.

```agda
fv-⟶≡  : ∀ {t t'} → t ⟶≡ t' → fv t' ⊑ fv t

fv-body : ∀ {u u'} (L : List Name)
        → (∀ {x} → x ∉ L → (u ^ fvar x) ⟶≡ (u' ^ fvar x))
        → fv u' ⊑ fv u
fv-body {u} {u'} L F {y} y∈ = go
  where
    A  = L ++ fv u ++ fv u'
    x  = fresh A
    a∉ = fresh-∉ A

    x∉L  : x ∉ L
    x∉L  = ∉-++ˡ a∉
    x∉u' : x ∉ fv u'
    x∉u' = ∉-++ʳ (fv u) (∉-++ʳ L a∉)

    step : y ∈ fv (u ^ fvar x)
    step = fv-⟶≡ (F x∉L) (fv-open-lower 0 (fvar x) u' y∈)

    go : y ∈ fv u
    go with fv-open-split 0 (fvar x) u step
    ... | inj₁ q        = q
    ... | inj₂ (here p) = ⊥-elim (x∉u' (subst (_∈ fv u') p y∈))

fv-⟶≡ Cr-Var h = h
fv-⟶≡ Cr-Top h = h
fv-⟶≡ (Cr-App {u} {u'} s₁ s₂) h with ∈-++⁻ (fv u') h
... | inj₁ p = ∈-++⁺ˡ (fv-⟶≡ s₁ p)
... | inj₂ p = ∈-++⁺ʳ (fv u) (fv-⟶≡ s₂ p)
fv-⟶≡ (Cr-Fun {t} {t'} {u} {u'} L st F) h with ∈-++⁻ (fv t') h
... | inj₁ p = ∈-++⁺ˡ (fv-⟶≡ st p)
... | inj₂ p = ∈-++⁺ʳ (fv t) (fv-body {u} {u'} L F p)
fv-⟶≡ (Cr-Beta {t} {u} {u'} {v} {v'} L F sv) h with fv-open-split 0 v' u' h
... | inj₁ p = ∈-++⁺ˡ (∈-++⁺ʳ (fv t) (fv-body {u} {u'} L F p))
... | inj₂ p = ∈-++⁺ʳ (fv t ++ fv u) (fv-⟶≡ sv p)
fv-⟶≡ Cr-TopApp ()
```

## Pointwise reduction of contexts and stacks

```agda
data CtxRed : Ctx → Ctx → Set where
  cr-nil  : CtxRed [] []
  cr-cons : ∀ {Γ Γ' x t t'} → CtxRed Γ Γ' → t ⟶≡ t' → CtxRed ((x , t) ∷ Γ) ((x , t') ∷ Γ')

data StkRed : Stack → Stack → Set where
  sr-nil  : StkRed [] []
  sr-cons : ∀ {s s' α α'} → StkRed s s' → α ⟶≡ α' → StkRed (α ∷ s) (α' ∷ s')

data StkLC : Stack → Set where
  slc-nil  : StkLC []
  slc-cons : ∀ {α s} → LC α → StkLC s → StkLC (α ∷ s)

CtxRed-dom : ∀ {Γ Γ'} → CtxRed Γ Γ' → dom Γ' ≡ dom Γ
CtxRed-dom cr-nil            = refl
CtxRed-dom (cr-cons {x = x} cr _) = cong (x ∷_) (CtxRed-dom cr)

CtxRed-lookup : ∀ {Γ Γ' y t} → CtxRed Γ Γ' → (y , t) ∈ Γ
              → ∃[ t' ] (((y , t') ∈ Γ') × (t ⟶≡ t'))
CtxRed-lookup (cr-cons cr st) (here refl) = _ , here refl , st
CtxRed-lookup (cr-cons cr st) (there m)   with CtxRed-lookup cr m
... | t' , m' , s = t' , there m' , s
```

Reflexivity of both, from prevalidity — this is where local closure of bounds and operands is
used, via Lemma 2.2.

```agda
prevalid-stkLC : ∀ {Γ s} → Γ ∣ s prevalid → StkLC s
prevalid-stkLC P-Ctx1           = slc-nil
prevalid-stkLC (P-Ctx2 _ _ _ _) = slc-nil
prevalid-stkLC (P-Ctx3 p lα _)  = slc-cons lα (prevalid-stkLC p)

CtxRed-refl : ∀ {Γ} → Γ ∣ [] prevalid → CtxRed Γ Γ
CtxRed-refl P-Ctx1            = cr-nil
CtxRed-refl (P-Ctx2 p _ lt _) = cr-cons (CtxRed-refl p) (⟶≡-refl lt)

StkRed-refl : ∀ {s} → StkLC s → StkRed s s
StkRed-refl slc-nil          = sr-nil
StkRed-refl (slc-cons lα sl) = sr-cons (StkRed-refl sl) (⟶≡-refl lα)
```

## Factoring `↣`

```agda
↣-ctx : ∀ {Γ s Γ' s'} → Γ ∣ [] prevalid → Γ ∣ s ↣ Γ' ∣ s' → CtxRed Γ Γ'
↣-ctx pv Ctx-Refl                          = CtxRed-refl pv
↣-ctx (P-Ctx2 p _ _ _) (Ctx-Annotation r st) = cr-cons (↣-ctx p r) st
↣-ctx pv (Ctx-Stack r _)                   = ↣-ctx pv r

↣-stk : ∀ {Γ s Γ' s'} → StkLC s → Γ ∣ s ↣ Γ' ∣ s' → StkRed s s'
↣-stk sl Ctx-Refl                = StkRed-refl sl
↣-stk sl (Ctx-Annotation r _)    = ↣-stk sl r
↣-stk (slc-cons lα sl) (Ctx-Stack r st) = sr-cons (↣-stk sl r) st
```

## Prevalidity survives context reduction

```agda
prevalid-red : ∀ {Γ s Γ' s'} → Γ ∣ s prevalid → CtxRed Γ Γ' → StkRed s s'
             → Γ' ∣ s' prevalid
prevalid-red P-Ctx1 cr-nil sr-nil = P-Ctx1
prevalid-red {Γ' = _} (P-Ctx2 {Γ} {x} {t} p x∉ lt fvt) (cr-cons cr st) sr-nil =
  P-Ctx2 (prevalid-red p cr sr-nil)
         (λ h → x∉ (subst (x ∈_) (CtxRed-dom cr) h))
         (⟶≡-lc lt st)
         (λ h → subst (_ ∈_) (sym (CtxRed-dom cr)) (fvt (fv-⟶≡ st h)))
prevalid-red (P-Ctx3 {Γ} {s} {α} p lα fvα) cr (sr-cons sr st) =
  P-Ctx3 (prevalid-red p cr sr)
         (⟶≡-lc lα st)
         (λ h → subst (_ ∈_) (sym (CtxRed-dom cr)) (fvα (fv-⟶≡ st h)))

↣-prevalid : ∀ {Γ s Γ' s'} → Γ ∣ s prevalid → Γ ∣ s ↣ Γ' ∣ s' → Γ' ∣ s' prevalid
↣-prevalid pv r =
  prevalid-red pv (↣-ctx (prevalid-nil′ pv) r) (↣-stk (prevalid-stkLC pv) r)
  where
    prevalid-nil′ : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ [] prevalid
    prevalid-nil′ P-Ctx1            = P-Ctx1
    prevalid-nil′ q@(P-Ctx2 _ _ _ _) = q
    prevalid-nil′ (P-Ctx3 q _ _)    = prevalid-nil′ q
```

## What this establishes

`⟶≡` does not enlarge the free-variable set; prevalidity survives Figure 3's context reduction;
and a bound can be looked up through a context reduction, with its reduct.

**Next:** Theorem 4.5.
