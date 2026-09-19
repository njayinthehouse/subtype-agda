# MPSS: substitutions as lists of single substitutions, and what they preserve

The fundamental lemma of the reducibility argument (`MPSS/CONJ8.md` §17) is about derivations
under a substitution for several names at once. The development has substitution for one name —
`Lem-28-ctx`, `⟶ᵉ-drop` for a `≤`-bound name, `prevalid-subst≡`, `⟶ᵉ-subst≡` for a `≡`-bound one —
and weakening. This module does not redo them for a parallel substitution; it takes a
substitution to be a **list of pairs acting one after the other**, and generates the relation
"`θ` takes `Γ` to `Γ′`" from three kinds of step, one for each lemma:

- substitute a `≤`-bound name in the middle of the context;
- substitute a `≡`-bound name by its own annotation;
- weaken in the middle of the context, which does not act on terms.

By induction on the relation: prevalidity and `⟶ᵉ`, at every stack, are preserved. The relation
lifts under a `≤`-binder and composes.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Morphism where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import MPSS.WellFormed
open import MPSS.Rename using (substCtx; substStack; prevalid-suffix; x∈-mid)
open import MPSS.Subst28 using (Lem-28-ctx; Lem-28-stk; fv-subst)
open import MPSS.SubstDrop using (⟶ᵉ-drop)
open import MPSS.SubstEqv using (⟶ᵉ-subst≡)
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Weakening using (⟶ᵉ-weaken; dom-⊑)
open import MPSS.Conj8Reduction using (_∣_⊢_⟶ᵉ*_; εᵉ; _◅ᵉ_)
open import PSS.Syntax
  using (subst-open; subst-fvar-≢; subst-fresh; subst-intro; subst-lc; ∉-++ˡ; ∉-++ʳ)

```

## Substitutions and their action

```agda
Sub : Set
Sub = List (Name × Tm)

act : Sub → Tm → Tm
act []            u = u
act ((x , α) ∷ θ) u = act θ (u [ x := α ])

actS : Sub → Stack → Stack
actS []            s = s
actS ((x , α) ∷ θ) s = actS θ (substStack x α s)

act-++ : ∀ θ₁ θ₂ u → act (θ₁ ++ θ₂) u ≡ act θ₂ (act θ₁ u)
act-++ []            θ₂ u = refl
act-++ ((x , α) ∷ θ) θ₂ u = act-++ θ θ₂ (u [ x := α ])

actS-++ : ∀ θ₁ θ₂ s → actS (θ₁ ++ θ₂) s ≡ actS θ₂ (actS θ₁ s)
actS-++ []            θ₂ s = refl
actS-++ ((x , α) ∷ θ) θ₂ s = actS-++ θ θ₂ (substStack x α s)

act-Top : ∀ θ → act θ Top ≡ Top
act-Top []            = refl
act-Top ((x , α) ∷ θ) = act-Top θ

act-lam : ∀ θ t u → act θ (lam t u) ≡ lam (act θ t) (act θ u)
act-lam []            t u = refl
act-lam ((x , α) ∷ θ) t u = act-lam θ (t [ x := α ]) (u [ x := α ])

act-app : ∀ θ u v → act θ (app u v) ≡ app (act θ u) (act θ v)
act-app []            u v = refl
act-app ((x , α) ∷ θ) u v = act-app θ (u [ x := α ]) (v [ x := α ])

actS-nil : ∀ θ → actS θ [] ≡ []
actS-nil []            = refl
actS-nil ((x , α) ∷ θ) = actS-nil θ

actS-cons : ∀ θ v s → actS θ (v ∷ s) ≡ act θ v ∷ actS θ s
actS-cons []            v s = refl
actS-cons ((x , α) ∷ θ) v s = actS-cons θ (v [ x := α ]) (substStack x α s)
```

## The relation

```agda
infix 3 _⊢_⇒_
data _⊢_⇒_ : Ctx → Sub → Ctx → Set where

  m-id  : ∀ {Γ} → Γ ⊢ [] ⇒ Γ

  m-sub : ∀ (Δ : Ctx) {Γ x t α θ Γ′}
        → LC α → fv α ⊑ dom Γ
        → (substCtx x α Δ ++ Γ) ⊢ θ ⇒ Γ′
        → (Δ ++ (x , sub , t) ∷ Γ) ⊢ (x , α) ∷ θ ⇒ Γ′

  m-eqv : ∀ (Δ : Ctx) {Γ x α θ Γ′}
        → LC α → fv α ⊑ dom Γ
        → (substCtx x α Δ ++ Γ) ⊢ θ ⇒ Γ′
        → (Δ ++ (x , eqv , α) ∷ Γ) ⊢ (x , α) ∷ θ ⇒ Γ′

  m-wk  : ∀ (Δ Θ : Ctx) {Γ θ Γ′}
        → (Δ ++ Θ ++ Γ) prevalid
        → (Δ ++ Θ ++ Γ) ⊢ θ ⇒ Γ′
        → (Δ ++ Γ) ⊢ θ ⇒ Γ′
```

The names of every context the relation passes through. A name outside them is distinct from
every substituted name, is not free in any substituted term, and is not bound by any weakening.

```agda
names : ∀ {Γ θ Γ′} → Γ ⊢ θ ⇒ Γ′ → List Name
names (m-id {Γ})                              = dom Γ
names (m-sub Δ {Γ} {x} {t} _ _ m)             = dom (Δ ++ (x , sub , t) ∷ Γ) ++ names m
names (m-eqv Δ {Γ} {x} {α} _ _ m)             = dom (Δ ++ (x , eqv , α) ∷ Γ) ++ names m
names (m-wk Δ Θ {Γ} _ m)                      = dom (Δ ++ Γ) ++ names m
```

## What is preserved

```agda
stk-weaken : ∀ (Δ Θ : Ctx) {Γ s} → (Δ ++ Θ ++ Γ) prevalid → (Δ ++ Γ) ∣ s prevalid
           → (Δ ++ Θ ++ Γ) ∣ s prevalid
stk-weaken Δ Θ pv (Pv-Nil _)        = Pv-Nil pv
stk-weaken Δ Θ pv (Pv-Sta p lα fα)  = Pv-Sta (stk-weaken Δ Θ pv p) lα (λ h → dom-⊑ Δ Θ (fα h))

m-pv : ∀ {Γ θ Γ′ s} → Γ ⊢ θ ⇒ Γ′ → Γ ∣ s prevalid → Γ′ ∣ actS θ s prevalid
m-pv m-id              pv = pv
m-pv (m-sub Δ lα fα m) pv = m-pv m (Lem-28-stk Δ lα fα pv)
m-pv (m-eqv Δ lα fα m) pv = m-pv m (Lem-28-stk Δ lα fα pv)
m-pv (m-wk Δ Θ pvΘ m)  pv = m-pv m (stk-weaken Δ Θ pvΘ pv)

m-e : ∀ {Γ θ Γ′ s u v} → Γ ⊢ θ ⇒ Γ′ → Γ ∣ s ⊢ u ⟶ᵉ v → Γ′ ∣ actS θ s ⊢ act θ u ⟶ᵉ act θ v
m-e m-id              d = d
m-e (m-sub Δ lα fα m) d = m-e m (⟶ᵉ-drop Δ lα fα d)
m-e (m-eqv Δ {x = x} lα fα m) d =
  m-e m (⟶ᵉ-subst≡ Δ x lα lα fα d (⟶ᵉ-refl (Pv-Nil pvΓ) lα fα))
  where pvΓ = tail-prevalid (prevalid-suffix Δ (prevalid-ctx (⟶ᵉ-prevalid d)))
m-e (m-wk Δ Θ pvΘ m)  d = m-e m (⟶ᵉ-weaken Δ Θ (stk-weaken Δ Θ pvΘ (⟶ᵉ-prevalid d)) d)

m-e* : ∀ {Γ θ Γ′ s u v} → Γ ⊢ θ ⇒ Γ′ → Γ ∣ s ⊢ u ⟶ᵉ* v → Γ′ ∣ actS θ s ⊢ act θ u ⟶ᵉ* act θ v
m-e* m εᵉ       = εᵉ
m-e* m (e ◅ᵉ p) = m-e m e ◅ᵉ m-e* m p
```

## Composition

```agda
infixr 5 _⊙_
_⊙_ : ∀ {Γ θ₁ Γ₁ θ₂ Γ₂} → Γ ⊢ θ₁ ⇒ Γ₁ → Γ₁ ⊢ θ₂ ⇒ Γ₂ → Γ ⊢ θ₁ ++ θ₂ ⇒ Γ₂
m-id            ⊙ n = n
m-sub Δ lα fα m ⊙ n = m-sub Δ lα fα (m ⊙ n)
m-eqv Δ lα fα m ⊙ n = m-eqv Δ lα fα (m ⊙ n)
m-wk Δ Θ pv m   ⊙ n = m-wk Δ Θ pv (m ⊙ n)

names-⊙ : ∀ {Γ θ₁ Γ₁ θ₂ Γ₂} (m : Γ ⊢ θ₁ ⇒ Γ₁) (n : Γ₁ ⊢ θ₂ ⇒ Γ₂) {z}
        → z ∉ names m → z ∉ names n → z ∉ names (m ⊙ n)
names-⊙ m-id n z∉m z∉n h = z∉n h
names-⊙ (m-sub Δ {Γ} {x} {t} _ _ m) n z∉m z∉n h with ∈-++⁻ (dom (Δ ++ (x , sub , t) ∷ Γ)) h
... | inj₁ p = z∉m (∈-++⁺ˡ p)
... | inj₂ q = names-⊙ m n (∉-++ʳ (dom (Δ ++ (x , sub , t) ∷ Γ)) z∉m) z∉n q
names-⊙ (m-eqv Δ {Γ} {x} {α} _ _ m) n z∉m z∉n h with ∈-++⁻ (dom (Δ ++ (x , eqv , α) ∷ Γ)) h
... | inj₁ p = z∉m (∈-++⁺ˡ p)
... | inj₂ q = names-⊙ m n (∉-++ʳ (dom (Δ ++ (x , eqv , α) ∷ Γ)) z∉m) z∉n q
names-⊙ (m-wk Δ Θ {Γ} _ m) n z∉m z∉n h with ∈-++⁻ (dom (Δ ++ Γ)) h
... | inj₁ p = z∉m (∈-++⁺ˡ p)
... | inj₂ q = names-⊙ m n (∉-++ʳ (dom (Δ ++ Γ)) z∉m) z∉n q
```

## Names the relation does not pass through

```agda
src-∉ : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) {z} → z ∉ names m → z ∉ dom Γ
src-∉ m-id              z∉ = z∉
src-∉ (m-sub Δ _ _ m)   z∉ = ∉-++ˡ z∉
src-∉ (m-eqv Δ _ _ m)   z∉ = ∉-++ˡ z∉
src-∉ (m-wk Δ Θ _ m)    z∉ = ∉-++ˡ z∉

act-fvar : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) {z} → z ∉ names m → act θ (fvar z) ≡ fvar z
act-fvar m-id z∉ = refl
act-fvar (m-sub Δ {Γ} {x} {t} {α} {θ} _ _ m) {z} z∉ =
  trans (cong (act θ) (subst-fvar-≢ {x} {z} α x≢z))
        (act-fvar m (∉-++ʳ (dom (Δ ++ (x , sub , t) ∷ Γ)) z∉))
  where
    x≢z : x ≢ z
    x≢z p = ∉-++ˡ z∉ (subst (_∈ dom (Δ ++ (x , sub , t) ∷ Γ)) p (x∈-mid Δ {Γ} {x} {sub} {t}))
act-fvar (m-eqv Δ {Γ} {x} {α} {θ} _ _ m) {z} z∉ =
  trans (cong (act θ) (subst-fvar-≢ {x} {z} α x≢z))
        (act-fvar m (∉-++ʳ (dom (Δ ++ (x , eqv , α) ∷ Γ)) z∉))
  where
    x≢z : x ≢ z
    x≢z p = ∉-++ˡ z∉ (subst (_∈ dom (Δ ++ (x , eqv , α) ∷ Γ)) p (x∈-mid Δ {Γ} {x} {eqv} {α}))
act-fvar (m-wk Δ Θ {Γ} _ m) z∉ = act-fvar m (∉-++ʳ (dom (Δ ++ Γ)) z∉)
```

## Under a `≤`-binder

A relation lifts under a binder whose name it does not pass through; the binder's annotation is
acted on with everything else.

```agda
up : ∀ {Γ θ Γ′} z w (m : Γ ⊢ θ ⇒ Γ′) → z ∉ names m → ((z , sub , w) ∷ Γ) prevalid
   → ((z , sub , w) ∷ Γ) ⊢ θ ⇒ ((z , sub , act θ w) ∷ Γ′)
up z w m-id z∉ pv = m-id
up z w (m-sub Δ {Γ} {x} {t} {α} lα fα m) z∉ pv =
  m-sub ((z , sub , w) ∷ Δ) lα fα
        (up z (w [ x := α ]) m (∉-++ʳ (dom (Δ ++ (x , sub , t) ∷ Γ)) z∉)
            (Lem-28-ctx ((z , sub , w) ∷ Δ) lα fα pv))
up z w (m-eqv Δ {Γ} {x} {α} lα fα m) z∉ pv =
  m-eqv ((z , sub , w) ∷ Δ) lα fα
        (up z (w [ x := α ]) m (∉-++ʳ (dom (Δ ++ (x , eqv , α) ∷ Γ)) z∉)
            (Lem-28-ctx ((z , sub , w) ∷ Δ) lα fα pv))
up z w (m-wk Δ Θ {Γ} pvΘ m) z∉ (Pv-Ctx _ _ lw fw) =
  m-wk ((z , sub , w) ∷ Δ) Θ pv′ (up z w m z∉′ pv′)
  where
    z∉′ = ∉-++ʳ (dom (Δ ++ Γ)) z∉
    pv′ : ((z , sub , w) ∷ Δ ++ Θ ++ Γ) prevalid
    pv′ = Pv-Ctx pvΘ (src-∉ m z∉′) lw (λ h → dom-⊑ Δ Θ (fw h))

names-up : ∀ {Γ θ Γ′} z w (m : Γ ⊢ θ ⇒ Γ′) (z∉ : z ∉ names m) (pv : ((z , sub , w) ∷ Γ) prevalid)
           {y} → y ≢ z → y ∉ names m → y ∉ names (up z w m z∉ pv)
names-up z w m-id z∉ pv y≢ y∉ (here p)  = y≢ p
names-up z w m-id z∉ pv y≢ y∉ (there h) = y∉ h
names-up z w (m-sub Δ {Γ} {x} {t} {α} lα fα m) z∉ pv y≢ y∉ (here p) = y≢ p
names-up z w (m-sub Δ {Γ} {x} {t} {α} lα fα m) z∉ pv y≢ y∉ (there h)
  with ∈-++⁻ (dom (Δ ++ (x , sub , t) ∷ Γ)) h
... | inj₁ q = y∉ (∈-++⁺ˡ q)
... | inj₂ q = names-up z (w [ x := α ]) m _ _ y≢ (∉-++ʳ (dom (Δ ++ (x , sub , t) ∷ Γ)) y∉) q
names-up z w (m-eqv Δ {Γ} {x} {α} lα fα m) z∉ pv y≢ y∉ (here p) = y≢ p
names-up z w (m-eqv Δ {Γ} {x} {α} lα fα m) z∉ pv y≢ y∉ (there h)
  with ∈-++⁻ (dom (Δ ++ (x , eqv , α) ∷ Γ)) h
... | inj₁ q = y∉ (∈-++⁺ˡ q)
... | inj₂ q = names-up z (w [ x := α ]) m _ _ y≢ (∉-++ʳ (dom (Δ ++ (x , eqv , α) ∷ Γ)) y∉) q
names-up z w (m-wk Δ Θ {Γ} pvΘ m) z∉ (Pv-Ctx _ _ lw fw) y≢ y∉ (here p) = y≢ p
names-up z w (m-wk Δ Θ {Γ} pvΘ m) z∉ (Pv-Ctx _ _ lw fw) y≢ y∉ (there h)
  with ∈-++⁻ (dom (Δ ++ Γ)) h
... | inj₁ q = y∉ (∈-++⁺ˡ q)
... | inj₂ q = names-up z w m _ _ y≢ (∉-++ʳ (dom (Δ ++ Γ)) y∉) q
```

## The action and opening, free names, local closure

```agda
dom-tail : ∀ (Δ : Ctx) {Γ e z} → z ∈ dom Γ → z ∈ dom (Δ ++ e ∷ Γ)
dom-tail []      h = there h
dom-tail (_ ∷ Δ) h = there (dom-tail Δ h)

act-open : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) {z} → z ∉ names m → ∀ u
         → act θ (u ^ fvar z) ≡ act θ u ^ fvar z
act-open m-id z∉ u = refl
act-open (m-sub Δ {Γ} {x} {t} {α} {θ} lα fα m) {z} z∉ u =
  trans (cong (act θ) (trans (subst-open lα 0 (fvar z) u x)
                             (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ {x} {z} α x≢z))))
        (act-open m (∉-++ʳ (dom (Δ ++ (x , sub , t) ∷ Γ)) z∉) (u [ x := α ]))
  where
    x≢z : x ≢ z
    x≢z p = ∉-++ˡ z∉ (subst (_∈ dom (Δ ++ (x , sub , t) ∷ Γ)) p (x∈-mid Δ {Γ} {x} {sub} {t}))
act-open (m-eqv Δ {Γ} {x} {α} {θ} lα fα m) {z} z∉ u =
  trans (cong (act θ) (trans (subst-open lα 0 (fvar z) u x)
                             (cong (λ q → openRec 0 q (u [ x := α ])) (subst-fvar-≢ {x} {z} α x≢z))))
        (act-open m (∉-++ʳ (dom (Δ ++ (x , eqv , α) ∷ Γ)) z∉) (u [ x := α ]))
  where
    x≢z : x ≢ z
    x≢z p = ∉-++ˡ z∉ (subst (_∈ dom (Δ ++ (x , eqv , α) ∷ Γ)) p (x∈-mid Δ {Γ} {x} {eqv} {α}))
act-open (m-wk Δ Θ {Γ} _ m) z∉ u = act-open m (∉-++ʳ (dom (Δ ++ Γ)) z∉) u

act-∉ : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) {z} → z ∉ names m → ∀ u → z ∉ fv u → z ∉ fv (act θ u)
act-∉ m-id z∉ u z∉u = z∉u
act-∉ (m-sub Δ {Γ} {x} {t} {α} lα fα m) {z} z∉ u z∉u =
  act-∉ m (∉-++ʳ (dom (Δ ++ (x , sub , t) ∷ Γ)) z∉) (u [ x := α ]) step
  where
    step : z ∉ fv (u [ x := α ])
    step h with fv-subst u x α h
    ... | inj₁ (p , _) = z∉u p
    ... | inj₂ q       = ∉-++ˡ z∉ (dom-tail Δ (fα q))
act-∉ (m-eqv Δ {Γ} {x} {α} lα fα m) {z} z∉ u z∉u =
  act-∉ m (∉-++ʳ (dom (Δ ++ (x , eqv , α) ∷ Γ)) z∉) (u [ x := α ]) step
  where
    step : z ∉ fv (u [ x := α ])
    step h with fv-subst u x α h
    ... | inj₁ (p , _) = z∉u p
    ... | inj₂ q       = ∉-++ˡ z∉ (dom-tail Δ (fα q))
act-∉ (m-wk Δ Θ {Γ} _ m) z∉ u z∉u = act-∉ m (∉-++ʳ (dom (Δ ++ Γ)) z∉) u z∉u

act-lc : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) {u} → LC u → LC (act θ u)
act-lc m-id              lu = lu
act-lc (m-sub Δ lα fα m) lu = act-lc m (subst-lc lu lα)
act-lc (m-eqv Δ lα fα m) lu = act-lc m (subst-lc lu lα)
act-lc (m-wk Δ Θ _ m)    lu = act-lc m lu
```

Extending by `z := v` at the end: the body opened at `z`, acted on, is the acted-on body opened
at `v`.

```agda
act-open-snoc : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) {z v} → z ∉ names m → LC v → ∀ u → z ∉ fv u
              → act (θ ++ (z , v) ∷ []) (u ^ fvar z) ≡ act θ u ^ v
act-open-snoc {θ = θ} m {z} {v} z∉ lv u z∉u =
  trans (act-++ θ ((z , v) ∷ []) (u ^ fvar z))
        (trans (cong (_[ z := v ]) (act-open m z∉ u))
               (sym (subst-intro {act θ u} lv z (act-∉ m z∉ u z∉u))))

act-snoc-fresh : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) {z v} → z ∉ names m → ∀ u → z ∉ fv u
               → act (θ ++ (z , v) ∷ []) u ≡ act θ u
act-snoc-fresh {θ = θ} m {z} {v} z∉ u z∉u =
  trans (act-++ θ ((z , v) ∷ []) u) (subst-fresh {act θ u} z v (act-∉ m z∉ u z∉u))
```

## Opening at a term, weakening the target, and instantiating a binder

```agda
act-openT : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) u v → act θ (u ^ v) ≡ act θ u ^ act θ v
act-openT m-id u v = refl
act-openT (m-sub Δ {x = x} {α = α} {θ = θ} lα fα m) u v =
  trans (cong (act θ) (subst-open lα 0 v u x)) (act-openT m (u [ x := α ]) (v [ x := α ]))
act-openT (m-eqv Δ {x = x} {α = α} {θ = θ} lα fα m) u v =
  trans (cong (act θ) (subst-open lα 0 v u x)) (act-openT m (u [ x := α ]) (v [ x := α ]))
act-openT (m-wk Δ Θ _ m) u v = act-openT m u v

post-wk : ∀ {Γ θ Γ′} → Γ ⊢ θ ⇒ Γ′ → ∀ (Δ : Ctx) → (Δ ++ Γ′) prevalid → Γ ⊢ θ ⇒ (Δ ++ Γ′)
post-wk m-id              Δ pv = m-wk [] Δ pv m-id
post-wk (m-sub Δ₁ lα fα m) Δ pv = m-sub Δ₁ lα fα (post-wk m Δ pv)
post-wk (m-eqv Δ₁ lα fα m) Δ pv = m-eqv Δ₁ lα fα (post-wk m Δ pv)
post-wk (m-wk Δ₁ Θ pvΘ m)  Δ pv = m-wk Δ₁ Θ pvΘ (post-wk m Δ pv)

names-post-wk : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) (Δ : Ctx) (pv : (Δ ++ Γ′) prevalid) {z}
              → z ∉ names m → z ∉ dom (Δ ++ Γ′) → z ∉ names (post-wk m Δ pv)
names-post-wk (m-id {Γ}) Δ pv z∉ z∉Δ h with ∈-++⁻ (dom Γ) h
... | inj₁ p = z∉ p
... | inj₂ q = z∉Δ q
names-post-wk (m-sub Δ₁ {Γ} {x} {t} lα fα m) Δ pv z∉ z∉Δ h
  with ∈-++⁻ (dom (Δ₁ ++ (x , sub , t) ∷ Γ)) h
... | inj₁ p = z∉ (∈-++⁺ˡ p)
... | inj₂ q = names-post-wk m Δ pv (∉-++ʳ (dom (Δ₁ ++ (x , sub , t) ∷ Γ)) z∉) z∉Δ q
names-post-wk (m-eqv Δ₁ {Γ} {x} {α} lα fα m) Δ pv z∉ z∉Δ h
  with ∈-++⁻ (dom (Δ₁ ++ (x , eqv , α) ∷ Γ)) h
... | inj₁ p = z∉ (∈-++⁺ˡ p)
... | inj₂ q = names-post-wk m Δ pv (∉-++ʳ (dom (Δ₁ ++ (x , eqv , α) ∷ Γ)) z∉) z∉Δ q
names-post-wk (m-wk Δ₁ Θ {Γ} pvΘ m) Δ pv z∉ z∉Δ h with ∈-++⁻ (dom (Δ₁ ++ Γ)) h
... | inj₁ p = z∉ (∈-++⁺ˡ p)
... | inj₂ q = names-post-wk m Δ pv (∉-++ʳ (dom (Δ₁ ++ Γ)) z∉) z∉Δ q
```

`inst`: from `θ : Γ ⇒ Γ′`, a binder `z ≤ t` over `Γ` and a term `v` of an extension `Δ ++ Γ′`, the
substitution `θ, z := v` from `z ≤ t, Γ` to `Δ ++ Γ′` — weaken the target, lift under `z`,
substitute `z` at the head.

```agda
inst : ∀ {Γ θ Γ′} (m : Γ ⊢ θ ⇒ Γ′) (Δ : Ctx) {z t v}
     → z ∉ names m → z ∉ dom (Δ ++ Γ′)
     → ((z , sub , t) ∷ Γ) prevalid → (Δ ++ Γ′) prevalid
     → LC v → fv v ⊑ dom (Δ ++ Γ′)
     → ((z , sub , t) ∷ Γ) ⊢ θ ++ (z , v) ∷ [] ⇒ (Δ ++ Γ′)
inst m Δ {z} {t} z∉ z∉Δ pv pvΔ lv fvv =
  up z t (post-wk m Δ pvΔ) (names-post-wk m Δ pvΔ z∉ z∉Δ) pv ⊙ m-sub [] lv fvv m-id
```

## What this establishes

Substitutions as lists, the relation `Γ ⊢ θ ⇒ Γ′` generated by the three kinds of step the
development has a lemma for, and: prevalidity and `⟶ᵉ` are preserved at every stack (`m-pv`,
`m-e`); the relation composes and lifts under a `≤`-binder; the action commutes with opening at a
name the relation does not pass through. Goodness of a substitution, and the fundamental lemma,
are `MPSS/Fundamental`'s.
