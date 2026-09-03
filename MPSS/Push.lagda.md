# MPSS: pushing a promotion derivation onto a stack

The heart of the Conjecture 8 plan. A promotion step taken at `Γˢ ∣ s₀` is to be replayed at
`Γᵉ ∣ s₀ ++ s`, where `Γᵉ` narrows some of `Γˢ`'s subtype entries `x ≤ w` to equivalence entries
`x ≡ α`. Two rules do not transfer by themselves, and this module shows that **both are repaired
by a chain rather than blocked**, given one datum each:

- **`Ms-Pro` on a narrowed variable.** `x` no longer has a subtype entry, so it cannot promote to
  `w` in one step. But it *unfolds* to `α` by `Me-Pro`, and if `α` reaches `w` by a chain of
  promotions at the current stack, the step is replaced by that chain. This corrects the earlier
  reading in `MPSS/Diff`: `push-is-false` says the single step is lost, not that the fact is.
- **`Ms-Fun` at a target stack that is not empty.** `Ms-Fun` needs an empty stack; at `α :: s′`
  the rule is `Ms-FOp`, which binds the parameter `x ≡ α` rather than `x ≤ t`. The body
  derivation is then replayed under the narrowing extended by that pair, which needs the same
  datum for `α` and `t`.

Both data have the same shape — the operand reaches the annotation **at every stack**, which is
the strength `PSS/BoundedNarrowing` shows is necessary. The judgement below carries them as
premises, so the push holds outright with the obligations explicit.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Push where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import MPSS.WellFormed
open import MPSS.Narrow using (Transfer; transfer-ext; transfer-pvˢ; ⟶ᵉ-transfer)
open Transfer
open import MPSS.StackPush using (pushᵉ; prevalid-cons; ⟶ᵉ-refl)
open import MPSS.Scope using (⟶ˢ-lc; ⟶ᵉ-lc)
open import MPSS.Wrap using (wrapˢ-fop; wrapˢ-fun)
open import PSS.Close using (open-close; close-open; fv-close)
open import PSS.Syntax using (closeRec)
```

## Chains of promotion

```agda
infixr 5 _◅ˢ_
infix 3 _∣_⊢_⟶ˢ*_
data _∣_⊢_⟶ˢ*_ : Ctx → Stack → Tm → Tm → Set where
  εˢ   : ∀ {Γ s a} → Γ ∣ s prevalid → Γ ∣ s ⊢ a ⟶ˢ* a
  _◅ˢ_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ˢ b → Γ ∣ s ⊢ b ⟶ˢ* c → Γ ∣ s ⊢ a ⟶ˢ* c

_++ˢ_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ˢ* b → Γ ∣ s ⊢ b ⟶ˢ* c → Γ ∣ s ⊢ a ⟶ˢ* c
εˢ _      ++ˢ q = q
(d ◅ˢ p)  ++ˢ q = d ◅ˢ (p ++ˢ q)

⟶ˢ*-prevalid : ∀ {Γ s a b} → Γ ∣ s ⊢ a ⟶ˢ* b → Γ ∣ s prevalid
⟶ˢ*-prevalid (εˢ pv)   = pv
⟶ˢ*-prevalid (d ◅ˢ _)  = ⟶ˢ-prevalid d

⟶ˢ*-lc : ∀ {Γ s a b} → LC a → Γ ∣ s ⊢ a ⟶ˢ* b → LC b
⟶ˢ*-lc la (εˢ _)    = la
⟶ˢ*-lc la (d ◅ˢ p)  = ⟶ˢ*-lc (⟶ˢ-lc la d) p
```

Congruence under an application, and under a popped-operand binder.

```agda
⟶ˢ*-app : ∀ {Γ s a a′ v} → Γ ∣ (v ∷ s) ⊢ a ⟶ˢ* a′ → Γ ∣ s ⊢ app a v ⟶ˢ* app a′ v
⟶ˢ*-app (εˢ pv)   = εˢ (prevalid-pop pv)
⟶ˢ*-app (d ◅ˢ p)  = Ms-App d ◅ˢ ⟶ˢ*-app p

⟶ˢ*-fop : ∀ {Γ s w α a a′} x → x ∉ dom Γ → x ∉ fvStack s → LC a
        → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ˢ* a′
        → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ˢ* lam w (closeRec 0 x a′)
⟶ˢ*-fop x x∉ x∉s la (εˢ pv) =
  εˢ (Pv-Sta (prevalid-strengthen x∉s pv) (head-lc ctx) (head-fv ctx))
  where ctx = prevalid-ctx pv
⟶ˢ*-fop x x∉ x∉s la (d ◅ˢ p) =
  wrapˢ-fop x x∉ x∉s la (⟶ˢ-lc la d) d ◅ˢ ⟶ˢ*-fop x x∉ x∉s (⟶ˢ-lc la d) p

⟶ˢ*-fun : ∀ {Γ w a a′} x → x ∉ dom Γ → LC a
        → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ˢ* a′
        → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ˢ* lam w (closeRec 0 x a′)
⟶ˢ*-fun x x∉ la (εˢ pv)   = εˢ (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
⟶ˢ*-fun x x∉ la (d ◅ˢ p)  =
  wrapˢ-fun x x∉ la (⟶ˢ-lc la d) d ◅ˢ ⟶ˢ*-fun x x∉ (⟶ˢ-lc la d) p
```

## Narrowing with a reachability payload

```agda
Reach : Ctx → Tm → Tm → Set
Reach Γ α w = ∀ {s} → Γ ∣ s prevalid → Γ ∣ s ⊢ α ⟶ˢ* w

infix 4 _▶_
data _▶_ : Ctx → Ctx → Set where

  m-nil  : [] ▶ []

  m-keep : ∀ {Γˢ Γᵉ x a t}
         → Γˢ ▶ Γᵉ
         → ((x , a , t) ∷ Γˢ) ▶ ((x , a , t) ∷ Γᵉ)

  m-eqv  : ∀ {Γˢ Γᵉ x w α}
         → Γˢ ▶ Γᵉ
         → LC α → fv α ⊑ dom Γᵉ
         → ((x , sub , w) ∷ Γˢ) ▶ ((x , eqv , α) ∷ Γᵉ)

▶-refl : ∀ Γ → Γ ▶ Γ
▶-refl []                = m-nil
▶-refl ((x , a , t) ∷ Γ) = m-keep (▶-refl Γ)

▶-dom : ∀ {Γˢ Γᵉ} → Γˢ ▶ Γᵉ → dom Γˢ ≡ dom Γᵉ
▶-dom m-nil                   = refl
▶-dom (m-keep {x = x} n)      = cong (x ∷_) (▶-dom n)
▶-dom (m-eqv {x = x} n _ _)   = cong (x ∷_) (▶-dom n)

▶-prevalid : ∀ {Γˢ Γᵉ} → Γˢ ▶ Γᵉ → Γˢ prevalid → Γᵉ prevalid
▶-prevalid m-nil pv = pv
▶-prevalid (m-keep {a = sub} n) (Pv-Ctx pv x∉ lt ft) =
  Pv-Ctx (▶-prevalid n pv) (subst (_ ∉_) (▶-dom n) x∉) lt
         (λ h → subst (_ ∈_) (▶-dom n) (ft h))
▶-prevalid (m-keep {a = eqv} n) (Pv-EqA pv x∉ lt ft) =
  Pv-EqA (▶-prevalid n pv) (subst (_ ∉_) (▶-dom n) x∉) lt
         (λ h → subst (_ ∈_) (▶-dom n) (ft h))
▶-prevalid (m-eqv n lα fα) (Pv-Ctx pv x∉ _ _) =
  Pv-EqA (▶-prevalid n pv) (subst (_ ∉_) (▶-dom n) x∉) lα fα

▶-≐ : ∀ {Γˢ Γᵉ y β} → Γˢ ▶ Γᵉ → y ≐ β ∈ Γˢ → y ≐ β ∈ Γᵉ
▶-≐ (m-keep n)    (here refl) = here refl
▶-≐ (m-keep n)    (there m)   = there (▶-≐ n m)
▶-≐ (m-eqv n _ _) (there m)   = there (▶-≐ n m)

▶-transfer : ∀ {Γˢ Γᵉ} → Γˢ ▶ Γᵉ → Transfer Γˢ Γᵉ
▶-transfer n = record { t-dom = ▶-dom n ; t-pv = ▶-prevalid n ; t-≐ = ▶-≐ n }

⟶ᵉ-▶ : ∀ {Γˢ Γᵉ s u v} → Γˢ ▶ Γᵉ → Γˢ ∣ s ⊢ u ⟶ᵉ v → Γᵉ ∣ s ⊢ u ⟶ᵉ v
⟶ᵉ-▶ n = ⟶ᵉ-transfer (▶-transfer n)
```

## Pushable derivations

A judgement mirroring `⟶ˢ`, indexed by the two contexts, the derivation's own stack `s₀` and the
extra stack `s` it is pushed onto. The two hard rules carry their `Reach` datum.

```agda
infix 3 _∣_∣_∣_⊢_⇒_
data _∣_∣_∣_⊢_⇒_ : Ctx → Ctx → Stack → Stack → Tm → Tm → Set where

  p-pro : ∀ {Γˢ Γᵉ s₀ s x t}
        → Γˢ ∣ s₀ prevalid → x ≤ t ∈ Γˢ → x ≤ t ∈ Γᵉ
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢ fvar x ⇒ t

  p-pro-eqv : ∀ {Γˢ Γᵉ s₀ s x t α}
        → Γˢ ∣ s₀ prevalid → x ≤ t ∈ Γˢ
        → x ≐ α ∈ Γᵉ → LC α → fv α ⊑ dom Γᵉ
        → Reach Γᵉ α t
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢ fvar x ⇒ t

  p-top : ∀ {Γˢ Γᵉ s₀ s u}
        → Γˢ ∣ s₀ prevalid
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢ u ⇒ Top

  p-equ : ∀ {Γˢ Γᵉ s₀ s u v}
        → Γˢ ∣ s₀ prevalid → Γˢ ∣ s₀ ⊢ u ⟶ᵉ v
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢ u ⇒ v

  p-app : ∀ {Γˢ Γᵉ s₀ s u u′ v}
        → Γˢ ∣ Γᵉ ∣ (v ∷ s₀) ∣ s ⊢ u ⇒ u′
        → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢ app u v ⇒ app u′ v

  p-fop : ∀ {Γˢ Γᵉ s₀ s α t u u′} (L : List Name)
        → (∀ {x} → x ∉ L
             → ((x , eqv , α) ∷ Γˢ) ∣ ((x , eqv , α) ∷ Γᵉ) ∣ s₀ ∣ s ⊢ (u ^ fvar x) ⇒ (u′ ^ fvar x))
        → Γˢ ∣ Γᵉ ∣ (α ∷ s₀) ∣ s ⊢ lam t u ⇒ lam t u′

  p-fun-nil : ∀ {Γˢ Γᵉ t u u′} (L : List Name)
        → (∀ {x} → x ∉ L
             → ((x , sub , t) ∷ Γˢ) ∣ ((x , sub , t) ∷ Γᵉ) ∣ [] ∣ [] ⊢ (u ^ fvar x) ⇒ (u′ ^ fvar x))
        → Γˢ ∣ Γᵉ ∣ [] ∣ [] ⊢ lam t u ⇒ lam t u′

  p-fun-cons : ∀ {Γˢ Γᵉ α s t u u′} (L : List Name)
        → LC α → fv α ⊑ dom Γᵉ
        → (∀ {x} → x ∉ L
             → ((x , sub , t) ∷ Γˢ) ∣ ((x , eqv , α) ∷ Γᵉ) ∣ [] ∣ s ⊢ (u ^ fvar x) ⇒ (u′ ^ fvar x))
        → Γˢ ∣ Γᵉ ∣ [] ∣ (α ∷ s) ⊢ lam t u ⇒ lam t u′
```

Forgetting the payload gives back a promotion step at the unnarrowed context.

```agda
⇒⇒⟶ˢ : ∀ {Γˢ Γᵉ s₀ s a a′} → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢ a ⇒ a′ → Γˢ ∣ s₀ ⊢ a ⟶ˢ a′
⇒⇒⟶ˢ (p-pro pv m _)                   = Ms-Pro pv m
⇒⇒⟶ˢ (p-pro-eqv pv m _ _ _ _)         = Ms-Pro pv m
⇒⇒⟶ˢ (p-top pv)                       = Ms-Top pv
⇒⇒⟶ˢ (p-equ pv e)                     = Ms-Equ pv e
⇒⇒⟶ˢ (p-app d)                        = Ms-App (⇒⇒⟶ˢ d)
⇒⇒⟶ˢ (p-fop {u′ = u′} L F)            = Ms-FOp {u' = u′} L (λ x∉ → ⇒⇒⟶ˢ (F x∉))
⇒⇒⟶ˢ (p-fun-nil {u′ = u′} L F)        = Ms-Fun {u' = u′} L (λ x∉ → ⇒⇒⟶ˢ (F x∉))
⇒⇒⟶ˢ (p-fun-cons {u′ = u′} L _ _ F)   = Ms-Fun {u' = u′} L (λ x∉ → ⇒⇒⟶ˢ (F x∉))
```

## The push

Local closure of the subject is a hypothesis: `Ms-Top` promotes any term, so a derivation does
not carry it.

```agda
⇒-push : ∀ {Γˢ Γᵉ s₀ s a a′}
       → Γˢ ▶ Γᵉ → LC a
       → Γˢ ∣ Γᵉ ∣ s₀ ∣ s ⊢ a ⇒ a′
       → Γᵉ ∣ (s₀ ++ s) prevalid
       → Γᵉ ∣ (s₀ ++ s) ⊢ a ⟶ˢ* a′

⇒-push n la (p-pro _ _ k) pv = Ms-Pro pv k ◅ˢ εˢ pv

⇒-push n la (p-pro-eqv _ _ k lα fα R) pv =
  Ms-Equ pv (Me-Pro pv k (⟶ᵉ-refl pv lα fα)) ◅ˢ R pv

⇒-push n la (p-top _)   pv = Ms-Top pv ◅ˢ εˢ pv
⇒-push n la (p-equ _ e) pv = Ms-Equ pv (pushᵉ (⟶ᵉ-▶ n e) pv) ◅ˢ εˢ pv

⇒-push n (lc-app lu lv) (p-app d) pv =
  ⟶ˢ*-app (⇒-push n lu d
            (Pv-Sta pv (prevalid-head-lc pv₀)
                       (λ h → subst (_ ∈_) (▶-dom n) (prevalid-head-fv pv₀ h))))
  where pv₀ = ⟶ˢ-prevalid (⇒⇒⟶ˢ d)

⇒-push {Γᵉ = Γᵉ} {s = s} n (lc-lam L₀ lt F₀)
       (p-fop {s₀ = s₀} {α = α} {t = t} {u = u} {u′ = u′} L F) pv = chain
  where
    A   = L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′ ++ fvStack (s₀ ++ s)
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L r₁
    r₃  = ∉-++ʳ (dom Γᵉ) r₂
    r₄  = ∉-++ʳ (fv u) r₃
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉Γ : x ∉ dom Γᵉ
    x∉Γ  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ˡ r₄
    x∉s : x ∉ fvStack (s₀ ++ s)
    x∉s  = ∉-++ʳ (fv u′) r₄

    inner : ((x , eqv , α) ∷ Γᵉ) ∣ (s₀ ++ s) ⊢ (u ^ fvar x) ⟶ˢ* (u′ ^ fvar x)
    inner = ⇒-push (m-keep n) (F₀ x∉L₀) (F x∉L)
                   (prevalid-cons (prevalid-pop pv) x∉Γ
                                  (prevalid-head-lc pv) (prevalid-head-fv pv))

    wrapped : Γᵉ ∣ (α ∷ (s₀ ++ s))
                ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ˢ* lam t (closeRec 0 x (u′ ^ fvar x))
    wrapped = ⟶ˢ*-fop x x∉Γ x∉s (F₀ x∉L₀) inner

    chain : Γᵉ ∣ (α ∷ (s₀ ++ s)) ⊢ lam t u ⟶ˢ* lam t u′
    chain =
      subst (λ z → Γᵉ ∣ (α ∷ (s₀ ++ s)) ⊢ lam t z ⟶ˢ* lam t u′) (close-open 0 x u x∉u)
        (subst (λ z → Γᵉ ∣ (α ∷ (s₀ ++ s))
                        ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ˢ* lam t z)
               (close-open 0 x u′ x∉u′) wrapped)

⇒-push {Γᵉ = Γᵉ} n (lc-lam L₀ lt F₀) (p-fun-nil {t = t} {u = u} {u′ = u′} L F) pv =
  chain
  where
    A   = L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L r₁
    r₃  = ∉-++ʳ (dom Γᵉ) r₂
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉Γ : x ∉ dom Γᵉ
    x∉Γ  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ʳ (fv u) r₃

    ctxˢ = prevalid-ctx (⟶ˢ-prevalid (⇒⇒⟶ˢ (F x∉L)))

    fvt : fv t ⊑ dom Γᵉ
    fvt h = subst (_ ∈_) (▶-dom n) (head-fv ctxˢ h)

    inner : ((x , sub , t) ∷ Γᵉ) ∣ [] ⊢ (u ^ fvar x) ⟶ˢ* (u′ ^ fvar x)
    inner = ⇒-push (m-keep n) (F₀ x∉L₀) (F x∉L)
                   (Pv-Nil (Pv-Ctx (prevalid-ctx pv) x∉Γ (head-lc ctxˢ) fvt))

    wrapped : Γᵉ ∣ [] ⊢ lam t (closeRec 0 x (u ^ fvar x))
                       ⟶ˢ* lam t (closeRec 0 x (u′ ^ fvar x))
    wrapped = ⟶ˢ*-fun x x∉Γ (F₀ x∉L₀) inner

    chain : Γᵉ ∣ [] ⊢ lam t u ⟶ˢ* lam t u′
    chain =
      subst (λ z → Γᵉ ∣ [] ⊢ lam t z ⟶ˢ* lam t u′) (close-open 0 x u x∉u)
        (subst (λ z → Γᵉ ∣ [] ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ˢ* lam t z)
               (close-open 0 x u′ x∉u′) wrapped)

⇒-push {Γᵉ = Γᵉ} n (lc-lam L₀ lt F₀)
       (p-fun-cons {α = α} {s = s} {t = t} {u = u} {u′ = u′} L lα fα F) pv = chain
  where
    A   = L₀ ++ L ++ dom Γᵉ ++ fv u ++ fv u′ ++ fvStack s
    x   = fresh A
    a∉  = fresh-∉ A
    r₁  = ∉-++ʳ L₀ a∉
    r₂  = ∉-++ʳ L r₁
    r₃  = ∉-++ʳ (dom Γᵉ) r₂
    r₄  = ∉-++ʳ (fv u) r₃
    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ r₁
    x∉Γ : x ∉ dom Γᵉ
    x∉Γ  = ∉-++ˡ r₂
    x∉u : x ∉ fv u
    x∉u  = ∉-++ˡ r₃
    x∉u′ : x ∉ fv u′
    x∉u′ = ∉-++ˡ r₄
    x∉s : x ∉ fvStack s
    x∉s  = ∉-++ʳ (fv u′) r₄

    inner : ((x , eqv , α) ∷ Γᵉ) ∣ s ⊢ (u ^ fvar x) ⟶ˢ* (u′ ^ fvar x)
    inner = ⇒-push (m-eqv n lα fα) (F₀ x∉L₀) (F x∉L)
                   (prevalid-cons (prevalid-pop pv) x∉Γ
                                  (prevalid-head-lc pv) (prevalid-head-fv pv))

    wrapped : Γᵉ ∣ (α ∷ s)
                ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ˢ* lam t (closeRec 0 x (u′ ^ fvar x))
    wrapped = ⟶ˢ*-fop x x∉Γ x∉s (F₀ x∉L₀) inner

    chain : Γᵉ ∣ (α ∷ s) ⊢ lam t u ⟶ˢ* lam t u′
    chain =
      subst (λ z → Γᵉ ∣ (α ∷ s) ⊢ lam t z ⟶ˢ* lam t u′) (close-open 0 x u x∉u)
        (subst (λ z → Γᵉ ∣ (α ∷ s) ⊢ lam t (closeRec 0 x (u ^ fvar x)) ⟶ˢ* lam t z)
               (close-open 0 x u′ x∉u′) wrapped)
```

## What this establishes

**The push holds, with its obligations named.** A promotion derivation at `Γˢ ∣ s₀` replays as a
*chain* of promotions at `Γᵉ ∣ s₀ ++ s`, for any narrowing of subtype entries to equivalence
entries and any extra stack, provided each narrowed variable and each binder that meets an
operand comes with the fact that the operand reaches the annotation at every stack.

Two things this settles about the earlier reading of the problem:

- **A narrowed variable is not stuck.** `MPSS/Diff`'s `push-is-false` refutes the transport of a
  single step, and was read as an obstruction. It is not: `Me-Pro` unfolds the variable to the
  operand, and the rest is the operand's own chain. Only the *step count* is lost, which is why
  the target has to be `⟶ˢ*` and not `⟶ˢ`, and that is exactly what `≤*wf` allows.
- **The obligation is `Reach`, not well-formedness.** What the two hard cases need is the
  stack-polymorphic reachability `α ⟶ˢ* w` at every stack — the same strength `PSS/NarrowPoly`
  needed for λ⊲, and the same one `PSS/BoundedNarrowing` shows cannot be weakened to the empty
  stack.

The residual for Conjecture 8 is therefore a single statement: **from `Γ ⊢ α ≤*wf w` derive
`Reach Γ α w`.** Nothing structural remains.
