# MPSS: the measure for the variant's diamond

Both sides of the join recursion share one configuration `(Γ, s, t)`. For the variant, a
measure on that configuration alone decreases at every recursive call, which `MPSS/NoMeasure`
shows is impossible for the original: there the unfolded definition keeps reducing at the current
stack, here it reduces at the empty one and never re-enters what it left.

The measure is the size of the focus term, plus the sizes of the stack entries, plus the sizes of
the annotations of the context entries *reachable* from the free names of the focus and the stack.
Reachability is computed in one pass down the context, which is enough because prevalidity makes
an annotation mention only earlier names: an entry counts if its name is reachable, and then its
annotation's names become reachable in turn.

- Unfolding `x ≡ α` replaces the focus `x` by `α` at the empty stack: `x`'s entry, which counted,
  no longer needs to, and it counted at least `|α|`; the term grows to `|α|` and the stack is dropped.
- Pushing an operand moves size from the term to the stack; popping one into a binding moves it
  from the stack to the context.
- Opening a body at a fresh name adds nothing reachable beyond what the abstraction already
  reached, and loses the abstraction node.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantMeasure where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_; ≤-refl; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; n≤1+n; m≤m+n; m≤n+m; +-assoc; +-comm; +-identityʳ; +-suc; ≤-reflexive)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Scope using (fv-open-split)
open import MPSS.WellFormed
```

## Sizes

```agda
tsize : Tm → ℕ
tsize (bvar _)  = 1
tsize (fvar _)  = 1
tsize Top       = 1
tsize (lam t u) = 1 + tsize t + tsize u
tsize (app u v) = 1 + tsize u + tsize v

ssize : Stack → ℕ
ssize []      = 0
ssize (α ∷ s) = tsize α + ssize s

tsize-open : ∀ k x t → tsize (openRec k (fvar x) t) ≡ tsize t
tsize-open k x (bvar i) with k ≟ i
... | yes _ = refl
... | no  _ = refl
tsize-open k x (fvar _)  = refl
tsize-open k x Top       = refl
tsize-open k x (lam t u) rewrite tsize-open k x t | tsize-open (suc k) x u = refl
tsize-open k x (app u v) rewrite tsize-open k x u | tsize-open k x v = refl
```

## Reachable annotations

```agda
rs : Ctx → List Name → ℕ
rs []                N = 0
rs ((y , _ , w) ∷ Γ) N with y ∈? N
... | yes _ = tsize w + rs Γ (fv w ++ N)
... | no  _ = rs Γ N

rs-mono : ∀ Γ {N N′} → N ⊑ N′ → rs Γ N ≤ rs Γ N′
rs-mono [] inc = z≤n
rs-mono ((y , a , w) ∷ Γ) {N} {N′} inc with y ∈? N | y ∈? N′
... | yes _ | yes _  = +-monoʳ-≤ (tsize w) (rs-mono Γ (λ h → go h))
  where
    go : ∀ {z} → z ∈ (fv w ++ N) → z ∈ (fv w ++ N′)
    go h with ∈-++⁻ (fv w) h
    ... | inj₁ p = ∈-++⁺ˡ p
    ... | inj₂ p = ∈-++⁺ʳ (fv w) (inc p)
... | yes p | no  q  = ⊥-elim (q (inc p))
... | no  _ | yes _  = ≤-trans (rs-mono Γ inc) (≤-trans (rs-mono Γ (∈-++⁺ʳ (fv w))) (m≤n+m _ (tsize w)))
... | no  _ | no  _  = rs-mono Γ inc

rs-cons : ∀ Γ {y a w N} → rs ((y , a , w) ∷ Γ) N ≤ tsize w + rs Γ (fv w ++ N)
rs-cons Γ {y} {a} {w} {N} with y ∈? N
... | yes _ = ≤-refl
... | no  _ = ≤-trans (rs-mono Γ (∈-++⁺ʳ (fv w))) (m≤n+m _ (tsize w))
```

A name the context does not bind is never matched, so adding it to the set changes nothing.

```agda
rs-ext : ∀ Γ {x N} → x ∉ dom Γ → ∀ M → rs Γ (M ++ x ∷ N) ≡ rs Γ (M ++ N)
rs-ext [] x∉ M = refl
rs-ext ((y , a , w) ∷ Γ) {x} {N} x∉ M with y ∈? (M ++ x ∷ N) | y ∈? (M ++ N)
... | yes p | yes _ =
  cong (tsize w +_)
       (trans (cong (rs Γ) (sym (++-assoc (fv w) M (x ∷ N))))
              (trans (rs-ext Γ (λ h → x∉ (there h)) (fv w ++ M))
                     (cong (rs Γ) (++-assoc (fv w) M N))))
... | yes p | no  q = ⊥-elim (q (drop p))
  where
    drop : y ∈ (M ++ x ∷ N) → y ∈ (M ++ N)
    drop h with ∈-++⁻ M h
    ... | inj₁ a           = ∈-++⁺ˡ a
    ... | inj₂ (here refl) = ⊥-elim (x∉ (here refl))
    ... | inj₂ (there b)   = ∈-++⁺ʳ M b
... | no  p | yes q = ⊥-elim (p (add q))
  where
    add : y ∈ (M ++ N) → y ∈ (M ++ x ∷ N)
    add h with ∈-++⁻ M h
    ... | inj₁ a = ∈-++⁺ˡ a
    ... | inj₂ b = ∈-++⁺ʳ M (there b)
... | no  _ | no  _ = rs-ext Γ (λ h → x∉ (there h)) M

rs-fresh : ∀ Γ {x N} → x ∉ dom Γ → rs Γ (x ∷ N) ≡ rs Γ N
rs-fresh Γ x∉ = rs-ext Γ x∉ []
```

Monotonicity up to a fresh name.

```agda
rs-mono-fresh : ∀ Γ {x N N′} → x ∉ dom Γ → N′ ⊑ (x ∷ N) → rs Γ N′ ≤ rs Γ N
rs-mono-fresh Γ {x} {N} x∉ inc = ≤-trans (rs-mono Γ inc) (≤-reflexive (rs-fresh Γ x∉))
```

Pulling a definition: its entry counted, and what its annotation reaches was counted below it.

```agda
rs-pull : ∀ Γ {x a α N} → Γ prevalid → (x , a , α) ∈ Γ → x ∈ N → rs Γ (fv α) + tsize α ≤ rs Γ N
rs-pull ((y , b , w) ∷ Γ) {x} {a} {α} {N} pv (here refl) x∈ with x ∈? N | x ∈? fv α
... | no  q | _     = ⊥-elim (q x∈)
... | yes _ | yes p = ⊥-elim (head-∉ pv (head-fv pv p))
  where
    head-∉ : ∀ {Γ′ z c t} → ((z , c , t) ∷ Γ′) prevalid → z ∉ dom Γ′
    head-∉ (Pv-Ctx _ z∉ _ _) = z∉
    head-∉ (Pv-EqA _ z∉ _ _) = z∉
... | yes _ | no  _ =
  subst (λ n → rs Γ (fv α) + tsize α ≤ n) (+-comm (rs Γ (fv α ++ N)) (tsize α))
        (+-monoˡ-≤ (tsize α) (rs-mono Γ (∈-++⁺ˡ)))
rs-pull ((y , b , w) ∷ Γ) {x} {a} {α} {N} pv (there m) x∈ with y ∈? N | y ∈? fv α
... | _     | yes p = ⊥-elim (y∉α p)
  where
    y∉α : y ∉ fv α
    y∉α h = head-∉ pv (prevalid-bound-fv (tail-prevalid pv) m h)
      where
        head-∉ : ∀ {Γ′ z c t} → ((z , c , t) ∷ Γ′) prevalid → z ∉ dom Γ′
        head-∉ (Pv-Ctx _ z∉ _ _) = z∉
        head-∉ (Pv-EqA _ z∉ _ _) = z∉
... | yes _ | no  _ =
  ≤-trans (rs-pull Γ (tail-prevalid pv) m x∈)
          (≤-trans (rs-mono Γ (∈-++⁺ʳ (fv w))) (m≤n+m _ (tsize w)))
... | no  _ | no  _ = rs-pull Γ (tail-prevalid pv) m x∈
```

## The measure, and the inequalities the cases need

```agda
Φ : Ctx → Stack → Tm → ℕ
Φ Γ s t = rs Γ (fv t ++ fvStack s) + ssize s + tsize t
```

Every focus term has size `suc r` for some `r`, so a strict inequality against the measure is a
plain inequality against the measure with that `suc` peeled off.

```agda
lt-of : ∀ {l} r a → l ≤ r + a → l < r + suc a
lt-of r a h = ≤-trans (s≤s h) (≤-reflexive (sym (+-suc r a)))

⊑-++[] : ∀ (M : List Name) → (M ++ []) ⊑ M
⊑-++[] M h with ∈-++⁻ M h
... | inj₁ p = p
... | inj₂ ()

open ≡-Reasoning

arith₁ : ∀ r v s u → r + (v + s) + u ≡ r + s + (u + v)
arith₁ r v s u = begin
  r + (v + s) + u   ≡⟨ cong (_+ u) (cong (r +_) (+-comm v s)) ⟩
  r + (s + v) + u   ≡⟨ cong (_+ u) (sym (+-assoc r s v)) ⟩
  r + s + v + u     ≡⟨ +-assoc (r + s) v u ⟩
  r + s + (v + u)   ≡⟨ cong ((r + s) +_) (+-comm v u) ⟩
  r + s + (u + v)   ∎

arith₂ : ∀ a r s u → a + r + s + u ≡ r + s + (a + u)
arith₂ a r s u = begin
  a + r + s + u     ≡⟨ cong (λ n → n + s + u) (+-comm a r) ⟩
  r + a + s + u     ≡⟨ cong (_+ u) (+-assoc r a s) ⟩
  r + (a + s) + u   ≡⟨ cong (λ n → r + n + u) (+-comm a s) ⟩
  r + (s + a) + u   ≡⟨ cong (_+ u) (sym (+-assoc r s a)) ⟩
  r + s + a + u     ≡⟨ +-assoc (r + s) a u ⟩
  r + s + (a + u)   ∎

arith₃ : ∀ a r s u → a + r + s + u ≡ r + (a + s) + u
arith₃ a r s u = begin
  a + r + s + u     ≡⟨ cong (λ n → n + s + u) (+-comm a r) ⟩
  r + a + s + u     ≡⟨ cong (_+ u) (+-assoc r a s) ⟩
  r + (a + s) + u   ∎
```

Unfolding a definition at the empty stack.

```agda
Φ-pull : ∀ {Γ s x a α} → Γ prevalid → (x , a , α) ∈ Γ → Φ Γ [] α < Φ Γ s (fvar x)
Φ-pull {Γ} {s} {x} {a} {α} pv m = lt-of (rs Γ (x ∷ fvStack s) + ssize s) 0 bound
  where
    bound : rs Γ (fv α ++ []) + 0 + tsize α ≤ rs Γ (x ∷ fvStack s) + ssize s + 0
    bound = ≤-trans (+-monoˡ-≤ (tsize α) (≤-trans (≤-reflexive (+-identityʳ _)) (rs-mono Γ (⊑-++[] (fv α)))))
            (≤-trans (rs-pull Γ pv m (here refl))
            (≤-trans (m≤m+n _ (ssize s)) (≤-reflexive (sym (+-identityʳ _)))))
```

Application: the operator at the operand's stack, and the operand at the empty stack.

```agda
Φ-app-op : ∀ Γ s u v → Φ Γ (v ∷ s) u < Φ Γ s (app u v)
Φ-app-op Γ s u v = lt-of (rs Γ ((fv u ++ fv v) ++ fvStack s) + ssize s) (tsize u + tsize v) (≤-reflexive eq)
  where
    eq : rs Γ (fv u ++ fv v ++ fvStack s) + (tsize v + ssize s) + tsize u
       ≡ rs Γ ((fv u ++ fv v) ++ fvStack s) + ssize s + (tsize u + tsize v)
    eq rewrite ++-assoc (fv u) (fv v) (fvStack s) = arith₁ (rs Γ (fv u ++ fv v ++ fvStack s)) (tsize v) (ssize s) (tsize u)

Φ-app-arg : ∀ Γ s u v → Φ Γ [] v < Φ Γ s (app u v)
Φ-app-arg Γ s u v = lt-of (rs Γ ((fv u ++ fv v) ++ fvStack s) + ssize s) (tsize u + tsize v)
  (+-mono-≤ (≤-trans (≤-reflexive (+-identityʳ (rs Γ (fv v ++ []))))
                     (≤-trans (rs-mono Γ inc) (m≤m+n (rs Γ ((fv u ++ fv v) ++ fvStack s)) (ssize s))))
            (m≤n+m (tsize v) (tsize u)))
  where
    inc : (fv v ++ []) ⊑ ((fv u ++ fv v) ++ fvStack s)
    inc h = ∈-++⁺ˡ (∈-++⁺ʳ (fv u) (⊑-++[] (fv v) h))
```

Abstractions: the annotation, and the body under the binder at a fresh name.

```agda
Φ-ann : ∀ Γ s t u → Φ Γ [] t < Φ Γ s (lam t u)
Φ-ann Γ s t u = lt-of (rs Γ ((fv t ++ fv u) ++ fvStack s) + ssize s) (tsize t + tsize u)
  (+-mono-≤ (≤-trans (≤-reflexive (+-identityʳ (rs Γ (fv t ++ []))))
                     (≤-trans (rs-mono Γ inc) (m≤m+n (rs Γ ((fv t ++ fv u) ++ fvStack s)) (ssize s))))
            (m≤m+n (tsize t) (tsize u)))
  where
    inc : (fv t ++ []) ⊑ ((fv t ++ fv u) ++ fvStack s)
    inc h = ∈-++⁺ˡ (∈-++⁺ˡ (⊑-++[] (fv t) h))

Φ-fun-body : ∀ Γ x t u → x ∉ dom Γ → Φ ((x , sub , t) ∷ Γ) [] (u ^ fvar x) < Φ Γ [] (lam t u)
Φ-fun-body Γ x t u x∉ = lt-of (R + 0) (tsize t + tsize u) bound
  where
    N₀ = fv (u ^ fvar x) ++ []
    R  = rs Γ ((fv t ++ fv u) ++ [])
    inc : (fv t ++ N₀) ⊑ (x ∷ ((fv t ++ fv u) ++ []))
    inc h with ∈-++⁻ (fv t) h
    ... | inj₁ p = there (∈-++⁺ˡ (∈-++⁺ˡ p))
    ... | inj₂ q with ∈-++⁻ (fv (u ^ fvar x)) q
    ...   | inj₂ ()
    ...   | inj₁ r with fv-open-split 0 (fvar x) u r
    ...     | inj₁ a           = there (∈-++⁺ˡ (∈-++⁺ʳ (fv t) a))
    ...     | inj₂ (here refl) = here refl
    step₁ : rs ((x , sub , t) ∷ Γ) N₀ ≤ tsize t + R
    step₁ = ≤-trans (rs-cons Γ {x} {sub} {t} {N₀})
                    (+-monoʳ-≤ (tsize t) (rs-mono-fresh Γ {x} {(fv t ++ fv u) ++ []} {fv t ++ N₀} x∉ inc))
    step₂ : rs ((x , sub , t) ∷ Γ) N₀ + 0 + tsize (u ^ fvar x) ≤ tsize t + R + 0 + tsize u
    step₂ = +-mono-≤ (+-monoˡ-≤ 0 step₁) (≤-reflexive (tsize-open 0 x u))
    bound : rs ((x , sub , t) ∷ Γ) N₀ + 0 + tsize (u ^ fvar x) ≤ R + 0 + (tsize t + tsize u)
    bound = ≤-trans step₂ (≤-reflexive (arith₂ (tsize t) R 0 (tsize u)))

Φ-fop-body : ∀ Γ s α x t u → x ∉ dom Γ
           → Φ ((x , eqv , α) ∷ Γ) s (u ^ fvar x) < Φ Γ (α ∷ s) (lam t u)
Φ-fop-body Γ s α x t u x∉ = lt-of (R + (tsize α + ssize s)) (tsize t + tsize u) bound
  where
    N₀ = fv (u ^ fvar x) ++ fvStack s
    R  = rs Γ ((fv t ++ fv u) ++ (fv α ++ fvStack s))
    inc : (fv α ++ N₀) ⊑ (x ∷ ((fv t ++ fv u) ++ (fv α ++ fvStack s)))
    inc h with ∈-++⁻ (fv α) h
    ... | inj₁ p = there (∈-++⁺ʳ (fv t ++ fv u) (∈-++⁺ˡ p))
    ... | inj₂ q with ∈-++⁻ (fv (u ^ fvar x)) q
    ...   | inj₂ r = there (∈-++⁺ʳ (fv t ++ fv u) (∈-++⁺ʳ (fv α) r))
    ...   | inj₁ r with fv-open-split 0 (fvar x) u r
    ...     | inj₁ a           = there (∈-++⁺ˡ (∈-++⁺ʳ (fv t) a))
    ...     | inj₂ (here refl) = here refl
    step₁ : rs ((x , eqv , α) ∷ Γ) N₀ ≤ tsize α + R
    step₁ = ≤-trans (rs-cons Γ {x} {eqv} {α} {N₀})
                    (+-monoʳ-≤ (tsize α) (rs-mono-fresh Γ {x} {(fv t ++ fv u) ++ (fv α ++ fvStack s)} {fv α ++ N₀} x∉ inc))
    step₂ : rs ((x , eqv , α) ∷ Γ) N₀ + ssize s + tsize (u ^ fvar x) ≤ tsize α + R + ssize s + tsize u
    step₂ = +-mono-≤ (+-monoˡ-≤ (ssize s) step₁) (≤-reflexive (tsize-open 0 x u))
    bound : rs ((x , eqv , α) ∷ Γ) N₀ + ssize s + tsize (u ^ fvar x) ≤ R + (tsize α + ssize s) + (tsize t + tsize u)
    bound = ≤-trans step₂
            (≤-trans (≤-reflexive (arith₃ (tsize α) R (ssize s) (tsize u)))
                     (+-monoʳ-≤ (R + (tsize α + ssize s)) (m≤n+m (tsize u) (tsize t))))
```

β: the operand at the empty stack, the body at the same context with the parameter unbound, or
under `x ≡ v`.

```agda
Φ-bet-arg : ∀ Γ s t u v → Φ Γ [] v < Φ Γ s (app (lam t u) v)
Φ-bet-arg Γ s t u v = lt-of (rs Γ (((fv t ++ fv u) ++ fv v) ++ fvStack s) + ssize s) (tsize (lam t u) + tsize v)
  (+-mono-≤ (≤-trans (≤-reflexive (+-identityʳ (rs Γ (fv v ++ []))))
                     (≤-trans (rs-mono Γ inc) (m≤m+n (rs Γ (((fv t ++ fv u) ++ fv v) ++ fvStack s)) (ssize s))))
            (m≤n+m (tsize v) (tsize (lam t u))))
  where
    inc : (fv v ++ []) ⊑ (((fv t ++ fv u) ++ fv v) ++ fvStack s)
    inc h = ∈-++⁺ˡ (∈-++⁺ʳ (fv t ++ fv u) (⊑-++[] (fv v) h))

Φ-bet-body : ∀ Γ s x t u v → x ∉ dom Γ → Φ Γ s (u ^ fvar x) < Φ Γ s (app (lam t u) v)
Φ-bet-body Γ s x t u v x∉ = lt-of (rs Γ (((fv t ++ fv u) ++ fv v) ++ fvStack s) + ssize s) (tsize (lam t u) + tsize v)
  (+-mono-≤ (+-monoˡ-≤ (ssize s) (rs-mono-fresh Γ x∉ inc))
            (≤-trans (≤-reflexive (tsize-open 0 x u))
                     (≤-trans (m≤n+m (tsize u) (suc (tsize t))) (m≤m+n _ (tsize v)))))
  where
    inc : (fv (u ^ fvar x) ++ fvStack s) ⊑ (x ∷ (((fv t ++ fv u) ++ fv v) ++ fvStack s))
    inc h with ∈-++⁻ (fv (u ^ fvar x)) h
    ... | inj₂ r = there (∈-++⁺ʳ ((fv t ++ fv u) ++ fv v) r)
    ... | inj₁ r with fv-open-split 0 (fvar x) u r
    ...   | inj₁ a           = there (∈-++⁺ˡ (∈-++⁺ˡ (∈-++⁺ʳ (fv t) a)))
    ...   | inj₂ (here refl) = here refl

Φ-app-bet-body : ∀ Γ s x t u v → x ∉ dom Γ
               → Φ ((x , eqv , v) ∷ Γ) s (u ^ fvar x) < Φ Γ s (app (lam t u) v)
Φ-app-bet-body Γ s x t u v x∉ = lt-of (R + ssize s) (tsize (lam t u) + tsize v) bound
  where
    N₀ = fv (u ^ fvar x) ++ fvStack s
    R  = rs Γ (((fv t ++ fv u) ++ fv v) ++ fvStack s)
    inc : (fv v ++ N₀) ⊑ (x ∷ (((fv t ++ fv u) ++ fv v) ++ fvStack s))
    inc h with ∈-++⁻ (fv v) h
    ... | inj₁ p = there (∈-++⁺ˡ (∈-++⁺ʳ (fv t ++ fv u) p))
    ... | inj₂ q with ∈-++⁻ (fv (u ^ fvar x)) q
    ...   | inj₂ r = there (∈-++⁺ʳ ((fv t ++ fv u) ++ fv v) r)
    ...   | inj₁ r with fv-open-split 0 (fvar x) u r
    ...     | inj₁ a           = there (∈-++⁺ˡ (∈-++⁺ˡ (∈-++⁺ʳ (fv t) a)))
    ...     | inj₂ (here refl) = here refl
    step₁ : rs ((x , eqv , v) ∷ Γ) N₀ ≤ tsize v + R
    step₁ = ≤-trans (rs-cons Γ {x} {eqv} {v} {N₀})
                    (+-monoʳ-≤ (tsize v) (rs-mono-fresh Γ {x} {((fv t ++ fv u) ++ fv v) ++ fvStack s} {fv v ++ N₀} x∉ inc))
    step₂ : rs ((x , eqv , v) ∷ Γ) N₀ + ssize s + tsize (u ^ fvar x) ≤ tsize v + R + ssize s + tsize u
    step₂ = +-mono-≤ (+-monoˡ-≤ (ssize s) step₁) (≤-reflexive (tsize-open 0 x u))
    last : tsize v + tsize u ≤ tsize (lam t u) + tsize v
    last = ≤-trans (≤-reflexive (+-comm (tsize v) (tsize u)))
                   (+-monoˡ-≤ (tsize v) (≤-trans (m≤n+m (tsize u) (tsize t)) (n≤1+n (tsize t + tsize u))))
    bound : rs ((x , eqv , v) ∷ Γ) N₀ + ssize s + tsize (u ^ fvar x) ≤ R + ssize s + (tsize (lam t u) + tsize v)
    bound = ≤-trans step₂
            (≤-trans (≤-reflexive (arith₂ (tsize v) R (ssize s) (tsize u)))
                     (+-monoʳ-≤ (R + ssize s) last))
```

## What this establishes

`Φ`, and one strict inequality for each recursive call the variant's diamond makes.
