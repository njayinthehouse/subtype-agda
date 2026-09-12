# MPSS: the measure for the mixed diamond

The mixed diamond (`MPSS/MixedDiamond`) joins an *original* step against a *variant* step. Its
recursion is measured on the original side alone:

> `Ψ = size d + (sizes of the stack pieces of c₂) + (sizes of the annotation pieces of c₂ for
> the variables reachable from the subject and the stack)`

where `c₂` is the original side's context reduction. A variant promotion lands its recursive
call at the empty stack, which discards the stack pieces and every piece not reachable from the
annotation, and the piece for the promoted variable is what the call's `d` becomes. An original
promotion consumes a node of `d`. Every structural step consumes a node of `d` and at most moves a
premise of it into `c₂`.

The reachable sum is `MPSS/VariantMeasure`'s `rs` with a weight function in place of `tsize`.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.MixedMeasure where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties
  using (_≟_; ≤-refl; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; n≤1+n; m≤m+n; m≤n+m;
         +-assoc; +-comm; +-identityʳ; +-suc; ≤-reflexive)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-eqv; ↣-empty)
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.StackPush using (⟶ᵉ-refl; fv-open-cons)
open import MPSS.VariantMeasure using (tsize; ssize; tsize-open)
open import MPSS.Sized
open import MPSS.Uniform using (SizedCtx)
```

## Weighted reachable sums

```agda
wsum : Ctx → (Name → ℕ) → List Name → ℕ
wsum []                f N = 0
wsum ((y , _ , w) ∷ Γ) f N with y ∈? N
... | yes _ = f y + wsum Γ f (fv w ++ N)
... | no  _ = wsum Γ f N

wsum-mono : ∀ Γ f {N N′} → N ⊑ N′ → wsum Γ f N ≤ wsum Γ f N′
wsum-mono [] f inc = z≤n
wsum-mono ((y , a , w) ∷ Γ) f {N} {N′} inc with y ∈? N | y ∈? N′
... | yes _ | yes _  = +-monoʳ-≤ (f y) (wsum-mono Γ f (λ h → go h))
  where
    go : ∀ {z} → z ∈ (fv w ++ N) → z ∈ (fv w ++ N′)
    go h with ∈-++⁻ (fv w) h
    ... | inj₁ p = ∈-++⁺ˡ p
    ... | inj₂ p = ∈-++⁺ʳ (fv w) (inc p)
... | yes p | no  q  = ⊥-elim (q (inc p))
... | no  _ | yes _  =
  ≤-trans (wsum-mono Γ f inc) (≤-trans (wsum-mono Γ f (∈-++⁺ʳ (fv w))) (m≤n+m _ (f y)))
... | no  _ | no  _  = wsum-mono Γ f inc

wsum-cons : ∀ Γ f {y a w N} → wsum ((y , a , w) ∷ Γ) f N ≤ f y + wsum Γ f (fv w ++ N)
wsum-cons Γ f {y} {a} {w} {N} with y ∈? N
... | yes _ = ≤-refl
... | no  _ = ≤-trans (wsum-mono Γ f (∈-++⁺ʳ (fv w))) (m≤n+m _ (f y))

wsum-ext : ∀ Γ f {x N} → x ∉ dom Γ → ∀ M → wsum Γ f (M ++ x ∷ N) ≡ wsum Γ f (M ++ N)
wsum-ext [] f x∉ M = refl
wsum-ext ((y , a , w) ∷ Γ) f {x} {N} x∉ M with y ∈? (M ++ x ∷ N) | y ∈? (M ++ N)
... | yes p | yes _ =
  cong (f y +_)
       (trans (cong (wsum Γ f) (sym (++-assoc (fv w) M (x ∷ N))))
              (trans (wsum-ext Γ f (λ h → x∉ (there h)) (fv w ++ M))
                     (cong (wsum Γ f) (++-assoc (fv w) M N))))
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
... | no  _ | no  _ = wsum-ext Γ f (λ h → x∉ (there h)) M

wsum-fresh : ∀ Γ f {x N} → x ∉ dom Γ → wsum Γ f (x ∷ N) ≡ wsum Γ f N
wsum-fresh Γ f x∉ = wsum-ext Γ f x∉ []
```

The weight function matters only on the domain.

```agda
wsum-cong : ∀ Γ {f g} → (∀ {y} → y ∈ dom Γ → f y ≡ g y) → ∀ N → wsum Γ f N ≡ wsum Γ g N
wsum-cong [] eq N = refl
wsum-cong ((y , a , w) ∷ Γ) {f} {g} eq N with y ∈? N
... | yes _ = trans (cong (_+ wsum Γ f (fv w ++ N)) (eq (here refl)))
                    (cong (g y +_) (wsum-cong Γ (λ h → eq (there h)) (fv w ++ N)))
... | no  _ = wsum-cong Γ (λ h → eq (there h)) N
```

Pulling a definition: its weight is counted, and what its annotation reaches was counted below.

```agda
head-∉ : ∀ {Γ z c t} → ((z , c , t) ∷ Γ) prevalid → z ∉ dom Γ
head-∉ (Pv-Ctx _ z∉ _ _) = z∉
head-∉ (Pv-EqA _ z∉ _ _) = z∉

wsum-pull : ∀ Γ f {x a α N} → Γ prevalid → (x , a , α) ∈ Γ → x ∈ N
          → wsum Γ f (fv α) + f x ≤ wsum Γ f N
wsum-pull ((y , b , w) ∷ Γ) f {x} {a} {α} {N} pv (here refl) x∈ with x ∈? N | x ∈? fv α
... | no  q | _     = ⊥-elim (q x∈)
... | yes _ | yes p = ⊥-elim (head-∉ pv (head-fv pv p))
... | yes _ | no  _ =
  subst (λ n → wsum Γ f (fv α) + f x ≤ n) (+-comm (wsum Γ f (fv α ++ N)) (f x))
        (+-monoˡ-≤ (f x) (wsum-mono Γ f (∈-++⁺ˡ)))
wsum-pull ((y , b , w) ∷ Γ) f {x} {a} {α} {N} pv (there m) x∈ with y ∈? N | y ∈? fv α
... | _     | yes p = ⊥-elim (y∉α p)
  where
    y∉α : y ∉ fv α
    y∉α h = head-∉ pv (prevalid-bound-fv (tail-prevalid pv) m h)
... | yes _ | no  _ =
  ≤-trans (wsum-pull Γ f (tail-prevalid pv) m x∈)
          (≤-trans (wsum-mono Γ f (∈-++⁺ʳ (fv w))) (m≤n+m _ (f y)))
... | no  _ | no  _ = wsum-pull Γ f (tail-prevalid pv) m x∈
```

Unfolding a definition inside the set: adding what the annotation reaches to a set containing
the variable changes nothing.

```agda
wsum-unfold : ∀ Γ f {x a α N} → Γ prevalid → (x , a , α) ∈ Γ → x ∈ N
            → wsum Γ f (fv α ++ N) ≤ wsum Γ f N
wsum-unfold ((y , b , w) ∷ Γ) f {x} {a} {α} {N} pv (here refl) x∈ with x ∈? (fv α ++ N) | x ∈? N
... | _     | no  q = ⊥-elim (q x∈)
... | no  q | yes _ = ⊥-elim (q (∈-++⁺ʳ (fv α) x∈))
... | yes _ | yes _ = +-monoʳ-≤ (f x) (wsum-mono Γ f go)
  where
    go : ∀ {z} → z ∈ (fv α ++ fv α ++ N) → z ∈ (fv α ++ N)
    go h with ∈-++⁻ (fv α) h
    ... | inj₁ p = ∈-++⁺ˡ p
    ... | inj₂ p = p
wsum-unfold ((y , b , w) ∷ Γ) f {x} {a} {α} {N} pv (there m) x∈ with y ∈? (fv α ++ N) | y ∈? N
... | yes p | no  q = ⊥-elim (q (drop p))
  where
    y∉α : y ∉ fv α
    y∉α h = head-∉ pv (prevalid-bound-fv (tail-prevalid pv) m h)
    drop : y ∈ (fv α ++ N) → y ∈ N
    drop h with ∈-++⁻ (fv α) h
    ... | inj₁ p = ⊥-elim (y∉α p)
    ... | inj₂ p = p
... | no  q | yes p = ⊥-elim (q (∈-++⁺ʳ (fv α) p))
... | yes _ | yes _ =
  +-monoʳ-≤ (f y) (≤-trans (wsum-mono Γ f swap) (wsum-unfold Γ f (tail-prevalid pv) m (∈-++⁺ʳ (fv w) x∈)))
  where
    swap : ∀ {z} → z ∈ (fv w ++ fv α ++ N) → z ∈ (fv α ++ fv w ++ N)
    swap h with ∈-++⁻ (fv w) h
    ... | inj₁ p = ∈-++⁺ʳ (fv α) (∈-++⁺ˡ p)
    ... | inj₂ p with ∈-++⁻ (fv α) p
    ...   | inj₁ q = ∈-++⁺ˡ q
    ...   | inj₂ q = ∈-++⁺ʳ (fv α) (∈-++⁺ʳ (fv w) q)
... | no  _ | no  _ = wsum-unfold Γ f (tail-prevalid pv) m x∈
```

## Weights read off a sized context reduction

The weight of a name is the size of its annotation piece: the size recorded in the `Ct-Ann`
layer, or the size of the reflexivity derivation of its annotation in the `Ct-Refl` suffix.

```agda
tsizeOf : Ctx → Name → ℕ
tsizeOf []                x = 0
tsizeOf ((y , _ , w) ∷ Γ) x with x ≟ y
... | yes _ = tsize w
... | no  _ = tsizeOf Γ x

tsizeOf-∈ : ∀ {Γ x a α} → Γ prevalid → (x , a , α) ∈ Γ → tsizeOf Γ x ≡ tsize α
tsizeOf-∈ {(x , a , α) ∷ Γ} {x} pv (here refl) with x ≟ x
... | yes _ = refl
... | no  q = ⊥-elim (q refl)
tsizeOf-∈ {(y , b , w) ∷ Γ} {x} pv (there m) with x ≟ y
... | yes refl = ⊥-elim (head-∉ pv (∈-dom m))
... | no  _    = tsizeOf-∈ (tail-prevalid pv) m

pieceW : ∀ {Γ s Γ' s'} (c : Γ ∣ s ↣ Γ' ∣ s') → SizedCtx c → Name → ℕ
pieceW (Ct-Refl {Γ})            _            y = tsizeOf Γ y
pieceW (Ct-Ann {x = x} c e)     (sc , n , _) y with y ≟ x
... | yes _ = n
... | no  _ = pieceW c sc y
pieceW (Ct-Stk c e)             (sc , _)     y = pieceW c sc y

stkSum : ∀ {Γ s Γ' s'} (c : Γ ∣ s ↣ Γ' ∣ s') → SizedCtx c → ℕ
stkSum (Ct-Refl {s = s}) _            = ssize s
stkSum (Ct-Ann c e)      (sc , _)     = stkSum c sc
stkSum (Ct-Stk c e)      (sc , n , _) = n + stkSum c sc
```

The piece `↣-eqv` returns has the weight of its variable.

```agda
Sized-eqv : ∀ {Γ s Γ' s' x α} (pv : Γ prevalid) (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
            (m : x ≐ α ∈ Γ)
          → Sized (proj₂ (proj₂ (↣-eqv pv c m))) (pieceW c sc x)
Sized-eqv {α = α} pv Ct-Refl sc m
  rewrite tsizeOf-∈ pv m = Sized-refl (Pv-Nil pv) (prevalid-bound-lc pv m) (prevalid-bound-fv pv m)
Sized-eqv pv (Ct-Stk c e) (sc , _) m = Sized-eqv pv c sc m
Sized-eqv {x = x} pv (Ct-Ann {x = y} {c = k} {t = t₀} c e) (sc , n , se) (here refl) with x ≟ x
... | yes _ = Sized-weaken [] ((x , k , t₀) ∷ []) (Pv-Nil pv) e se
... | no  q = ⊥-elim (q refl)
Sized-eqv {x = x} pv (Ct-Ann {x = y} {c = k} {t = t₀} c e) (sc , n , se) (there m)
  with ↣-eqv (tail-prevalid pv) c m | Sized-eqv (tail-prevalid pv) c sc m | x ≟ y
... | α' , m' , e' | se' | yes refl = ⊥-elim (head-∉ pv (∈-dom m))
... | α' , m' , e' | se' | no  _    = Sized-weaken [] ((y , k , t₀) ∷ []) (Pv-Nil pv) e' se'
```

Emptying the stack keeps the weights and drops the stack pieces.

```agda
sizedEmpty : ∀ {Γ s Γ' s'} (c : Γ ∣ s ↣ Γ' ∣ s') → SizedCtx c → SizedCtx (↣-empty c)
sizedEmpty Ct-Refl      sc           = tt
sizedEmpty (Ct-Ann c e) (sc , n , se) = sizedEmpty c sc , n , se
sizedEmpty (Ct-Stk c e) (sc , _)      = sizedEmpty c sc

pieceW-empty : ∀ {Γ s Γ' s'} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c) y
             → pieceW (↣-empty c) (sizedEmpty c sc) y ≡ pieceW c sc y
pieceW-empty Ct-Refl sc y = refl
pieceW-empty (Ct-Ann {x = x} c e) (sc , n , se) y with y ≟ x
... | yes _ = refl
... | no  _ = pieceW-empty c sc y
pieceW-empty (Ct-Stk c e) (sc , _) y = pieceW-empty c sc y

stkSum-empty : ∀ {Γ s Γ' s'} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
             → stkSum (↣-empty c) (sizedEmpty c sc) ≡ 0
stkSum-empty Ct-Refl      sc       = refl
stkSum-empty (Ct-Ann c e) (sc , _) = stkSum-empty c sc
stkSum-empty (Ct-Stk c e) (sc , _) = stkSum-empty c sc
```

## The measure

```agda
Ψ : ∀ {Γ s Γ' s'} (c : Γ ∣ s ↣ Γ' ∣ s') → SizedCtx c → ℕ → Tm → ℕ
Ψ {Γ} {s} c sc n t = n + stkSum c sc + wsum Γ (pieceW c sc) (fv t ++ fvStack s)
```

Two arithmetic facts used repeatedly.

```agda
≤-suc-l : ∀ {a b} → a ≤ b → a < suc b
≤-suc-l h = s≤s h

shuffle : ∀ a b c d → a + b + (c + d) ≡ (a + c) + (b + d)
shuffle a b c d =
  trans (+-assoc a b (c + d))
        (trans (cong (a +_) (trans (sym (+-assoc b c d))
                                   (trans (cong (_+ d) (+-comm b c)) (+-assoc c b d))))
               (sym (+-assoc a c (b + d))))
```

## The inequalities the cases need

An original promotion, against a variant variable or a variant promotion: the subject grows
from the variable to its annotation, at the same stack; `d` loses its root.

```agda
Ψ-pro : ∀ {Γ s Γ' s' x a α n} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
      → Γ prevalid → (x , a , α) ∈ Γ
      → Ψ c sc n α < Ψ c sc (suc n) (fvar x)
Ψ-pro {Γ} {s} {x = x} {α = α} {n = n} c sc pv m = s≤s (+-monoʳ-≤ (n + stkSum c sc) reach)
  where
    f = pieceW c sc
    reach : wsum Γ f (fv α ++ fvStack s) ≤ wsum Γ f (x ∷ fvStack s)
    reach = ≤-trans (wsum-mono Γ f (λ h → step h)) (wsum-unfold Γ f pv m (here refl))
      where
        step : ∀ {z} → z ∈ (fv α ++ fvStack s) → z ∈ (fv α ++ x ∷ fvStack s)
        step h with ∈-++⁻ (fv α) h
        ... | inj₁ p = ∈-++⁺ˡ p
        ... | inj₂ p = ∈-++⁺ʳ (fv α) (there p)
```

A variant promotion against an original variable: the call is at the empty stack, on the
annotation, with the annotation's piece as its `d`.

```agda
Ψ-pull : ∀ {Γ s Γ' s' x α} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
       → Γ prevalid → x ≐ α ∈ Γ
       → Ψ (↣-empty c) (sizedEmpty c sc) (pieceW c sc x) α < Ψ c sc 1 (fvar x)
Ψ-pull {Γ} {s} {x = x} {α = α} c sc pv m
  rewrite stkSum-empty c sc | +-identityʳ (pieceW c sc x)
        | wsum-cong Γ {pieceW (↣-empty c) (sizedEmpty c sc)} {pieceW c sc}
                    (λ {y} _ → pieceW-empty c sc y) (fv α ++ [])
  = s≤s (≤-trans (+-monoʳ-≤ (f x) (wsum-mono Γ f (⊑-++[] (fv α))))
                 (≤-trans (subst (_≤ wsum Γ f (x ∷ fvStack s)) (+-comm (wsum Γ f (fv α)) (f x))
                                 (wsum-pull Γ f pv m (here refl)))
                          (m≤n+m _ (stkSum c sc))))
  where
    f = pieceW c sc
    ⊑-++[] : ∀ (M : List Name) → (M ++ []) ⊑ M
    ⊑-++[] M h rewrite ++-identityʳ M = h
```

## Popping the stack head

`MPSS/DiamondStep`'s `↣-pop` and `pop-piece`, with the sizes carried along: the popped piece's
size leaves the stack sum and becomes the new head weight.

```agda
open import MPSS.DiamondStep using (Popped; same; piece; ↣-pop; pop-piece)

PoppedSized : ∀ {Γ α α'} → ℕ → Popped Γ α α' → Set
PoppedSized {α = α} n same              = n ≡ tsize α
PoppedSized         n (piece Δ Γₜ _ e)  = Sized e n

popCtx : ∀ {Γ s Γ' s' α} (c : Γ ∣ (α ∷ s) ↣ Γ' ∣ s') → Γ ∣ s ↣ Γ' ∣ proj₁ (proj₂ (↣-pop c))
popCtx c = proj₁ (proj₂ (proj₂ (proj₂ (↣-pop c))))

popPc : ∀ {Γ s Γ' s' α} (c : Γ ∣ (α ∷ s) ↣ Γ' ∣ s') → Popped Γ α (proj₁ (↣-pop c))
popPc c = proj₂ (proj₂ (proj₂ (proj₂ (↣-pop c))))

sizedPop : ∀ {Γ s Γ' s' α} (c : Γ ∣ (α ∷ s) ↣ Γ' ∣ s') (sc : SizedCtx c)
         → SizedCtx (popCtx c) × ∃[ n ] PoppedSized n (popPc c)
sizedPop Ct-Refl      sc              = tt , _ , refl
sizedPop (Ct-Stk c e) (sc , n , se)   = sc , n , se
sizedPop (Ct-Ann {x = y} {c = k} {t = t₀} c e) (sc , n , se) with ↣-pop c | sizedPop c sc
... | α' , s'' , refl , c′ , same               | sc′ , m , eq  = (sc′ , n , se) , m , eq
... | α' , s'' , refl , c′ , piece Δ Γₜ refl e′ | sc′ , m , se′ = (sc′ , n , se) , m , se′

Sized-pop : ∀ {Γ α α' n} (pv : Γ ∣ [] prevalid) (lα : LC α) (f : fv α ⊑ dom Γ)
            (pp : Popped Γ α α') → PoppedSized n pp
          → Sized (pop-piece pv lα f pp) n
Sized-pop pv lα f same              refl = Sized-refl pv lα f
Sized-pop pv lα f (piece Δ Γₜ refl e) se = Sized-weaken [] Δ pv e se

stkSum-pop : ∀ {Γ s Γ' s' α} (c : Γ ∣ (α ∷ s) ↣ Γ' ∣ s') (sc : SizedCtx c)
           → stkSum c sc ≡ proj₁ (proj₂ (sizedPop c sc)) + stkSum (popCtx c) (proj₁ (sizedPop c sc))
stkSum-pop Ct-Refl      sc            = refl
stkSum-pop (Ct-Stk c e) (sc , n , se) = refl
stkSum-pop (Ct-Ann {x = y} {c = k} {t = t₀} c e) (sc , n , se)
  with ↣-pop c | sizedPop c sc | stkSum-pop c sc
... | α' , s'' , refl , c′ , same               | sc′ , m , eq  | ih = ih
... | α' , s'' , refl , c′ , piece Δ Γₜ refl e′ | sc′ , m , se′ | ih = ih

pieceW-ann-cong : ∀ {Γ s s₁ Γ' s' s₁' x k t t′ n}
                  (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c) (c₁ : Γ ∣ s₁ ↣ Γ' ∣ s₁') (sc₁ : SizedCtx c₁)
                  {e : Γ ∣ [] ⊢ t ⟶ᵉ t′} (se : Sized e n)
                → (∀ z → pieceW c sc z ≡ pieceW c₁ sc₁ z)
                → ∀ y → pieceW (Ct-Ann {x = x} {c = k} c e) (sc , n , se) y
                        ≡ pieceW (Ct-Ann {x = x} {c = k} c₁ e) (sc₁ , n , se) y
pieceW-ann-cong {x = x} c sc c₁ sc₁ se eq y with y ≟ x
... | yes _ = refl
... | no  _ = eq y

pieceW-pop : ∀ {Γ s Γ' s' α} (c : Γ ∣ (α ∷ s) ↣ Γ' ∣ s') (sc : SizedCtx c) y
           → pieceW (popCtx c) (proj₁ (sizedPop c sc)) y ≡ pieceW c sc y
pieceW-pop Ct-Refl      sc            y = refl
pieceW-pop (Ct-Stk c e) (sc , n , se) y = refl
pieceW-pop (Ct-Ann {x = x} {c = k} {t = t₀} c e) (sc , n , se) y
  with ↣-pop c | sizedPop c sc | pieceW-pop c sc
... | α' , s'' , refl , c′ , same               | sc′ , m , eq  | ih = pieceW-ann-cong {x = x} {k = k} c′ sc′ c sc {e} se ih y
... | α' , s'' , refl , c′ , piece Δ Γₜ refl e′ | sc′ , m , se′ | ih = pieceW-ann-cong {x = x} {k = k} c′ sc′ c sc {e} se ih y
```

## Weights at a new head

```agda
pieceW-head : ∀ {Γ s Γ' s' x k t t′ n} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
              {e : Γ ∣ [] ⊢ t ⟶ᵉ t′} (se : Sized e n)
            → pieceW (Ct-Ann {x = x} {c = k} c e) (sc , n , se) x ≡ n
pieceW-head {x = x} c sc se with x ≟ x
... | yes _ = refl
... | no  q = ⊥-elim (q refl)

pieceW-tail : ∀ {Γ s Γ' s' x k t t′ n} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
              {e : Γ ∣ [] ⊢ t ⟶ᵉ t′} (se : Sized e n) → x ∉ dom Γ
            → ∀ {y} → y ∈ dom Γ
            → pieceW (Ct-Ann {x = x} {c = k} c e) (sc , n , se) y ≡ pieceW c sc y
pieceW-tail {x = x} c sc se x∉ {y} y∈ with y ≟ x
... | yes refl = ⊥-elim (x∉ y∈)
... | no  _    = refl
```

The reachable sum at a context extended by a fresh binding, in terms of the old one.

```agda
wsum-head : ∀ {Γ s Γ' s' x k t t′ n} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
            {e : Γ ∣ [] ⊢ t ⟶ᵉ t′} (se : Sized e n) → x ∉ dom Γ → ∀ N
          → wsum ((x , k , t) ∷ Γ) (pieceW (Ct-Ann {x = x} {c = k} c e) (sc , n , se)) N
              ≤ n + wsum Γ (pieceW c sc) (fv t ++ N)
wsum-head {Γ} {x = x} {k = k} {t = t} {n = n} c sc {e} se x∉ N =
  ≤-trans (wsum-cons Γ f′ {x} {k} {t} {N})
          (≤-reflexive (trans (cong (_+ wsum Γ f′ (fv t ++ N)) (pieceW-head {x = x} {k = k} c sc se))
                              (cong (n +_) (wsum-cong Γ (λ h → pieceW-tail {x = x} {k = k} c sc se x∉ h) (fv t ++ N)))))
  where
    f′ = pieceW (Ct-Ann {x = x} {c = k} c e) (sc , n , se)
```

## The structural inequalities

Membership shuffles the inequalities need.

```agda
⊑-assocˡ : ∀ (A B C : List Name) → (A ++ B ++ C) ⊑ ((A ++ B) ++ C)
⊑-assocˡ A B C {z} h = subst (z ∈_) (sym (++-assoc A B C)) h

⊑-assocʳ : ∀ (A B C : List Name) → ((A ++ B) ++ C) ⊑ (A ++ B ++ C)
⊑-assocʳ A B C {z} h = subst (z ∈_) (++-assoc A B C) h

⊑-skip : ∀ (A B C : List Name) → (B ++ C) ⊑ (A ++ B ++ C)
⊑-skip A B C h = ∈-++⁺ʳ A h

⊑-drop-mid : ∀ (A B C : List Name) → (A ++ C) ⊑ (A ++ B ++ C)
⊑-drop-mid A B C h with ∈-++⁻ A h
... | inj₁ p = ∈-++⁺ˡ p
... | inj₂ p = ∈-++⁺ʳ A (∈-++⁺ʳ B p)

⊑-++[] : ∀ (M : List Name) → (M ++ []) ⊑ M
⊑-++[] M {z} h = subst (z ∈_) (++-identityʳ M) h

⊑-swap : ∀ (A B C : List Name) → (B ++ A ++ C) ⊑ (A ++ B ++ C)
⊑-swap A B C h with ∈-++⁻ B h
... | inj₁ p = ∈-++⁺ʳ A (∈-++⁺ˡ p)
... | inj₂ p with ∈-++⁻ A p
...   | inj₁ q = ∈-++⁺ˡ q
...   | inj₂ q = ∈-++⁺ʳ A (∈-++⁺ʳ B q)

⊑-open : ∀ {x b} (N : List Name) → (fv (b ^ fvar x) ++ N) ⊑ (x ∷ fv b ++ N)
⊑-open {x} {b} N h with ∈-++⁻ (fv (b ^ fvar x)) h
... | inj₁ p with fv-open-cons {b} x (λ q → q) p
...   | here refl = here refl
...   | there q   = there (∈-++⁺ˡ q)
⊑-open {x} {b} N h | inj₂ p = there (∈-++⁺ʳ (fv b) p)
```

The common shape: the new `d` is smaller by at least one node, the stack sum is what it was
plus whatever `d` gave up, and the reachable sum is bounded through inclusions.

```agda
Ψ-lt : ∀ {a b W′ W} → a ≤ b → W′ ≤ W → a + W′ < suc (b + W)
Ψ-lt h₁ h₂ = s≤s (+-mono-≤ h₁ h₂)
```

The operator of an application, at the pushed stack, with the operand stored.

```agda
Ψ-app-op : ∀ {Γ s Γ' s' u v v′ n₁ n₂} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
           {p : Γ ∣ [] ⊢ v ⟶ᵉ v′} (sp : Sized p n₂)
         → Ψ (Ct-Stk c p) (sc , n₂ , sp) n₁ u < Ψ c sc (suc (n₁ + n₂)) (app u v)
Ψ-app-op {Γ} {s} {u = u} {v = v} {n₁ = n₁} {n₂} c sc sp =
  Ψ-lt (≤-reflexive (sym (+-assoc n₁ n₂ (stkSum c sc))))
       (wsum-mono Γ (pieceW c sc) (⊑-assocˡ (fv u) (fv v) (fvStack s)))
```

An operand, or any subterm at the empty stack with a `d` no larger than the rest.

```agda
Ψ-arg : ∀ {Γ s Γ' s' u v n m} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
       → n ≤ m
       → Ψ (↣-empty c) (sizedEmpty c sc) n v < Ψ c sc (suc m) (app u v)
Ψ-arg {Γ} {s} {u = u} {v = v} {n} {m} c sc n≤m
  rewrite stkSum-empty c sc | +-identityʳ n
        | wsum-cong Γ {pieceW (↣-empty c) (sizedEmpty c sc)} {pieceW c sc}
                    (λ {y} _ → pieceW-empty c sc y) (fv v ++ [])
  = Ψ-lt (≤-trans n≤m (m≤m+n m (stkSum c sc)))
         (wsum-mono Γ (pieceW c sc) (λ h → ∈-++⁺ˡ (∈-++⁺ʳ (fv u) (⊑-++[] (fv v) h))))
```

An annotation, at the empty stack, whichever stack the abstraction sits under.

```agda
Ψ-ann : ∀ {Γ s Γ' s' t u n m} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
      → n ≤ m
      → Ψ (↣-empty c) (sizedEmpty c sc) n t < Ψ c sc (suc m) (lam t u)
Ψ-ann {Γ} {s} {t = t} {u = u} {n} {m} c sc n≤m
  rewrite stkSum-empty c sc | +-identityʳ n
        | wsum-cong Γ {pieceW (↣-empty c) (sizedEmpty c sc)} {pieceW c sc}
                    (λ {y} _ → pieceW-empty c sc y) (fv t ++ [])
  = Ψ-lt (≤-trans n≤m (m≤m+n m (stkSum c sc)))
         (wsum-mono Γ (pieceW c sc) (λ h → ∈-++⁺ˡ (∈-++⁺ˡ (⊑-++[] (fv t) h))))
```

A body under `Me-Fun`: the fresh name is bound to the annotation, whose piece is stored, and the
body is opened at it; the abstraction sits at the empty stack.

```agda
arith-fun : ∀ n₁ n₂ k → n₂ + k + n₁ ≡ n₁ + n₂ + k
arith-fun n₁ n₂ k = trans (+-comm (n₂ + k) n₁) (sym (+-assoc n₁ n₂ k))

Ψ-fun-body : ∀ {Γ Γ' x t t′ u n₁ n₂} (c : Γ ∣ [] ↣ Γ' ∣ []) (sc : SizedCtx c)
             {a : Γ ∣ [] ⊢ t ⟶ᵉ t′} (sa : Sized a n₁) → x ∉ dom Γ
           → Ψ (Ct-Ann {x = x} {c = sub} c a) (sc , n₁ , sa) n₂ (u ^ fvar x)
             < Ψ c sc (suc (n₁ + n₂)) (lam t u)
Ψ-fun-body {Γ} {x = x} {t = t} {u = u} {n₁ = n₁} {n₂} c sc {a} sa x∉ =
  s≤s (≤-trans (+-monoʳ-≤ (n₂ + k) (wsum-head {x = x} {k = sub} c sc sa x∉ (fv (u ^ fvar x) ++ [])))
               (≤-trans (≤-reflexive (sym (+-assoc (n₂ + k) n₁ _)))
                        (+-mono-≤ (≤-reflexive (arith-fun n₁ n₂ k)) reach)))
  where
    k = stkSum c sc
    f = pieceW c sc
    step : ∀ {z} → z ∈ (fv t ++ fv (u ^ fvar x) ++ []) → z ∈ (fv t ++ x ∷ fv u ++ [])
    step h with ∈-++⁻ (fv t) h
    ... | inj₁ p = ∈-++⁺ˡ p
    ... | inj₂ p = ∈-++⁺ʳ (fv t) (⊑-open {x} {u} [] p)
    reach : wsum Γ f (fv t ++ fv (u ^ fvar x) ++ []) ≤ wsum Γ f ((fv t ++ fv u) ++ [])
    reach = ≤-trans (wsum-mono Γ f (λ h → step h))
            (≤-trans (≤-reflexive (wsum-ext Γ f x∉ (fv t)))
                     (wsum-mono Γ f (⊑-assocˡ (fv t) (fv u) [])))
```

A body under `Me-FOp`: the stack head is popped, its piece becomes the fresh name's, and the
body is opened at it under the rest of the stack.

```agda
arith-fop : ∀ n₁ n₂ k m → n₂ + k + m ≤ n₁ + n₂ + (m + k)
arith-fop n₁ n₂ k m =
  ≤-trans (≤-reflexive (trans (+-assoc n₂ k m) (cong (n₂ +_) (+-comm k m))))
          (≤-trans (m≤n+m (n₂ + (m + k)) n₁) (≤-reflexive (sym (+-assoc n₁ n₂ (m + k)))))

Ψ-fop-body : ∀ {Γ s Γ' s' x α t u n₁ n₂} (c : Γ ∣ (α ∷ s) ↣ Γ' ∣ s') (sc : SizedCtx c)
             (pv : Γ ∣ [] prevalid) (lα : LC α) (fα : fv α ⊑ dom Γ) → x ∉ dom Γ
           → Ψ (Ct-Ann {x = x} {c = eqv} (popCtx c) (pop-piece pv lα fα (popPc c)))
               (proj₁ (sizedPop c sc) , proj₁ (proj₂ (sizedPop c sc))
                , Sized-pop pv lα fα (popPc c) (proj₂ (proj₂ (sizedPop c sc))))
               n₂ (u ^ fvar x)
             < Ψ c sc (suc (n₁ + n₂)) (lam t u)
Ψ-fop-body {Γ} {s} {x = x} {α = α} {t = t} {u = u} {n₁ = n₁} {n₂} c sc pv lα fα x∉
  rewrite stkSum-pop c sc =
  s≤s (≤-trans (+-monoʳ-≤ (n₂ + k) (≤-trans (wsum-head {x = x} {k = eqv} c′ sc′ sq x∉ (fv (u ^ fvar x) ++ fvStack s))
                                            (+-monoʳ-≤ m reach)))
               (≤-trans (≤-reflexive (sym (+-assoc (n₂ + k) m _)))
                        (+-mono-≤ (arith-fop n₁ n₂ k m) ≤-refl)))
  where
    c′  = popCtx c
    sc′ = proj₁ (sizedPop c sc)
    m   = proj₁ (proj₂ (sizedPop c sc))
    sq  = Sized-pop pv lα fα (popPc c) (proj₂ (proj₂ (sizedPop c sc)))
    k   = stkSum c′ sc′
    f   = pieceW c sc
    step : ∀ {z} → z ∈ (fv α ++ fv (u ^ fvar x) ++ fvStack s) → z ∈ (fv α ++ x ∷ fv u ++ fvStack s)
    step h with ∈-++⁻ (fv α) h
    ... | inj₁ p = ∈-++⁺ˡ p
    ... | inj₂ p = ∈-++⁺ʳ (fv α) (⊑-open {x} {u} (fvStack s) p)
    incl : ∀ {z} → z ∈ (fv α ++ fv u ++ fvStack s) → z ∈ ((fv t ++ fv u) ++ fv α ++ fvStack s)
    incl h with ∈-++⁻ (fv α) h
    ... | inj₁ p = ∈-++⁺ʳ (fv t ++ fv u) (∈-++⁺ˡ p)
    ... | inj₂ p with ∈-++⁻ (fv u) p
    ...   | inj₁ q = ∈-++⁺ˡ (∈-++⁺ʳ (fv t) q)
    ...   | inj₂ q = ∈-++⁺ʳ (fv t ++ fv u) (∈-++⁺ʳ (fv α) q)
    reach : wsum Γ (pieceW c′ sc′) (fv α ++ fv (u ^ fvar x) ++ fvStack s)
          ≤ wsum Γ f ((fv t ++ fv u) ++ fv α ++ fvStack s)
    reach = ≤-trans (≤-reflexive (wsum-cong Γ (λ {y} _ → pieceW-pop c sc y) _))
            (≤-trans (wsum-mono Γ f (λ h → step h))
            (≤-trans (≤-reflexive (wsum-ext Γ f x∉ (fv α)))
                     (wsum-mono Γ f (λ h → incl h))))
```

A body under `Me-Bet`, with the parameter unbound: same context reduction, the body opened at
a name the context does not bind.

```agda
Ψ-bet-body : ∀ {Γ s Γ' s' x t u v n m} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
           → x ∉ dom Γ → n ≤ m
           → Ψ c sc n (u ^ fvar x) < Ψ c sc (suc m) (app (lam t u) v)
Ψ-bet-body {Γ} {s} {x = x} {t = t} {u = u} {v = v} {n} {m} c sc x∉ n≤m =
  Ψ-lt (+-monoˡ-≤ (stkSum c sc) n≤m) reach
  where
    f = pieceW c sc
    incl : ∀ {z} → z ∈ (fv u ++ fvStack s) → z ∈ (((fv t ++ fv u) ++ fv v) ++ fvStack s)
    incl h with ∈-++⁻ (fv u) h
    ... | inj₁ p = ∈-++⁺ˡ (∈-++⁺ˡ (∈-++⁺ʳ (fv t) p))
    ... | inj₂ p = ∈-++⁺ʳ ((fv t ++ fv u) ++ fv v) p
    reach : wsum Γ f (fv (u ^ fvar x) ++ fvStack s) ≤ wsum Γ f (((fv t ++ fv u) ++ fv v) ++ fvStack s)
    reach = ≤-trans (wsum-mono Γ f (⊑-open {x} {u} (fvStack s)))
            (≤-trans (≤-reflexive (wsum-fresh Γ f x∉))
                     (wsum-mono Γ f (λ h → incl h)))
```

The body of the `Me-App`/`Me-Bet` case: the parameter is bound to the operand, whose piece is
stored, on both orientations of the case. The bound `n + n₂ ≤ m` covers a `Me-Bet` on the
original side (`m = n + n₂`) and a `Me-App` over `Me-FOp` (`m = suc (n₁ + n) + n₂`).

```agda
arith-ab : ∀ n k n₂ m → n + n₂ ≤ m → n + k + n₂ ≤ m + k
arith-ab n k n₂ m h =
  ≤-trans (≤-reflexive (trans (+-assoc n k n₂) (trans (cong (n +_) (+-comm k n₂)) (sym (+-assoc n n₂ k)))))
          (+-monoˡ-≤ k h)

Ψ-app-bet-body : ∀ {Γ s Γ' s' x t u v v′ n n₂ m} (c : Γ ∣ s ↣ Γ' ∣ s') (sc : SizedCtx c)
                 {p : Γ ∣ [] ⊢ v ⟶ᵉ v′} (sp : Sized p n₂) → x ∉ dom Γ → n + n₂ ≤ m
               → Ψ (Ct-Ann {x = x} {c = eqv} c p) (sc , n₂ , sp) n (u ^ fvar x)
                 < Ψ c sc (suc m) (app (lam t u) v)
Ψ-app-bet-body {Γ} {s} {x = x} {t = t} {u = u} {v = v} {n = n} {n₂} {m} c sc {p} sp x∉ h =
  s≤s (≤-trans (+-monoʳ-≤ (n + k) (wsum-head {x = x} {k = eqv} c sc sp x∉ (fv (u ^ fvar x) ++ fvStack s)))
               (≤-trans (≤-reflexive (sym (+-assoc (n + k) n₂ _)))
                        (+-mono-≤ (arith-ab n k n₂ m h) reach)))
  where
    k = stkSum c sc
    f = pieceW c sc
    step : ∀ {z} → z ∈ (fv v ++ fv (u ^ fvar x) ++ fvStack s) → z ∈ (fv v ++ x ∷ fv u ++ fvStack s)
    step h with ∈-++⁻ (fv v) h
    ... | inj₁ q = ∈-++⁺ˡ q
    ... | inj₂ q = ∈-++⁺ʳ (fv v) (⊑-open {x} {u} (fvStack s) q)
    incl : ∀ {z} → z ∈ (fv v ++ fv u ++ fvStack s) → z ∈ (((fv t ++ fv u) ++ fv v) ++ fvStack s)
    incl h with ∈-++⁻ (fv v) h
    ... | inj₁ q = ∈-++⁺ˡ (∈-++⁺ʳ (fv t ++ fv u) q)
    ... | inj₂ q with ∈-++⁻ (fv u) q
    ...   | inj₁ r = ∈-++⁺ˡ (∈-++⁺ˡ (∈-++⁺ʳ (fv t) r))
    ...   | inj₂ r = ∈-++⁺ʳ ((fv t ++ fv u) ++ fv v) r
    reach : wsum Γ f (fv v ++ fv (u ^ fvar x) ++ fvStack s) ≤ wsum Γ f (((fv t ++ fv u) ++ fv v) ++ fvStack s)
    reach = ≤-trans (wsum-mono Γ f (λ h′ → step h′))
            (≤-trans (≤-reflexive (wsum-ext Γ f x∉ (fv v)))
                     (wsum-mono Γ f (λ h′ → incl h′)))
```

## What this establishes

`Ψ`, and one strict inequality per recursive call of the mixed diamond's case analysis:
`Ψ-pro` (an original promotion, against a variant variable or promotion), `Ψ-pull` (a variant
promotion against an original variable — the call at the empty stack on the annotation, with
its piece as the new `d`), `Ψ-app-op`, `Ψ-arg`, `Ψ-ann`, `Ψ-fun-body`, `Ψ-fop-body`,
`Ψ-bet-body`, `Ψ-app-bet-body`. Every call of `MPSS/MixedDiamond`'s cases is one of these.
