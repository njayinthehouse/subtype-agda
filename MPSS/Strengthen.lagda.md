# MPSS: strengthening a reduction, and what the `Me-App`/`Me-Bet` case really needs

The `Me-App`/`Me-Bet` case of Lemma 2's printed proof obtains the body's join under `x ≡ v₁`
and then says: since the derivation never promotes `x`, "as a result we have
`Γ₁;s₁ ⊢ u₁ ⟶≡ u₃`". That is a strengthening step — drop the binding for `x` — justified by
the absence of `Me-Pro` on `x`. `MPSS/Moreover` shows the absence itself cannot be guaranteed
in the form printed. This module shows that even granted, it is **not enough**: a derivation
that never promotes `x` can still be underivable once `x` is unbound, because it pushes `x`
onto the stack, and a stack entry has to be scoped in the context.

> `(x ≡ ⊤) ; nil ⊢ (λ⊤.0) x ⟶≡ (λ⊤.0) x` by `Me-App` (pushing `x`) and `Me-FOp`, promoting
> nothing; and `ε ; nil ⊢ (λ⊤.0) x ⟶≡ (λ⊤.0) x` has no derivation at all.

What strengthening actually needs is that `x` occur in no stack, in no binder annotation, and
in no promotion anywhere in the derivation. `Avoids x d` says exactly that, and
`⟶ᵉ-strengthen` is the lemma. Two facts make it usable in the diamond: a derivation at a
context that does not bind `x` avoids `x` automatically (`unbound-avoids`), and so do all the
pieces of a context reduction at such a context (`unbound-avoidsC`). So the invariant a proof of
the diamond has to carry is: *if one edge and the context reduction on its side avoid `x`, the
join on the other side avoids `x`* — `Avoids` in place of the printed "no promotion", and the
context reduction included, which the printed clause omits.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Strengthen where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Moreover using (Promotes; pro-here)
open import MPSS.ReflFails using (no-push)
open import MPSS.Rename using (fvCtx)
open import MPSS.StackPush using (dom-++; prevalid-cons)
open import MPSS.Weakening using (dom-⊑)
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; open-lc-id)
open import Data.Nat.Properties using (_≟_)
```

## The absence of promotion is not enough

```agda
Strengthen-by-NoPro : Set
Strengthen-by-NoPro = ∀ {Γ x a w s u v}
                    → (d : ((x , a , w) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v)
                    → ¬ Promotes x d
                    → Γ ∣ s ⊢ u ⟶ᵉ v
```

The derivation at `x ≡ ⊤`: `Me-App` pushes `x`, `Me-FOp` binds the parameter to it, the body
is a variable left alone.

```agda
Γx : Ctx
Γx = (0 , eqv , Top) ∷ []

pvx : Γx ∣ [] prevalid
pvx = Pv-Nil (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ()))

pvx-s : Γx ∣ (fvar 0 ∷ []) prevalid
pvx-s = Pv-Sta pvx lc-fvar (λ { (here refl) → here refl })

redex : Tm
redex = app (lam Top (bvar 0)) (fvar 0)

d-push : Γx ∣ [] ⊢ redex ⟶ᵉ redex
d-push = Me-App (Me-FOp (0 ∷ []) (Me-Top pvx) body) (Me-Var pvx)
  where
    body : ∀ {z} → z ∉ (0 ∷ []) → ((z , eqv , fvar 0) ∷ Γx) ∣ [] ⊢ fvar z ⟶ᵉ fvar z
    body {z} z∉ = Me-Var (Pv-Nil (Pv-EqA (Pv-EqA Pv-Emp (λ ()) lc-Top (λ ()))
                                         z∉′ lc-fvar (λ { (here refl) → here refl })))
      where
        z∉′ : z ∉ dom Γx
        z∉′ (here refl) = z∉ (here refl)
        z∉′ (there ())
```

It promotes nothing.

```agda
d-push-no-pro : ¬ Promotes 0 d-push
d-push-no-pro (Promotes.pro-appˡ (Promotes.pro-fopˡ ()))
d-push-no-pro (Promotes.pro-appˡ (Promotes.pro-fopʳ p ()))
d-push-no-pro (Promotes.pro-appʳ ())
```

And at the empty context the judgement has no derivation: `Me-App` would push an unscoped
variable, and `Me-Bet` produces `x`, not the redex. So the only reduct of the redex at the empty
context is `x`.

```agda
fvar-inj : ∀ {a b} → fvar a ≡ fvar b → a ≡ b
fvar-inj refl = refl

open-var : ∀ u z → (u ^ fvar z) ≡ fvar z → z ∉ fv u → u ≡ bvar 0
open-var (bvar 0) z eq z∉ = refl
open-var (fvar y) z eq z∉ with z ≟ y
... | yes refl = ⊥-elim (z∉ (here refl))
... | no  q    = ⊥-elim (q (sym (fvar-inj eq)))

var-only : ∀ {y w} → [] ∣ [] ⊢ fvar y ⟶ᵉ w → w ≡ fvar y
var-only (Me-Var _)     = refl
var-only (Me-Pro _ () _)

only-x : ∀ {w} → [] ∣ [] ⊢ redex ⟶ᵉ w → w ≡ fvar 0
only-x (Me-App d _) = ⊥-elim (no-push (⟶ᵉ-prevalid d))
only-x (Me-Bet {u' = u'} {v' = v'} L F e) = result
  where
    A  = L ++ fv u'
    z  = fresh A
    z∉L : z ∉ L
    z∉L = ∉-++ˡ (fresh-∉ A)
    z∉u' : z ∉ fv u'
    z∉u' = ∉-++ʳ L (fresh-∉ A)

    u'≡ : u' ≡ bvar 0
    u'≡ = open-var u' z (var-only (F z∉L)) z∉u'

    v'≡ : v' ≡ fvar 0
    v'≡ = var-only e

    result : (u' ^ v') ≡ fvar 0
    result rewrite u'≡ | v'≡ = refl

no-deriv : ¬ ([] ∣ [] ⊢ redex ⟶ᵉ redex)
no-deriv d with only-x d
... | ()

strengthen-by-nopro-false : ¬ Strengthen-by-NoPro
strengthen-by-nopro-false h = no-deriv (h d-push d-push-no-pro)
```

## Avoiding a variable

`Avoids x d`: `x` is in no stack at any node of `d`, in no binder annotation, and is never
promoted. The binder families are only required to avoid `x` at names other than `x` itself,
which is all a strengthening ever uses.

```agda
Avoids : ∀ x {Γ s u v} → Γ ∣ s ⊢ u ⟶ᵉ v → Set
Avoids x (Me-Var {s = s} _)                = x ∉ fvStack s
Avoids x (Me-Top {s = s} _)                = x ∉ fvStack s
Avoids x (Me-TAp {s = s} _)                = x ∉ fvStack s
Avoids x (Me-Pro {s = s} {x = y} _ _ d)    = (x ≢ y) × (x ∉ fvStack s) × Avoids x d
Avoids x (Me-App d e)                      = Avoids x d × Avoids x e
Avoids x (Me-Bet L F e)                    = (∀ {z} (p : z ∉ L) → Avoids x (F p)) × Avoids x e
Avoids x (Me-Fun {t = t} L d F)            =
  (x ∉ fv t) × Avoids x d × (∀ {z} (p : z ∉ L) → z ≢ x → Avoids x (F p))
Avoids x (Me-FOp {α = α} L d F)            =
  (x ∉ fv α) × Avoids x d × (∀ {z} (p : z ∉ L) → z ≢ x → Avoids x (F p))
```

## Dropping a binding from a prevalid extended context

```agda
∉-++ : ∀ {x} {xs ys : List Name} → x ∉ xs → x ∉ ys → x ∉ xs ++ ys
∉-++ {xs = xs} p q h with ∈-++⁻ xs h
... | inj₁ a = p a
... | inj₂ b = q b

dom-drop : ∀ (Δ : Ctx) {Γ x a w y} → y ≢ x
         → y ∈ dom (Δ ++ (x , a , w) ∷ Γ) → y ∈ dom (Δ ++ Γ)
dom-drop Δ {Γ} {x} {a} {w} y≢x h
  with ∈-++⁻ (dom Δ) (subst (_ ∈_) (dom-++ Δ ((x , a , w) ∷ Γ)) h)
... | inj₁ p           = subst (_ ∈_) (sym (dom-++ Δ Γ)) (∈-++⁺ˡ p)
... | inj₂ (here eq)   = ⊥-elim (y≢x eq)
... | inj₂ (there p)   = subst (_ ∈_) (sym (dom-++ Δ Γ)) (∈-++⁺ʳ (dom Δ) p)

∈-drop : ∀ (Δ : Ctx) {Γ x a w y b t} → y ≢ x
       → (y , b , t) ∈ (Δ ++ (x , a , w) ∷ Γ) → (y , b , t) ∈ (Δ ++ Γ)
∈-drop Δ y≢x m with ∈-++⁻ Δ m
... | inj₁ p           = ∈-++⁺ˡ p
... | inj₂ (here refl) = ⊥-elim (y≢x refl)
... | inj₂ (there p)   = ∈-++⁺ʳ Δ p

prevalid-drop-ctx : ∀ (Δ : Ctx) {Γ x a w} → x ∉ fvCtx Δ
                  → (Δ ++ (x , a , w) ∷ Γ) prevalid → (Δ ++ Γ) prevalid
prevalid-drop-ctx [] x∉ pv = tail-prevalid pv
prevalid-drop-ctx ((z , sub , t) ∷ Δ) {Γ} {x} {a} {w} x∉ (Pv-Ctx pv z∉ lt ft) =
  Pv-Ctx (prevalid-drop-ctx Δ (∉-++ʳ (fv t) x∉) pv)
         (λ h → z∉ (dom-⊑ Δ ((x , a , w) ∷ []) h)) lt
         (λ {y} h → dom-drop Δ (λ eq → ∉-++ˡ x∉ (subst (_∈ fv t) eq h)) (ft h))
prevalid-drop-ctx ((z , eqv , t) ∷ Δ) {Γ} {x} {a} {w} x∉ (Pv-EqA pv z∉ lt ft) =
  Pv-EqA (prevalid-drop-ctx Δ (∉-++ʳ (fv t) x∉) pv)
         (λ h → z∉ (dom-⊑ Δ ((x , a , w) ∷ []) h)) lt
         (λ {y} h → dom-drop Δ (λ eq → ∉-++ˡ x∉ (subst (_∈ fv t) eq h)) (ft h))

prevalid-drop : ∀ (Δ : Ctx) {Γ x a w s} → x ∉ fvCtx Δ → x ∉ fvStack s
              → (Δ ++ (x , a , w) ∷ Γ) ∣ s prevalid → (Δ ++ Γ) ∣ s prevalid
prevalid-drop Δ x∉Δ x∉s (Pv-Nil pv) = Pv-Nil (prevalid-drop-ctx Δ x∉Δ pv)
prevalid-drop Δ x∉Δ x∉s (Pv-Sta {α = α} pv lα fα) =
  Pv-Sta (prevalid-drop Δ x∉Δ (∉-++ʳ (fv α) x∉s) pv) lα
         (λ {y} h → dom-drop Δ (λ eq → ∉-++ˡ x∉s (subst (_∈ fv α) eq h)) (fα h))
```

## Strengthening

```agda
⟶ᵉ-strengthen : ∀ (Δ : Ctx) {Γ x a w s u v} → x ∉ fvCtx Δ
              → (d : (Δ ++ (x , a , w) ∷ Γ) ∣ s ⊢ u ⟶ᵉ v) → Avoids x d
              → (Δ ++ Γ) ∣ s ⊢ u ⟶ᵉ v
⟶ᵉ-strengthen Δ x∉Δ (Me-Var pv) av = Me-Var (prevalid-drop Δ x∉Δ av pv)
⟶ᵉ-strengthen Δ x∉Δ (Me-Top pv) av = Me-Top (prevalid-drop Δ x∉Δ av pv)
⟶ᵉ-strengthen Δ x∉Δ (Me-TAp pv) av = Me-TAp (prevalid-drop Δ x∉Δ av pv)
⟶ᵉ-strengthen Δ x∉Δ (Me-Pro pv m d) (x≢y , x∉s , av) =
  Me-Pro (prevalid-drop Δ x∉Δ x∉s pv) (∈-drop Δ (λ eq → x≢y (sym eq)) m)
         (⟶ᵉ-strengthen Δ x∉Δ d av)
⟶ᵉ-strengthen Δ x∉Δ (Me-App d e) (avd , ave) =
  Me-App (⟶ᵉ-strengthen Δ x∉Δ d avd) (⟶ᵉ-strengthen Δ x∉Δ e ave)
⟶ᵉ-strengthen Δ x∉Δ (Me-Bet {u' = u'} L F e) (avF , ave) =
  Me-Bet {u' = u'} L (λ p → ⟶ᵉ-strengthen Δ x∉Δ (F p) (avF p))
         (⟶ᵉ-strengthen Δ x∉Δ e ave)
⟶ᵉ-strengthen Δ {Γ} {x} x∉Δ (Me-Fun {t = t} {u = u} {u' = u'} L d F) (x∉t , avd , avF) =
  Me-Fun {u' = u'} (L ++ x ∷ []) (⟶ᵉ-strengthen Δ x∉Δ d avd) body
  where
    body : ∀ {z} → z ∉ (L ++ x ∷ [])
         → ((z , sub , t) ∷ Δ ++ Γ) ∣ [] ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)
    body {z} z∉ = ⟶ᵉ-strengthen ((z , sub , t) ∷ Δ) (∉-++ x∉t x∉Δ) (F (∉-++ˡ z∉))
                                (avF (∉-++ˡ z∉) z≢x)
      where
        z≢x : z ≢ x
        z≢x refl = ∉-++ʳ L z∉ (here refl)
⟶ᵉ-strengthen Δ {Γ} {x} x∉Δ (Me-FOp {s = s} {α = α} {u = u} {u' = u'} L d F) (x∉α , avd , avF) =
  Me-FOp {u' = u'} (L ++ x ∷ []) (⟶ᵉ-strengthen Δ x∉Δ d avd) body
  where
    body : ∀ {z} → z ∉ (L ++ x ∷ [])
         → ((z , eqv , α) ∷ Δ ++ Γ) ∣ s ⊢ (u ^ fvar z) ⟶ᵉ (u' ^ fvar z)
    body {z} z∉ = ⟶ᵉ-strengthen ((z , eqv , α) ∷ Δ) (∉-++ x∉α x∉Δ) (F (∉-++ˡ z∉))
                                (avF (∉-++ˡ z∉) z≢x)
      where
        z≢x : z ≢ x
        z≢x refl = ∉-++ʳ L z∉ (here refl)
```

## A derivation at a context that does not bind `x` avoids `x`

Prevalidity scopes every stack entry and every binder annotation in the context, so a
variable outside the domain is in none of them, and it cannot be promoted.

```agda
stack-fv : ∀ {Γ s} → Γ ∣ s prevalid → fvStack s ⊑ dom Γ
stack-fv (Pv-Nil _) ()
stack-fv (Pv-Sta {α = α} pv lα fα) h with ∈-++⁻ (fv α) h
... | inj₁ p = fα p
... | inj₂ p = stack-fv pv p

unbound-avoids : ∀ {Γ s u v} x → x ∉ dom Γ → (d : Γ ∣ s ⊢ u ⟶ᵉ v) → Avoids x d
unbound-avoids x x∉ (Me-Var pv) = λ h → x∉ (stack-fv pv h)
unbound-avoids x x∉ (Me-Top pv) = λ h → x∉ (stack-fv pv h)
unbound-avoids x x∉ (Me-TAp pv) = λ h → x∉ (stack-fv pv h)
unbound-avoids x x∉ (Me-Pro pv m d) =
  (λ { refl → x∉ (∈-dom m) }) , (λ h → x∉ (stack-fv pv h)) , unbound-avoids x x∉ d
unbound-avoids x x∉ (Me-App d e) = unbound-avoids x x∉ d , unbound-avoids x x∉ e
unbound-avoids x x∉ (Me-Bet L F e) = (λ p → unbound-avoids x x∉ (F p)) , unbound-avoids x x∉ e
unbound-avoids {Γ} x x∉ (Me-Fun {t = t} L d F) =
  (λ h → x∉ (head-fv inner h)) , unbound-avoids x x∉ d ,
  (λ {z} p z≢x → unbound-avoids x (x∉′ z≢x) (F p))
  where
    inner : ((fresh L , sub , t) ∷ Γ) prevalid
    inner = prevalid-ctx (⟶ᵉ-prevalid (F (fresh-∉ L)))
    x∉′ : ∀ {z} → z ≢ x → x ∉ dom ((z , sub , t) ∷ Γ)
    x∉′ z≢x (here eq)  = z≢x (sym eq)
    x∉′ z≢x (there h)  = x∉ h
unbound-avoids {Γ} x x∉ (Me-FOp {α = α} {u = u} {u' = u'} L d F) =
  (λ h → x∉ (prevalid-head-fv (⟶ᵉ-prevalid (Me-FOp {u = u} {u' = u'} L d F)) h)) ,
  unbound-avoids x x∉ d ,
  (λ {z} p z≢x → unbound-avoids x (x∉′ z≢x) (F p))
  where
    x∉′ : ∀ {z} → z ≢ x → x ∉ dom ((z , eqv , α) ∷ Γ)
    x∉′ z≢x (here eq)  = z≢x (sym eq)
    x∉′ z≢x (there h)  = x∉ h
```

The same for a context reduction: every piece avoids `x`.

```agda
AvoidsC : ∀ x {Γ s Γ' s'} → Γ ∣ s ↣ Γ' ∣ s' → Set
AvoidsC x Ct-Refl       = ⊤
AvoidsC x (Ct-Ann c d)  = AvoidsC x c × Avoids x d
AvoidsC x (Ct-Stk c d)  = AvoidsC x c × Avoids x d

unbound-avoidsC : ∀ {Γ s Γ' s'} x → x ∉ dom Γ → (c : Γ ∣ s ↣ Γ' ∣ s') → AvoidsC x c
unbound-avoidsC x x∉ Ct-Refl      = tt
unbound-avoidsC x x∉ (Ct-Ann c d) =
  unbound-avoidsC x (λ h → x∉ (there h)) c , unbound-avoids x (λ h → x∉ (there h)) d
unbound-avoidsC x x∉ (Ct-Stk c d) = unbound-avoidsC x x∉ c , unbound-avoids x x∉ d
```

## What this establishes

`strengthen-by-nopro-false`: the step "the derivation does not promote `x`, so it holds without
`x`" that the `Me-App`/`Me-Bet` case of Lemma 2's printed proof makes is not valid as stated,
independently of whether the absence of promotion can be guaranteed (`MPSS/Moreover` shows it
cannot, as printed). A derivation that pushes `x` has no counterpart once `x` is unbound.

`⟶ᵉ-strengthen`: the valid form of the step. `Avoids x d` is the condition, and it is the
condition the diamond's invariant has to carry in place of "no promotion of `x`": *a derivation
and a context reduction that both avoid `x` yield a join that avoids `x`*. `unbound-avoids` and
`unbound-avoidsC` give the base of that invariant for free at the `Me-App`/`Me-Bet` case, where
the parameter is fresh for the whole context.
