# MPSS: context weakening

Inserting a context `Θ` in the middle of a context preserves both reductions, the subtyping
chain, and the three well-formedness judgements of v2 Figure 4. This is the MPSS counterpart of
`../PSS/Weakening`, and it follows the same shape: prevalidity of the **enlarged** context is a
hypothesis, since a bigger context is not automatically prevalid; and each binder rule re-picks
its fresh name by enlarging the cofinite avoid-set with the domain of the enlarged context, so
no renaming lemma is needed.

The extra work relative to v1 is only that MPSS has more rules: `Me-Pro` recurses at the same
extended context, `Me-App` and `Ms-App` at a pushed one, and `Me-FOp` and `Ms-FOp` bind the
popped operand under the surviving stack (where `prevalid-cons` from `MPSS/StackPush` is what
adds the entry).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Weakening where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.StackPush using (prevalid-cons; dom-++)
```

## Domains

Membership and domain inclusion both survive the insertion.

```agda
∈-weaken : ∀ (Δ Θ : Ctx) {Γ y a t}
         → (y , a , t) ∈ (Δ ++ Γ)
         → (y , a , t) ∈ (Δ ++ Θ ++ Γ)
∈-weaken Δ Θ {Γ} m with ∈-++⁻ Δ m
... | inj₁ p = ∈-++⁺ˡ p
... | inj₂ p = ∈-++⁺ʳ Δ (∈-++⁺ʳ Θ p)

dom-⊑ : ∀ (Δ Θ : Ctx) {Γ} → dom (Δ ++ Γ) ⊑ dom (Δ ++ Θ ++ Γ)
dom-⊑ Δ Θ {Γ} h
  with ∈-++⁻ (dom Δ) (subst (_ ∈_) (dom-++ Δ Γ) h)
... | inj₁ p = subst (_ ∈_) (sym (dom-++ Δ (Θ ++ Γ))) (∈-++⁺ˡ p)
... | inj₂ p = subst (_ ∈_) (sym (dom-++ Δ (Θ ++ Γ)))
                     (∈-++⁺ʳ (dom Δ) (subst (_ ∈_) (sym (dom-++ Θ Γ)) (∈-++⁺ʳ (dom Θ) p)))
```

## Weakening the two reductions

Both reductions carry their extended context, so every leaf rule just swaps in the enlarged
prevalidity. The structural rules differ in where their premise lives:

- `Me-Pro`: same extended context.
- `Me-App`, `Ms-App`: the pushed stack. The operand's local closure and scoping come from the
  premise's own prevalidity, and scoping is carried over by `dom-⊑`.
- `Me-Fun`, `Ms-Fun`: under `y ≤ t` at the empty stack. The entry's local closure and scoping
  come from the prevalidity the premise derivation carries, via `head-lc` and `head-fv`.
- `Me-FOp`, `Ms-FOp`: under `y ≡ α` at the surviving stack `s`. Here the operand `α` is the
  head of the stack in the hypothesis, so `prevalid-head-lc` and `prevalid-head-fv` of the
  enlarged prevalidity give exactly what `prevalid-cons` needs.

```agda
⟶ᵉ-weaken : ∀ (Δ Θ : Ctx) {Γ s u v}
          → (Δ ++ Θ ++ Γ) ∣ s prevalid
          → (Δ ++ Γ) ∣ s ⊢ u ⟶ᵉ v
          → (Δ ++ Θ ++ Γ) ∣ s ⊢ u ⟶ᵉ v
⟶ᵉ-weaken Δ Θ pv (Me-Var _)      = Me-Var pv
⟶ᵉ-weaken Δ Θ pv (Me-Top _)      = Me-Top pv
⟶ᵉ-weaken Δ Θ pv (Me-TAp _)      = Me-TAp pv
⟶ᵉ-weaken Δ Θ pv (Me-Pro _ m d)  =
  Me-Pro pv (∈-weaken Δ Θ m) (⟶ᵉ-weaken Δ Θ pv d)
⟶ᵉ-weaken Δ Θ pv (Me-App d e)    =
  Me-App (⟶ᵉ-weaken Δ Θ pv′ d) (⟶ᵉ-weaken Δ Θ (prevalid-nil pv) e)
  where
    inner = ⟶ᵉ-prevalid d
    pv′ = Pv-Sta pv (prevalid-head-lc inner) (λ h → dom-⊑ Δ Θ (prevalid-head-fv inner h))
⟶ᵉ-weaken Δ Θ pv (Me-Bet {u' = u'} L F e) =
  Me-Bet {u' = u'} L (λ x∉ → ⟶ᵉ-weaken Δ Θ pv (F x∉))
         (⟶ᵉ-weaken Δ Θ (prevalid-nil pv) e)
⟶ᵉ-weaken Δ Θ {Γ} pv (Me-Fun {t = t} {u = u} {u' = u'} L d F) =
  Me-Fun (L ++ dom (Δ ++ Θ ++ Γ)) (⟶ᵉ-weaken Δ Θ pv d) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ∣ [] ⊢ (u ^ fvar y) ⟶ᵉ (u' ^ fvar y)
    body {y} y∉ = ⟶ᵉ-weaken ((y , sub , t) ∷ Δ) Θ pv′ (F (∉-++ˡ y∉))
      where
        inner : ((y , sub , t) ∷ Δ ++ Γ) prevalid
        inner = prevalid-ctx (⟶ᵉ-prevalid (F (∉-++ˡ y∉)))
        pv′ : ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ∣ [] prevalid
        pv′ = Pv-Nil (Pv-Ctx (prevalid-ctx pv) (∉-++ʳ L y∉) (head-lc inner)
                             (λ h → dom-⊑ Δ Θ (head-fv inner h)))
⟶ᵉ-weaken Δ Θ {Γ} pv (Me-FOp {s = s} {α = α} {u = u} {u' = u'} L d F) =
  Me-FOp (L ++ dom (Δ ++ Θ ++ Γ)) (⟶ᵉ-weaken Δ Θ (prevalid-nil pv) d) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , eqv , α) ∷ Δ ++ Θ ++ Γ) ∣ s ⊢ (u ^ fvar y) ⟶ᵉ (u' ^ fvar y)
    body {y} y∉ = ⟶ᵉ-weaken ((y , eqv , α) ∷ Δ) Θ pv′ (F (∉-++ˡ y∉))
      where
        pv′ : ((y , eqv , α) ∷ Δ ++ Θ ++ Γ) ∣ s prevalid
        pv′ = prevalid-cons (prevalid-pop pv) (∉-++ʳ L y∉)
                            (prevalid-head-lc pv) (prevalid-head-fv pv)
```

```agda
⟶ˢ-weaken : ∀ (Δ Θ : Ctx) {Γ s u v}
          → (Δ ++ Θ ++ Γ) ∣ s prevalid
          → (Δ ++ Γ) ∣ s ⊢ u ⟶ˢ v
          → (Δ ++ Θ ++ Γ) ∣ s ⊢ u ⟶ˢ v
⟶ˢ-weaken Δ Θ pv (Ms-Pro _ m)  = Ms-Pro pv (∈-weaken Δ Θ m)
⟶ˢ-weaken Δ Θ pv (Ms-Top _)    = Ms-Top pv
⟶ˢ-weaken Δ Θ pv (Ms-Equ _ e)  = Ms-Equ pv (⟶ᵉ-weaken Δ Θ pv e)
⟶ˢ-weaken Δ Θ pv (Ms-App d)    = Ms-App (⟶ˢ-weaken Δ Θ pv′ d)
  where
    inner = ⟶ˢ-prevalid d
    pv′ = Pv-Sta pv (prevalid-head-lc inner) (λ h → dom-⊑ Δ Θ (prevalid-head-fv inner h))
⟶ˢ-weaken Δ Θ {Γ} pv (Ms-Fun {t = t} {u = u} {u' = u'} L F) =
  Ms-Fun (L ++ dom (Δ ++ Θ ++ Γ)) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ∣ [] ⊢ (u ^ fvar y) ⟶ˢ (u' ^ fvar y)
    body {y} y∉ = ⟶ˢ-weaken ((y , sub , t) ∷ Δ) Θ pv′ (F (∉-++ˡ y∉))
      where
        inner : ((y , sub , t) ∷ Δ ++ Γ) prevalid
        inner = prevalid-ctx (⟶ˢ-prevalid (F (∉-++ˡ y∉)))
        pv′ : ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ∣ [] prevalid
        pv′ = Pv-Nil (Pv-Ctx (prevalid-ctx pv) (∉-++ʳ L y∉) (head-lc inner)
                             (λ h → dom-⊑ Δ Θ (head-fv inner h)))
⟶ˢ-weaken Δ Θ {Γ} pv (Ms-FOp {s = s} {α = α} {u = u} {u' = u'} L F) =
  Ms-FOp (L ++ dom (Δ ++ Θ ++ Γ)) body
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , eqv , α) ∷ Δ ++ Θ ++ Γ) ∣ s ⊢ (u ^ fvar y) ⟶ˢ (u' ^ fvar y)
    body {y} y∉ = ⟶ˢ-weaken ((y , eqv , α) ∷ Δ) Θ pv′ (F (∉-++ˡ y∉))
      where
        pv′ : ((y , eqv , α) ∷ Δ ++ Θ ++ Γ) ∣ s prevalid
        pv′ = prevalid-cons (prevalid-pop pv) (∉-++ʳ L y∉)
                            (prevalid-head-lc pv) (prevalid-head-fv pv)
```

## Weakening the subtyping chain

Every rule of Figure 3 stays at the same extended context, so this is pure threading.

```agda
⊲-weaken : ∀ (Δ Θ : Ctx) {Γ s u m t}
         → (Δ ++ Θ ++ Γ) ∣ s prevalid
         → (Δ ++ Γ) ∣ s ⊢ u ⊲[ m ] t
         → (Δ ++ Θ ++ Γ) ∣ s ⊢ u ⊲[ m ] t
⊲-weaken Δ Θ pv (As-Refl _)       = As-Refl pv
⊲-weaken Δ Θ pv (As-Left-1 st d)  = As-Left-1 (⟶ˢ-weaken Δ Θ pv st) (⊲-weaken Δ Θ pv d)
⊲-weaken Δ Θ pv (As-Left-2 st d)  = As-Left-2 (⟶ᵉ-weaken Δ Θ pv st) (⊲-weaken Δ Θ pv d)
⊲-weaken Δ Θ pv (As-Right d st)   = As-Right (⊲-weaken Δ Θ pv d) (⟶ᵉ-weaken Δ Θ pv st)
```

## Weakening well-formedness and well-subtyping

The three judgements of Figure 4 are over a logical context, with their reduction premises at
the empty stack; the hypothesis is accordingly `(Δ ++ Θ ++ Γ) prevalid`, and the reduction
premises are weakened at `Pv-Nil` of it. The three proofs are mutually recursive, exactly as the
judgements are: `Wf-App` needs `⊑*wf-weaken`, and `Ws-Lf2` and `Ws-Sub` need `wf-weaken`.

The one binder rule, `Wf-Fun`, is handled as `Me-Fun` was: the body's own derivation carries
prevalidity of `(y , sub , t) ∷ Δ ++ Γ`, which supplies the entry's local closure and scoping.

```agda
wf-weaken   : ∀ (Δ Θ : Ctx) {Γ t}
            → (Δ ++ Θ ++ Γ) prevalid
            → (Δ ++ Γ) ⊢ t wf
            → (Δ ++ Θ ++ Γ) ⊢ t wf

⊑wf-weaken  : ∀ (Δ Θ : Ctx) {Γ u m t}
            → (Δ ++ Θ ++ Γ) prevalid
            → (Δ ++ Γ) ⊢ u ⊑wf[ m ] t
            → (Δ ++ Θ ++ Γ) ⊢ u ⊑wf[ m ] t

⊑*wf-weaken : ∀ (Δ Θ : Ctx) {Γ u m t}
            → (Δ ++ Θ ++ Γ) prevalid
            → (Δ ++ Γ) ⊢ u ⊑*wf[ m ] t
            → (Δ ++ Θ ++ Γ) ⊢ u ⊑*wf[ m ] t

wf-weaken Δ Θ pv (Wf-PrS _ m)  = Wf-PrS pv (∈-weaken Δ Θ m)
wf-weaken Δ Θ pv (Wf-PrE _ m)  = Wf-PrE pv (∈-weaken Δ Θ m)
wf-weaken Δ Θ pv (Wf-Top _)    = Wf-Top pv
wf-weaken Δ Θ pv (Wf-App d₁ d₂) =
  Wf-App (⊑*wf-weaken Δ Θ pv d₁) (⊑*wf-weaken Δ Θ pv d₂)
wf-weaken Δ Θ {Γ} pv (Wf-Fun {t = t} {u = u} L F d) =
  Wf-Fun (L ++ dom (Δ ++ Θ ++ Γ)) body (wf-weaken Δ Θ pv d)
  where
    body : ∀ {y} → y ∉ (L ++ dom (Δ ++ Θ ++ Γ))
         → ((y , sub , t) ∷ Δ ++ Θ ++ Γ) ⊢ (u ^ fvar y) wf
    body {y} y∉ = wf-weaken ((y , sub , t) ∷ Δ) Θ pv′ (F (∉-++ˡ y∉))
      where
        inner : ((y , sub , t) ∷ Δ ++ Γ) prevalid
        inner = wf⇒prevalid (F (∉-++ˡ y∉))
        pv′ : ((y , sub , t) ∷ Δ ++ Θ ++ Γ) prevalid
        pv′ = Pv-Ctx pv (∉-++ʳ L y∉) (head-lc inner) (λ h → dom-⊑ Δ Θ (head-fv inner h))

⊑wf-weaken Δ Θ pv (Ws-Rfl _)          = Ws-Rfl pv
⊑wf-weaken Δ Θ pv (Ws-Lf1 st d)       =
  Ws-Lf1 (⟶ᵉ-weaken Δ Θ (Pv-Nil pv) st) (⊑wf-weaken Δ Θ pv d)
⊑wf-weaken Δ Θ pv (Ws-Lf2 w st w′ d)  =
  Ws-Lf2 (wf-weaken Δ Θ pv w) (⟶ˢ-weaken Δ Θ (Pv-Nil pv) st)
         (wf-weaken Δ Θ pv w′) (⊑wf-weaken Δ Θ pv d)
⊑wf-weaken Δ Θ pv (Ws-Rgh d st)       =
  Ws-Rgh (⊑wf-weaken Δ Θ pv d) (⟶ᵉ-weaken Δ Θ (Pv-Nil pv) st)

⊑*wf-weaken Δ Θ pv (Ws-Sub w d w′)    =
  Ws-Sub (wf-weaken Δ Θ pv w) (⊑wf-weaken Δ Θ pv d) (wf-weaken Δ Θ pv w′)
⊑*wf-weaken Δ Θ pv (Ws-Trs d₁ w d₂)   =
  Ws-Trs (⊑*wf-weaken Δ Θ pv d₁) (wf-weaken Δ Θ pv w) (⊑*wf-weaken Δ Θ pv d₂)
```

## Adding one entry on top

The instances with `Δ = []` and `Θ` a single entry, which is how weakening is usually consumed.

```agda
wf-weaken₁ : ∀ {Γ x a w t}
           → ((x , a , w) ∷ Γ) prevalid
           → Γ ⊢ t wf
           → ((x , a , w) ∷ Γ) ⊢ t wf
wf-weaken₁ {x = x} {a} {w} pv d = wf-weaken [] ((x , a , w) ∷ []) pv d

⊑*wf-weaken₁ : ∀ {Γ x a w u m t}
             → ((x , a , w) ∷ Γ) prevalid
             → Γ ⊢ u ⊑*wf[ m ] t
             → ((x , a , w) ∷ Γ) ⊢ u ⊑*wf[ m ] t
⊑*wf-weaken₁ {x = x} {a} {w} pv d = ⊑*wf-weaken [] ((x , a , w) ∷ []) pv d
```

## What this establishes

**Context weakening for MPSS**, at every level of the system, with prevalidity of the enlarged
context as a hypothesis:

- `∈-weaken`, `dom-⊑`: membership and domain inclusion survive inserting `Θ`.
- `⟶ᵉ-weaken`, `⟶ˢ-weaken`: both reductions of Figure 2, at any stack.
- `⊲-weaken`: the subtyping chain of Figure 3, in either mode.
- `wf-weaken`, `⊑wf-weaken`, `⊑*wf-weaken`: the three judgements of Figure 4, proved together.
- `wf-weaken₁`, `⊑*wf-weaken₁`: the single-entry instances.

As in `../PSS/Weakening`, the only place a proof does more than thread the hypothesis is at a
binder, where the fresh name is re-picked to avoid the enlarged domain and the new entry's
prevalidity is rebuilt from what the premise derivation already carries.
