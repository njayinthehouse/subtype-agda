# MPSS: an evaluation step is a chain of equivalence steps, at any configuration

The printed Proposition 17 says an evaluation step `t ↦ t'` is a single equivalence step
`Γ;s ⊢ t ⟶≡ t'`. It is false (`MPSS/BetaScope`, `MPSS/Prop17Refuted`): `Me-Bet` reduces the
redex body at a context that does not bind the opened name. `MPSS/Prop17Chain` repairs it as a
chain of equivalence steps at the empty stack, for well-formed terms, with well-formedness
carried along the chain.

This module proves the chain form with no well-formedness hypothesis and at an arbitrary stack:
if `t` is locally closed, its free variables are in `dom Γ`, and `Γ;s` is prevalid, then
`t ↦ t'` gives `Γ ∣ s ⊢ t ⟶ᵉ* t'`. The β case is the two steps of `MPSS/Prop17Chain` — bind the
parameter to the operand by `Me-FOp` under `Me-App` and unfold it throughout the body, then
contract by `Me-Bet` a body in which the parameter no longer occurs — and the congruence cases
lift a chain through `Me-App`, `Me-Fun` and `Me-FOp`. Two corollaries for the machine relation
of `MPSS/Subtyping` follow: the contractum is below the redex, and the redex is below the
contractum.

The chain type is the one of `MPSS/Strip`. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.EvalChain where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)

open import MPSS.WellFormed
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_)
open import MPSS.Prop17Chain using (unfold; ⊑-there)
open import MPSS.StackPush
  using (⟶ᵉ-refl; prevalid-cons; fv-lam-ann; fv-lam-body; fv-open-cons; fv-app-arg; fv-app-op)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (fv-⟶ᵉ-dom)
open import MPSS.Wrap using (wrapᵉ-fun; wrapᵉ-fop)
open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; closeRec; subst-intro; open-lc-id)
open import PSS.Scope using (fv-open-split)
open import PSS.Close using (close-open)
open import PSS.Progress using (↦-lc)
```

## Lifting a chain through the congruences

**The operator of an application.** The operator's chain is at the stack holding the operand;
each step goes under `Me-App` with the operand reflexive.

```agda
app-l-chain : ∀ {Γ s u u' v}
            → Γ ∣ s prevalid → LC v → fv v ⊑ dom Γ
            → Γ ∣ (v ∷ s) ⊢ u ⟶ᵉ* u' → Γ ∣ s ⊢ app u v ⟶ᵉ* app u' v
app-l-chain pv lv fvv (ε _)   = ε pv
app-l-chain pv lv fvv (d ◅ p) =
  Me-App d (⟶ᵉ-refl (prevalid-nil pv) lv fvv) ◅ app-l-chain pv lv fvv p
```

**The operand of an application.** The operand's chain is at the empty stack. `Me-App` reduces
the operator at the stack holding the source operand, so the reflexive operator step is taken
at a different stack for each step of the chain; local closure and scoping of the current
operand follow the chain along.

```agda
app-r-chain : ∀ {Γ s u v v'}
            → Γ ∣ s prevalid → LC u → fv u ⊑ dom Γ → LC v → fv v ⊑ dom Γ
            → Γ ∣ [] ⊢ v ⟶ᵉ* v' → Γ ∣ s ⊢ app u v ⟶ᵉ* app u v'
app-r-chain pv lu fvu lv fvv (ε _)   = ε pv
app-r-chain pv lu fvu lv fvv (d ◅ p) =
  Me-App (⟶ᵉ-refl (Pv-Sta pv lv fvv) lu fvu) d
    ◅ app-r-chain pv lu fvu (⟶ᵉ-lc lv d) (fv-⟶ᵉ-dom d fvv) p
```

**The annotation of an abstraction.** The annotation's chain is at the empty stack. At the empty
stack each step is `Me-Fun`, whose reflexive body is under the current annotation; at a stack
`δ ∷ s` each step is `Me-FOp`, whose reflexive body is under `x ≡ δ`.

```agda
lam-l-chain : ∀ {Γ s t t' b}
            → Γ ∣ s prevalid → LC t → fv t ⊑ dom Γ
            → (L : List Name) → (∀ {x} → x ∉ L → LC (b ^ fvar x)) → fv b ⊑ dom Γ
            → Γ ∣ [] ⊢ t ⟶ᵉ* t' → Γ ∣ s ⊢ lam t b ⟶ᵉ* lam t' b
lam-l-chain pv lt fvt L F fvb (ε _) = ε pv
lam-l-chain {Γ} {[]} {t} {t'} {b} pv lt fvt L F fvb (d ◅ p) =
  Me-Fun {u' = b} (L ++ dom Γ) d body ◅ lam-l-chain pv (⟶ᵉ-lc lt d) (fv-⟶ᵉ-dom d fvt) L F fvb p
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , sub , t) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ (b ^ fvar x)
    body {x} x∉ = ⟶ᵉ-refl (prevalid-cons pv (∉-++ʳ L x∉) lt fvt)
                          (F (∉-++ˡ x∉)) (fv-open-cons {b} x fvb)
lam-l-chain {Γ} {δ ∷ s} {t} {t'} {b} pv lt fvt L F fvb (d ◅ p) =
  Me-FOp {u' = b} (L ++ dom Γ) d body ◅ lam-l-chain pv (⟶ᵉ-lc lt d) (fv-⟶ᵉ-dom d fvt) L F fvb p
  where
    body : ∀ {x} → x ∉ (L ++ dom Γ)
         → ((x , eqv , δ) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ (b ^ fvar x)
    body {x} x∉ = ⟶ᵉ-refl (prevalid-cons (prevalid-pop pv) (∉-++ʳ L x∉)
                                         (prevalid-head-lc pv) (prevalid-head-fv pv))
                          (F (∉-++ˡ x∉)) (fv-open-cons {b} x fvb)
```

**The body of an abstraction.** The chain at one fresh name is closed over that name, and each
step is wrapped by `Me-Fun` or `Me-FOp` (`MPSS/Wrap`).

```agda
fun-body-chain : ∀ {Γ w a c} x → x ∉ dom Γ → Γ ∣ [] prevalid → LC a
               → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ* c
               → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ᵉ* lam w (closeRec 0 x c)
fun-body-chain x x∉ pv la (ε _)   = ε pv
fun-body-chain x x∉ pv la (d ◅ p) =
  wrapᵉ-fun x x∉ la (⟶ᵉ-lc la d) d ◅ fun-body-chain x x∉ pv (⟶ᵉ-lc la d) p

fop-body-chain : ∀ {Γ s w δ a c} x → x ∉ dom Γ → x ∉ fvStack s → Γ ∣ (δ ∷ s) prevalid
               → LC w → fv w ⊑ dom Γ → LC a
               → ((x , eqv , δ) ∷ Γ) ∣ s ⊢ a ⟶ᵉ* c
               → Γ ∣ (δ ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ᵉ* lam w (closeRec 0 x c)
fop-body-chain x x∉ x∉s pv lw fw la (ε _)   = ε pv
fop-body-chain x x∉ x∉s pv lw fw la (d ◅ p) =
  wrapᵉ-fop x x∉ x∉s la (⟶ᵉ-lc la d) lw fw d
    ◅ fop-body-chain x x∉ x∉s pv lw fw (⟶ᵉ-lc la d) p
```

## Scoping of a contractum

```agda
fv-open-⊑ : ∀ {b c} {N : List Name} → fv b ⊑ N → fv c ⊑ N → fv (b ^ c) ⊑ N
fv-open-⊑ {b} {c} fb fc h with fv-open-split 0 c b h
... | inj₁ p = fb p
... | inj₂ p = fc p
```

## The chain

```agda
↦⇒⟶ᵉ* : ∀ {Γ s t t'} → LC t → fv t ⊑ dom Γ → Γ ∣ s prevalid → t ↦ t' → Γ ∣ s ⊢ t ⟶ᵉ* t'
```

**β.** Two steps, at the stack `s` of the configuration. First `Me-App` over `Me-FOp`: the
operator is reduced at `c ∷ s`, so the parameter is bound `x ≡ c` and `unfold` replaces it by
`c` throughout the body; the abstraction's body becomes the contractum, which is locally closed.
Then `Me-Bet`, whose body premise is a reflexive step at `Γ ∣ s` because opening the locally
closed contractum at a name leaves it unchanged.

```agda
↦⇒⟶ᵉ* {Γ} {s} (lc-app {lam t b} {c} (lc-lam L lt F) lc) f pv (E-App llam _) =
  s₁ ◅ s₂ ◅ ε pv
  where
    fvl : fv (lam t b) ⊑ dom Γ
    fvl = fv-app-op {lam t b} {c} f
    fvt : fv t ⊑ dom Γ
    fvt = fv-lam-ann {t} {b} fvl
    fvb : fv b ⊑ dom Γ
    fvb = fv-lam-body {t} {b} fvl
    fvc : fv c ⊑ dom Γ
    fvc = fv-app-arg {lam t b} {c} f

    lb : LC (b ^ c)
    lb = ↦-lc (lc-app (lc-lam L lt F) lc) (E-App llam lc)
    fvbc : fv (b ^ c) ⊑ dom Γ
    fvbc = fv-open-⊑ {b} {c} fvb fvc

    pvc : Γ ∣ (c ∷ s) prevalid
    pvc = Pv-Sta pv lc fvc

    s₁ : Γ ∣ s ⊢ app (lam t b) c ⟶ᵉ app (lam t (b ^ c)) c
    s₁ = Me-App (Me-FOp {u = b} {u' = b ^ c} (L ++ fv b ++ dom Γ)
                        (⟶ᵉ-refl (prevalid-nil pv) lt fvt) body)
                (⟶ᵉ-refl (prevalid-nil pv) lc fvc)
      where
        body : ∀ {x} → x ∉ (L ++ fv b ++ dom Γ)
             → ((x , eqv , c) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ ((b ^ c) ^ fvar x)
        body {x} x∉ =
          subst (λ q → ((x , eqv , c) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ q) eq
                (unfold (prevalid-cons pv (∉-++ʳ (fv b) (∉-++ʳ L x∉)) lc fvc)
                        (here refl) lc (⊑-there fvc)
                        (F (∉-++ˡ x∉)) (fv-open-cons {b} x fvb))
          where
            eq : (b ^ fvar x) [ x := c ] ≡ (b ^ c) ^ fvar x
            eq = trans (sym (subst-intro {b} lc x (∉-++ˡ (∉-++ʳ L x∉)))) (open-lc-id lb 0 (fvar x))

    s₂ : Γ ∣ s ⊢ app (lam t (b ^ c)) c ⟶ᵉ (b ^ c)
    s₂ = subst (λ q → Γ ∣ s ⊢ app (lam t (b ^ c)) c ⟶ᵉ q) (sym (open-lc-id lb 0 c))
               (Me-Bet {u = b ^ c} {u' = b ^ c} {v = c} {v' = c} (dom Γ) body₂
                       (⟶ᵉ-refl (prevalid-nil pv) lc fvc))
      where
        body₂ : ∀ {x} → x ∉ dom Γ → Γ ∣ s ⊢ ((b ^ c) ^ fvar x) ⟶ᵉ ((b ^ c) ^ fvar x)
        body₂ {x} _ = subst (λ q → Γ ∣ s ⊢ q ⟶ᵉ q) (open-lc-id lb 0 (fvar x))
                            (⟶ᵉ-refl pv lb fvbc)
```

**The congruences.**

```agda
↦⇒⟶ᵉ* (lc-lam {t} {b} L lt F) f pv (E-Lam-l st) =
  lam-l-chain pv lt fvt L F (fv-lam-body {t} {b} f) (↦⇒⟶ᵉ* lt fvt (prevalid-nil pv) st)
  where fvt = fv-lam-ann {t} {b} f

↦⇒⟶ᵉ* {Γ} {[]} (lc-lam {t} {b} L lt F) f pv (E-Lam-r {u' = b'} L' F') =
  subst₂ (λ p q → Γ ∣ [] ⊢ lam t p ⟶ᵉ* lam t q)
         (close-open 0 x b x∉b) (close-open 0 x b' x∉b')
         (fun-body-chain x x∉Γ pv (F x∉L)
           (↦⇒⟶ᵉ* (F x∉L) (fv-open-cons {b} x (fv-lam-body {t} {b} f))
                   (prevalid-cons pv x∉Γ lt (fv-lam-ann {t} {b} f)) (F' x∉L')))
  where
    A    = L ++ L' ++ dom Γ ++ fv b ++ fv b'
    x    = fresh A
    x∉A  = fresh-∉ A
    x∉L  = ∉-++ˡ x∉A
    x∉L' = ∉-++ˡ (∉-++ʳ L x∉A)
    x∉Γ  = ∉-++ˡ (∉-++ʳ L' (∉-++ʳ L x∉A))
    x∉b  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L' (∉-++ʳ L x∉A)))
    x∉b' = ∉-++ʳ (fv b) (∉-++ʳ (dom Γ) (∉-++ʳ L' (∉-++ʳ L x∉A)))

↦⇒⟶ᵉ* {Γ} {δ ∷ s} (lc-lam {t} {b} L lt F) f pv (E-Lam-r {u' = b'} L' F') =
  subst₂ (λ p q → Γ ∣ (δ ∷ s) ⊢ lam t p ⟶ᵉ* lam t q)
         (close-open 0 x b x∉b) (close-open 0 x b' x∉b')
         (fop-body-chain x x∉Γ x∉s pv lt (fv-lam-ann {t} {b} f) (F x∉L)
           (↦⇒⟶ᵉ* (F x∉L) (fv-open-cons {b} x (fv-lam-body {t} {b} f))
                   (prevalid-cons (prevalid-pop pv) x∉Γ (prevalid-head-lc pv) (prevalid-head-fv pv))
                   (F' x∉L')))
  where
    A    = L ++ L' ++ dom Γ ++ fv b ++ fv b' ++ fvStack s
    x    = fresh A
    x∉A  = fresh-∉ A
    x∉L  = ∉-++ˡ x∉A
    x∉L' = ∉-++ˡ (∉-++ʳ L x∉A)
    x∉Γ  = ∉-++ˡ (∉-++ʳ L' (∉-++ʳ L x∉A))
    x∉b  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L' (∉-++ʳ L x∉A)))
    x∉b' = ∉-++ˡ (∉-++ʳ (fv b) (∉-++ʳ (dom Γ) (∉-++ʳ L' (∉-++ʳ L x∉A))))
    x∉s  = ∉-++ʳ (fv b') (∉-++ʳ (fv b) (∉-++ʳ (dom Γ) (∉-++ʳ L' (∉-++ʳ L x∉A))))

↦⇒⟶ᵉ* (lc-app {u} {v} lu lv) f pv (E-App-l st) =
  app-l-chain pv lv fvv (↦⇒⟶ᵉ* lu (fv-app-op {u} {v} f) (Pv-Sta pv lv fvv) st)
  where fvv = fv-app-arg {u} {v} f

↦⇒⟶ᵉ* (lc-app {u} {v} lu lv) f pv (E-App-r st) =
  app-r-chain pv lu (fv-app-op {u} {v} f) lv fvv (↦⇒⟶ᵉ* lv fvv (prevalid-nil pv) st)
  where fvv = fv-app-arg {u} {v} f
```

## The machine relation along a chain

`As-Right` takes an equivalence step on the right-hand term, so a chain from `a` to `c` puts
`c` below `a`. `As-Left-1` takes a promotion step on the left-hand term, and `Ms-Equ` makes an
equivalence step a promotion step, so the same chain puts `a` below `c`.

```agda
chain⇒≥ : ∀ {Γ s a c} → Γ ∣ s ⊢ a ⟶ᵉ* c → Γ ∣ s ⊢ c ≤ a
chain⇒≥ (ε pv)  = As-Refl pv
chain⇒≥ (d ◅ p) = As-Right (chain⇒≥ p) d

chain⇒≤ : ∀ {Γ s a c} → Γ ∣ s ⊢ a ⟶ᵉ* c → Γ ∣ s ⊢ a ≤ c
chain⇒≤ (ε pv)  = As-Refl pv
chain⇒≤ (d ◅ p) = As-Left-1 (Ms-Equ (⟶ᵉ-prevalid d) d) (chain⇒≤ p)

↦⇒≥ : ∀ {Γ s t t'} → LC t → fv t ⊑ dom Γ → Γ ∣ s prevalid → t ↦ t' → Γ ∣ s ⊢ t' ≤ t
↦⇒≥ lt f pv st = chain⇒≥ (↦⇒⟶ᵉ* lt f pv st)

↦⇒≤ : ∀ {Γ s t t'} → LC t → fv t ⊑ dom Γ → Γ ∣ s prevalid → t ↦ t' → Γ ∣ s ⊢ t ≤ t'
↦⇒≤ lt f pv st = chain⇒≤ (↦⇒⟶ᵉ* lt f pv st)
```

## What this establishes

`↦⇒⟶ᵉ*`, with nothing assumed beyond local closure, scoping and prevalidity: an evaluation step
is a chain of equivalence steps at every prevalid configuration `Γ ∣ s`, not only at the empty
stack and not only for well-formed terms. The β case is two steps, as in `MPSS/Prop17Chain`;
well-formedness there served only to keep the intermediate terms well-formed. `↦⇒≥` and `↦⇒≤`
are the consequences for the machine relation: across an evaluation step the two terms are
below each other at the configuration, by `As-Right` and by `As-Left-1` with `Ms-Equ`.
