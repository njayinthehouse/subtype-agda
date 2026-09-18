# MPSS: Proposition 17, repaired — an evaluation step is a chain of equivalence steps through well-formed terms

The printed Proposition 17 says an evaluation step `u ↦ v` is a single equivalence step
`Γ;s ⊢ u ⟶≡ v`. It is false (`MPSS/BetaScope`, `MPSS/BetaScopeWf`), and so is the assumed
repair with a scoping premise (`MPSS/Prop17Refuted`): `Me-Bet` reduces the redex body with its
parameter unbound, so a body that passes the parameter as an operand has no derivation at all.

What is true, and what every consumer needs, is the chain form with well-formedness carried
along: if `u` and `v` are well-formed and `u ↦ v`, then `u` reaches `v` by equivalence steps at
`Γ;nil` **every one of whose terms is well-formed**. The β case takes two steps — bind the
parameter to the operand by `Me-FOp` and unfold it, then contract the now closed body by
`Me-Bet` — and the intermediate `(λx≤t. u[x\v]) v` is well-formed because its body is the
contractum. The congruence cases lift the chain through `Me-Fun`, `Me-FOp`-free binders and
`Me-App`, showing each intermediate well-formed by `push≡*wf` (applications) and Lemma 23
(annotations); under a binder the chain at one fresh name is closed and renamed
(`MPSS/WfRename`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Prop17Chain where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (Dec; yes; no)

open import MPSS.WellFormed
open import MPSS.Narrow using (wf-fv)
open import MPSS.Static using (Lem-15; Lem-16; ⊑*wf⇒wfʳ)
open import MPSS.Unconditional using (Lem-10)
open import MPSS.Preservation using (push≡*wf)
open import MPSS.Lemma23 using (Lem-23-holds)
open import MPSS.Weakening using (wf-weaken)
open import MPSS.StackPush
  using (⟶ᵉ-refl; pushᵉ; prevalid-cons; fv-lam-ann; fv-lam-body; fv-open-cons; fv-app-arg; fv-app-op)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Wrap using (wrapᵉ-fun)
open import MPSS.WfRename using (wf-rename-head)
open import PSS.Syntax
  using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; ∉-tail; closeRec; openRec;
         subst-intro; subst-open; subst-fvar-≡; subst-fvar-≢; open-lc-id)
open import PSS.Close using (open-close; close-open; fv-close)
```

## Chains of equivalence steps through well-formed terms

At the empty stack; every term on the chain, including the last, is well-formed.

```agda
infix 3 _⊢_⟶ᵉ*wf_
data _⊢_⟶ᵉ*wf_ : Ctx → Tm → Tm → Set where
  εʷ   : ∀ {Γ t} → Γ ⊢ t wf → Γ ⊢ t ⟶ᵉ*wf t
  step : ∀ {Γ a b c} → Γ ∣ [] ⊢ a ⟶ᵉ b → Γ ⊢ b wf → Γ ⊢ b ⟶ᵉ*wf c → Γ ⊢ a ⟶ᵉ*wf c

⟶ᵉ*wf⇒wfʳ : ∀ {Γ a c} → Γ ⊢ a ⟶ᵉ*wf c → Γ ⊢ c wf
⟶ᵉ*wf⇒wfʳ (εʷ w)       = w
⟶ᵉ*wf⇒wfʳ (step _ _ p) = ⟶ᵉ*wf⇒wfʳ p
```

What the consumers do with such a chain: push a well-subtyping derivation forward along it
(Proposition 27, Theorem 5), and narrow a body's well-formedness along it (Lemma 6).

```agda
push-chain : ∀ {Γ a c v m} → Γ ⊢ a ⊑*wf[ m ] v → Γ ⊢ a ⟶ᵉ*wf c → Γ ⊢ c ⊑*wf[ m ] v
push-chain d (εʷ _)        = d
push-chain d (step e wb p) = push-chain (push≡*wf e d wb) p

narrow-chain : ∀ {Γ x t t' u}
             → ((x , sub , t) ∷ Γ) ⊢ u wf → Γ ⊢ t wf → Γ ⊢ t ⟶ᵉ*wf t'
             → ((x , sub , t') ∷ Γ) ⊢ u wf
narrow-chain w wt (εʷ _)         = w
narrow-chain w wt (step e wt₂ p) = narrow-chain (Lem-23-holds [] w wt e wt₂) wt₂ p
```

## Unfolding a definition everywhere in a term

With `x ≡ v` in the context, a locally closed and scoped term reduces in one step to itself
with `v` substituted for `x`, at any stack: `Me-Pro` at each occurrence, reflexivity elsewhere.

```agda
⊑-there : ∀ {N x} {xs : List Name} → xs ⊑ N → xs ⊑ (x ∷ N)
⊑-there f h = there (f h)

unfold : ∀ {Γ s x v w}
       → Γ ∣ s prevalid → x ≐ v ∈ Γ → LC v → fv v ⊑ dom Γ
       → LC w → fv w ⊑ dom Γ
       → Γ ∣ s ⊢ w ⟶ᵉ (w [ x := v ])
unfold {Γ} {s} {x} {v} pv mem lv fvv (lc-fvar {z}) f = go (x ≟ z)
  where
    -- decided as a value, not by `with`: the substitution's own case split on
    -- the same comparison would otherwise be abstracted out of the goal
    go : Dec (x ≡ z) → Γ ∣ s ⊢ fvar z ⟶ᵉ ((fvar z) [ x := v ])
    go (yes p) = subst (λ q → Γ ∣ s ⊢ fvar z ⟶ᵉ q)
                       (sym (subst (λ y → (fvar y) [ x := v ] ≡ v) p (subst-fvar-≡ v)))
                       (subst (λ y → Γ ∣ s ⊢ fvar y ⟶ᵉ v) p (Me-Pro pv mem (⟶ᵉ-refl pv lv fvv)))
    go (no np) = subst (λ q → Γ ∣ s ⊢ fvar z ⟶ᵉ q) (sym (subst-fvar-≢ v np)) (Me-Var pv)
unfold pv mem lv fvv lc-Top f = Me-Top pv
unfold pv mem lv fvv (lc-app {u} {a} lu la) f =
  Me-App (unfold (Pv-Sta pv la (fv-app-arg {u} {a} f)) mem lv fvv lu (fv-app-op {u} {a} f))
         (unfold (prevalid-nil pv) mem lv fvv la (fv-app-arg {u} {a} f))
unfold {Γ} {[]} {x} {v} pv mem lv fvv (lc-lam {t} {b} L lt F) f =
  Me-Fun (x ∷ L ++ dom Γ) (unfold pv mem lv fvv lt (fv-lam-ann {t} {b} f)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ dom Γ)
         → ((z , sub , t) ∷ Γ) ∣ [] ⊢ (b ^ fvar z) ⟶ᵉ ((b [ x := v ]) ^ fvar z)
    body {z} z∉ =
      subst (λ q → ((z , sub , t) ∷ Γ) ∣ [] ⊢ (b ^ fvar z) ⟶ᵉ q) eq
            (unfold (prevalid-cons pv (∉-++ʳ L (∉-tail z∉)) lt (fv-lam-ann {t} {b} f))
                    (there mem) lv (⊑-there fvv)
                    (F (∉-++ˡ (∉-tail z∉))) (fv-open-cons {b} z (fv-lam-body {t} {b} f)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq : (b ^ fvar z) [ x := v ] ≡ (b [ x := v ]) ^ fvar z
        eq = trans (subst-open lv 0 (fvar z) b x)
                   (cong (λ q → openRec 0 q (b [ x := v ])) (subst-fvar-≢ v x≢z))
unfold {Γ} {α ∷ s} {x} {v} pv mem lv fvv (lc-lam {t} {b} L lt F) f =
  Me-FOp (x ∷ L ++ dom Γ) (unfold (prevalid-nil pv) mem lv fvv lt (fv-lam-ann {t} {b} f)) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ dom Γ)
         → ((z , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar z) ⟶ᵉ ((b [ x := v ]) ^ fvar z)
    body {z} z∉ =
      subst (λ q → ((z , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar z) ⟶ᵉ q) eq
            (unfold (prevalid-cons (prevalid-pop pv) (∉-++ʳ L (∉-tail z∉))
                                   (prevalid-head-lc pv) (prevalid-head-fv pv))
                    (there mem) lv (⊑-there fvv)
                    (F (∉-++ˡ (∉-tail z∉))) (fv-open-cons {b} z (fv-lam-body {t} {b} f)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq : (b ^ fvar z) [ x := v ] ≡ (b [ x := v ]) ^ fvar z
        eq = trans (subst-open lv 0 (fvar z) b x)
                   (cong (λ q → openRec 0 q (b [ x := v ])) (subst-fvar-≢ v x≢z))
```

## Lifting a chain through the congruences

**The annotation of an abstraction.** Each step is `Me-Fun` with a reflexive body; the body's
well-formedness follows the annotation along by Lemma 23.

```agda
fun-ann-chain : ∀ {Γ t t' u} (L : List Name)
              → (∀ {z} → z ∉ L → ((z , sub , t) ∷ Γ) ⊢ (u ^ fvar z) wf)
              → Γ ⊢ t wf → Γ ⊢ t ⟶ᵉ*wf t'
              → Γ ⊢ lam t u ⟶ᵉ*wf lam t' u
fun-ann-chain L F wt (εʷ wt') = εʷ (Wf-Fun L F wt')
fun-ann-chain {Γ} {t} {t'} {u} L F wt (step {b = t₂} e wt₂ p) =
  step (Me-Fun (L ++ dom Γ) e body) (Wf-Fun L F₂ wt₂) (fun-ann-chain L F₂ wt₂ p)
  where
    F₂ : ∀ {z} → z ∉ L → ((z , sub , t₂) ∷ Γ) ⊢ (u ^ fvar z) wf
    F₂ z∉ = Lem-23-holds [] (F z∉) wt e wt₂
    body : ∀ {z} → z ∉ (L ++ dom Γ)
         → ((z , sub , t) ∷ Γ) ∣ [] ⊢ (u ^ fvar z) ⟶ᵉ (u ^ fvar z)
    body {z} z∉ = ⟶ᵉ-refl (Pv-Nil (wf⇒prevalid w)) (wf⇒lc w) (wf-fv w)
      where w = F (∉-++ˡ z∉)
```

**The body of an abstraction.** The chain at one fresh name is closed over that name; each step
is wrapped by `Me-Fun` (`MPSS/Wrap`), and each intermediate abstraction is well-formed because
its body at any fresh name is the renaming of the body at the chosen one.

```agda
wrap-wf : ∀ {Γ w a} x → x ∉ dom Γ → LC a
        → ((x , sub , w) ∷ Γ) ⊢ a wf → Γ ⊢ w wf
        → Γ ⊢ lam w (closeRec 0 x a) wf
wrap-wf {Γ} {w} {a} x x∉ la wa ww = Wf-Fun (x ∷ dom Γ) fam ww
  where
    fam : ∀ {y} → y ∉ (x ∷ dom Γ) → ((y , sub , w) ∷ Γ) ⊢ ((closeRec 0 x a) ^ fvar y) wf
    fam {y} y∉ = subst (λ q → ((y , sub , w) ∷ Γ) ⊢ q wf) (sym eq) (wf-rename-head y∉ wa)
      where
        eq : (closeRec 0 x a) ^ fvar y ≡ a [ x := fvar y ]
        eq = trans (subst-intro {closeRec 0 x a} lc-fvar x (fv-close 0 x a))
                   (cong (_[ x := fvar y ]) (open-close la 0 x))

fun-body-chain : ∀ {Γ w a c} x → x ∉ dom Γ → LC a → Γ ⊢ w wf
               → ((x , sub , w) ∷ Γ) ⊢ a ⟶ᵉ*wf c
               → Γ ⊢ lam w (closeRec 0 x a) ⟶ᵉ*wf lam w (closeRec 0 x c)
fun-body-chain x x∉ la ww (εʷ wc) = εʷ (wrap-wf x x∉ la wc ww)
fun-body-chain x x∉ la ww (step e wb p) =
  step (wrapᵉ-fun x x∉ la lb e) (wrap-wf x x∉ lb wb ww) (fun-body-chain x x∉ lb ww p)
  where lb = ⟶ᵉ-lc la e
```

**Applications.** The operator's chain is pushed to the stack holding the operand; the
intermediate applications are well-formed because the operator's well-subtyping derivation is
pushed along with it.

```agda
app-l-chain : ∀ {Γ u u' v t}
            → Γ ⊢ u ⊑*wf[ sub-m ] lam t Top → Γ ⊢ v ⊑*wf[ sub-m ] t
            → Γ ⊢ u ⟶ᵉ*wf u' → Γ ⊢ app u v ⟶ᵉ*wf app u' v
app-l-chain d₁ d₂ (εʷ _) = εʷ (Wf-App d₁ d₂)
app-l-chain d₁ d₂ (step e wb p) =
  step (Me-App (pushᵉ e (Pv-Sta (Pv-Nil pvΓ) lv fvv)) (⟶ᵉ-refl (Pv-Nil pvΓ) lv fvv))
       (Wf-App d₁' d₂) (app-l-chain d₁' d₂ p)
  where
    wv  = ⊑*wf⇒wfˡ d₂
    pvΓ = wf⇒prevalid wv
    lv  = wf⇒lc wv
    fvv = wf-fv wv
    d₁' = push≡*wf e d₁ wb

app-r-chain : ∀ {Γ u v v' t}
            → Γ ⊢ u ⊑*wf[ sub-m ] lam t Top → Γ ⊢ v ⊑*wf[ sub-m ] t
            → Γ ⊢ v ⟶ᵉ*wf v' → Γ ⊢ app u v ⟶ᵉ*wf app u v'
app-r-chain d₁ d₂ (εʷ _) = εʷ (Wf-App d₁ d₂)
app-r-chain d₁ d₂ (step e wb p) =
  step (Me-App (⟶ᵉ-refl (Pv-Sta (Pv-Nil pvΓ) lv fvv) lu fvu) e)
       (Wf-App d₁ d₂') (app-r-chain d₁ d₂' p)
  where
    wu  = ⊑*wf⇒wfˡ d₁
    wv  = ⊑*wf⇒wfˡ d₂
    pvΓ = wf⇒prevalid wv
    lu  = wf⇒lc wu
    fvu = wf-fv wu
    lv  = wf⇒lc wv
    fvv = wf-fv wv
    d₂' = push≡*wf e d₂ wb
```

## The proposition

```agda
Prop-17ʷ : ∀ {Γ u v} → Γ ⊢ u wf → u ↦ v → Γ ⊢ v wf → Γ ⊢ u ⟶ᵉ*wf v
```

**β.** Two steps. First `Me-App` over `Me-FOp`: the parameter is bound to the operand and
unfolded throughout the body, so the abstraction's body becomes the contractum. The operand
is below the annotation by inversion, symmetry and the cast to subtyping — exactly as in Lemma
6's β case — which, with the contractum well-formed, makes the intermediate application
well-formed. Then `Me-Bet` on a body in which the parameter no longer occurs.

```agda
Prop-17ʷ {Γ} (Wf-App {u = lam t b} {v = c} d₁ d₂) (E-App _ lc) wv
  with ⊑*wf⇒wfˡ d₁ | ⊑*wf⇒wfʳ d₁
... | Wf-Fun L F wt | Wf-Fun _ _ wz = step s₁ w₁ (step s₂ wv (εʷ wv))
  where
    pvΓ = wf⇒prevalid wt
    lt  = wf⇒lc wt
    fvt = wf-fv wt
    fvc = wf-fv (⊑*wf⇒wfˡ d₂)
    lb  = wf⇒lc wv
    fvb = wf-fv wv

    c≤t : Γ ⊢ c ⊑*wf[ sub-m ] t
    c≤t = Ws-Trs d₂ wz (Ws-Sub wz (Lem-16 (Lem-15 (Lem-10 d₁))) wt)

    A'-wf : Γ ⊢ lam t (b ^ c) wf
    A'-wf = Wf-Fun (dom Γ) fam wt
      where
        fam : ∀ {z} → z ∉ dom Γ → ((z , sub , t) ∷ Γ) ⊢ ((b ^ c) ^ fvar z) wf
        fam {z} z∉ = subst (λ q → ((z , sub , t) ∷ Γ) ⊢ q wf) (open-lc-id lb 0 (fvar z))
                           (wf-weaken [] ((z , sub , t) ∷ []) (Pv-Ctx pvΓ z∉ lt fvt) wv)

    lamTop-wf : Γ ⊢ lam t Top wf
    lamTop-wf = Wf-Fun (dom Γ) (λ {z} z∉ → Wf-Top (Pv-Ctx pvΓ z∉ lt fvt)) wt

    A'≤ : Γ ⊢ lam t (b ^ c) ⊑*wf[ sub-m ] lam t Top
    A'≤ = Ws-Sub A'-wf (Ws-Lf2 A'-wf pro lamTop-wf (Ws-Rfl pvΓ)) lamTop-wf
      where
        pro : Γ ∣ [] ⊢ lam t (b ^ c) ⟶ˢ lam t Top
        pro = Ms-Fun {u' = Top} (dom Γ) (λ {z} z∉ → Ms-Top (Pv-Nil (Pv-Ctx pvΓ z∉ lt fvt)))

    w₁ : Γ ⊢ app (lam t (b ^ c)) c wf
    w₁ = Wf-App A'≤ c≤t

    s₁ : Γ ∣ [] ⊢ app (lam t b) c ⟶ᵉ app (lam t (b ^ c)) c
    s₁ = Me-App (Me-FOp {u = b} {u' = b ^ c} (L ++ fv b ++ dom Γ) (⟶ᵉ-refl (Pv-Nil pvΓ) lt fvt) body)
                (⟶ᵉ-refl (Pv-Nil pvΓ) lc fvc)
      where
        body : ∀ {x} → x ∉ (L ++ fv b ++ dom Γ)
             → ((x , eqv , c) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ ((b ^ c) ^ fvar x)
        body {x} x∉ =
          subst (λ q → ((x , eqv , c) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ q) eq
                (unfold (Pv-Nil (Pv-EqA pvΓ (∉-++ʳ (fv b) (∉-++ʳ L x∉)) lc fvc))
                        (here refl) lc (⊑-there fvc) (wf⇒lc wx) (wf-fv wx))
          where
            wx = F (∉-++ˡ x∉)
            eq : (b ^ fvar x) [ x := c ] ≡ (b ^ c) ^ fvar x
            eq = trans (sym (subst-intro {b} lc x (∉-++ˡ (∉-++ʳ L x∉)))) (open-lc-id lb 0 (fvar x))

    s₂ : Γ ∣ [] ⊢ app (lam t (b ^ c)) c ⟶ᵉ (b ^ c)
    s₂ = subst (λ q → Γ ∣ [] ⊢ app (lam t (b ^ c)) c ⟶ᵉ q) (sym (open-lc-id lb 0 c))
               (Me-Bet {u = b ^ c} {u' = b ^ c} {v = c} {v' = c} (dom Γ) body₂ (⟶ᵉ-refl (Pv-Nil pvΓ) lc fvc))
      where
        body₂ : ∀ {x} → x ∉ dom Γ → Γ ∣ [] ⊢ ((b ^ c) ^ fvar x) ⟶ᵉ ((b ^ c) ^ fvar x)
        body₂ {x} _ = subst (λ q → Γ ∣ [] ⊢ q ⟶ᵉ q) (open-lc-id lb 0 (fvar x))
                            (⟶ᵉ-refl (Pv-Nil pvΓ) lb fvb)
```

**The congruences.**

```agda
Prop-17ʷ (Wf-Fun L F wt) (E-Lam-l st) (Wf-Fun _ _ wt') =
  fun-ann-chain L F wt (Prop-17ʷ wt st wt')

Prop-17ʷ {Γ} (Wf-Fun {t = t} {u = b} L F wt) (E-Lam-r L' F') (Wf-Fun {u = b'} L₂ F₂ _) =
  subst₂ (λ p q → Γ ⊢ lam t p ⟶ᵉ*wf lam t q)
         (close-open 0 x b x∉b) (close-open 0 x b' x∉b')
         (fun-body-chain x x∉Γ (wf⇒lc wx) wt (Prop-17ʷ wx (F' x∉L') (F₂ x∉L₂)))
  where
    A    = L ++ L' ++ L₂ ++ dom Γ ++ fv b ++ fv b'
    x    = fresh A
    x∉A  = fresh-∉ A
    x∉L  = ∉-++ˡ x∉A
    x∉L' = ∉-++ˡ (∉-++ʳ L x∉A)
    x∉L₂ = ∉-++ˡ (∉-++ʳ L' (∉-++ʳ L x∉A))
    x∉Γ  = ∉-++ˡ (∉-++ʳ L₂ (∉-++ʳ L' (∉-++ʳ L x∉A)))
    x∉b  = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₂ (∉-++ʳ L' (∉-++ʳ L x∉A))))
    x∉b' = ∉-++ʳ (fv b) (∉-++ʳ (dom Γ) (∉-++ʳ L₂ (∉-++ʳ L' (∉-++ʳ L x∉A))))
    wx   = F x∉L

Prop-17ʷ (Wf-App d₁ d₂) (E-App-l st) (Wf-App d₁' _) =
  app-l-chain d₁ d₂ (Prop-17ʷ (⊑*wf⇒wfˡ d₁) st (⊑*wf⇒wfˡ d₁'))

Prop-17ʷ (Wf-App d₁ d₂) (E-App-r st) (Wf-App _ d₂') =
  app-r-chain d₁ d₂ (Prop-17ʷ (⊑*wf⇒wfˡ d₂) st (⊑*wf⇒wfˡ d₂'))
```

## What this establishes

`Prop-17ʷ`, with nothing assumed: on well-formed terms, an evaluation step is a chain of
equivalence steps at the empty stack through well-formed terms. It is the statement Lemma 6,
Proposition 27 and Theorem 5 consume in `MPSS/Preservation17`, in place of the refuted
`Prop-17ʳ`.
