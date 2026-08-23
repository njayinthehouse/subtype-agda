# System λ⊲: promotion under substitution (Lemmas B.6 and B.9)

Theorem 4.5's `Cr-Beta` case contracts a redex on the equivalence side while the promotion side
has pushed the operand into the context. Reconciling them needs **Lemma B.9**: promotion is
stable under substituting a variable by its bound, with the substitution applied to the context
and the stack as well.

That needs **Lemma B.6** — substitution preserves prevalidity — since three of the six promotion
rules carry a prevalidity premise.

Definition B.2 gives substitution on extended contexts. Here the context is a list of
`(name, bound)` pairs, most recent first, so the paper's `Γ, x ≤ v, Γ′` is `Δ ++ (x , v) ∷ Γ`
with `Δ` the *later* bindings — the ones substitution touches.

```agda
{-# OPTIONS --safe #-}

module PSS.Promotion where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Equivalence
```

## Substitution on contexts and stacks

```agda
substCtx : Name → Tm → Ctx → Ctx
substCtx x v = map (λ p → (proj₁ p , (proj₂ p) [ x := v ]))

substStack : Name → Tm → Stack → Stack
substStack x v = map (_[ x := v ])

dom-substCtx : ∀ x v Δ → dom (substCtx x v Δ) ≡ dom Δ
dom-substCtx x v []            = refl
dom-substCtx x v ((y , t) ∷ Δ) = cong (y ∷_) (dom-substCtx x v Δ)

dom-++ : ∀ (Δ Γ : Ctx) → dom (Δ ++ Γ) ≡ dom Δ ++ dom Γ
dom-++ Δ Γ = map-++ proj₁ Δ Γ

∈-substCtx : ∀ x v {y t} (Δ : Ctx) → (y , t) ∈ Δ → (y , t [ x := v ]) ∈ substCtx x v Δ
∈-substCtx x v ((z , u) ∷ Δ) (here refl) = here refl
∈-substCtx x v ((z , u) ∷ Δ) (there m)   = there (∈-substCtx x v Δ m)
```

## Where substitution can put a free variable

```agda
fv-subst : ∀ x v t {y} → y ∈ fv (t [ x := v ])
         → (y ∈ fv t × y ≢ x) ⊎ (y ∈ fv v)
fv-subst x v (bvar i) ()
fv-subst x v (fvar z) {y} y∈ = go (x ≟ z)
  where
    go : Dec (x ≡ z) → (y ∈ fv (fvar z) × y ≢ x) ⊎ (y ∈ fv v)
    go (yes refl) = inj₂ (subst (λ w → y ∈ fv w) (subst-fvar-≡ {x} v) y∈)
    go (no  x≢z)  = inj₁ (h , λ p → x≢z (trans (sym p) (mem h)))
      where
        h : y ∈ fv (fvar z)
        h = subst (λ w → y ∈ fv w) (subst-fvar-≢ {x} {z} v x≢z) y∈
        mem : y ∈ fv (fvar z) → y ≡ z
        mem (here p) = p
fv-subst x v Top ()
fv-subst x v (lam t b) {y} y∈ with ∈-++⁻ (fv (t [ x := v ])) y∈
... | inj₁ p with fv-subst x v t p
...   | inj₁ (q , n) = inj₁ (∈-++⁺ˡ q , n)
...   | inj₂ q       = inj₂ q
fv-subst x v (lam t b) {y} y∈ | inj₂ p with fv-subst x v b p
...   | inj₁ (q , n) = inj₁ (∈-++⁺ʳ (fv t) q , n)
...   | inj₂ q       = inj₂ q
fv-subst x v (app f a) {y} y∈ with ∈-++⁻ (fv (f [ x := v ])) y∈
... | inj₁ p with fv-subst x v f p
...   | inj₁ (q , n) = inj₁ (∈-++⁺ˡ q , n)
...   | inj₂ q       = inj₂ q
fv-subst x v (app f a) {y} y∈ | inj₂ p with fv-subst x v a p
...   | inj₁ (q , n) = inj₁ (∈-++⁺ʳ (fv f) q , n)
...   | inj₂ q       = inj₂ q
```

Re-scoping: a term scoped over `Δ ++ (x ≤ v) ∷ Γ` becomes, after substituting `x := v`, scoped
over `substCtx x v Δ ++ Γ`.

```agda
∈-dom-split : ∀ (Δ : Ctx) {Γ x v y} → y ∈ dom (Δ ++ (x , v) ∷ Γ)
            → (y ∈ dom Δ) ⊎ (y ∈ x ∷ dom Γ)
∈-dom-split Δ {Γ} {x} {v} {y} h =
  ∈-++⁻ (dom Δ) (subst (y ∈_) (dom-++ Δ ((x , v) ∷ Γ)) h)

∈-dom-join : ∀ x v (Δ : Ctx) {Γ y} → (y ∈ dom Δ) ⊎ (y ∈ dom Γ)
           → y ∈ dom (substCtx x v Δ ++ Γ)
∈-dom-join x v Δ {Γ} {y} (inj₁ h) =
  subst (y ∈_) (sym (dom-++ (substCtx x v Δ) Γ))
        (∈-++⁺ˡ (subst (y ∈_) (sym (dom-substCtx x v Δ)) h))
∈-dom-join x v Δ {Γ} {y} (inj₂ h) =
  subst (y ∈_) (sym (dom-++ (substCtx x v Δ) Γ))
        (∈-++⁺ʳ (dom (substCtx x v Δ)) h)

⊑-subst : ∀ {Γ v} x (Δ : Ctx) {t}
        → fv v ⊑ dom Γ
        → fv t ⊑ dom (Δ ++ (x , v) ∷ Γ)
        → fv (t [ x := v ]) ⊑ dom (substCtx x v Δ ++ Γ)
⊑-subst {Γ} {v} x Δ {t} fvv fvt {y} y∈ with fv-subst x v t y∈
... | inj₂ q            = ∈-dom-join x v Δ (inj₂ (fvv q))
... | inj₁ (q , y≢x) with ∈-dom-split Δ (fvt q)
...   | inj₁ r          = ∈-dom-join x v Δ (inj₁ r)
...   | inj₂ (here p)   = ⊥-elim (y≢x p)
...   | inj₂ (there p)  = ∈-dom-join x v Δ (inj₂ p)
```

## Structural facts about prevalidity

Three facts the `Srs-Prom` case of B.9 needs: the stack can be dropped, a prefix of the context
can be dropped, and every bound in a prevalid context is scoped by that context.

```agda
prevalid-nil : ∀ {Γ s} → Γ ∣ s prevalid → Γ ∣ [] prevalid
prevalid-nil P-Ctx1            = P-Ctx1
prevalid-nil p@(P-Ctx2 _ _ _)  = p
prevalid-nil (P-Ctx3 p _)      = prevalid-nil p

prevalid-suffix : ∀ (Δ : Ctx) {Γ} → (Δ ++ Γ) ∣ [] prevalid → Γ ∣ [] prevalid
prevalid-suffix []            p              = p
prevalid-suffix ((y , t) ∷ Δ) (P-Ctx2 p _ _) = prevalid-suffix Δ p

prevalid-entry-fv : ∀ {Γ y t} → Γ ∣ [] prevalid → (y , t) ∈ Γ → fv t ⊑ dom Γ
prevalid-entry-fv (P-Ctx2 p _ fvu) (here refl) = λ h → there (fvu h)
prevalid-entry-fv (P-Ctx2 p _ _)   (there m)   = λ h → there (prevalid-entry-fv p m h)
```

The substituted variable is not bound anywhere in the later part of the context, nor free in
any bound of the earlier part.

```agda
x∉-domΔ : ∀ (Δ : Ctx) {Γ x v s} → (Δ ++ (x , v) ∷ Γ) ∣ s prevalid → x ∉ dom Δ
x∉-domΔ []            p ()
x∉-domΔ ((y , t) ∷ Δ) {Γ} {x} {v} p h = go (prevalid-nil p) h
  where
    x∈tail : x ∈ dom (Δ ++ (x , v) ∷ Γ)
    x∈tail = subst (x ∈_) (sym (dom-++ Δ ((x , v) ∷ Γ)))
                   (∈-++⁺ʳ (dom Δ) (here refl))

    go : ((y , t) ∷ (Δ ++ (x , v) ∷ Γ)) ∣ [] prevalid → x ∈ (y ∷ dom Δ) → ⊥
    go (P-Ctx2 q y∉ _) (here p')  = y∉ (subst (_∈ dom (Δ ++ (x , v) ∷ Γ)) p' x∈tail)
    go (P-Ctx2 q y∉ _) (there p') = x∉-domΔ Δ q p'

x∉-domΓ : ∀ (Δ : Ctx) {Γ x v s} → (Δ ++ (x , v) ∷ Γ) ∣ s prevalid → x ∉ dom Γ
x∉-domΓ Δ p = go (prevalid-suffix Δ (prevalid-nil p))
  where
    go : ∀ {Γ x v} → ((x , v) ∷ Γ) ∣ [] prevalid → x ∉ dom Γ
    go (P-Ctx2 _ x∉ _) = x∉

x∉-boundΓ : ∀ (Δ : Ctx) {Γ x v s y t} → (Δ ++ (x , v) ∷ Γ) ∣ s prevalid
          → (y , t) ∈ Γ → x ∉ fv t
x∉-boundΓ Δ {Γ} p m h =
  x∉-domΓ Δ p (prevalid-entry-fv (prevalid-suffix ((_ , _) ∷ []) suffix) m h)
  where
    suffix : ((_ , _) ∷ Γ) ∣ [] prevalid
    suffix = prevalid-suffix Δ (prevalid-nil p)
```

## Lemma B.6 — substitution preserves prevalidity

```agda
prevalid-subst : ∀ {Γ s v} x (Δ : Ctx)
               → fv v ⊑ dom Γ
               → (Δ ++ (x , v) ∷ Γ) ∣ s prevalid
               → (substCtx x v Δ ++ Γ) ∣ substStack x v s prevalid
prevalid-subst x []            fvv (P-Ctx2 p _ _)     = p
prevalid-subst {Γ} {v = v} x ((y , t) ∷ Δ) fvv (P-Ctx2 p y∉ fvt) =
  P-Ctx2 (prevalid-subst x Δ fvv p) y∉' (⊑-subst x Δ {t} fvv fvt)
  where
    y∉' : y ∉ dom (substCtx x v Δ ++ Γ)
    y∉' h with ∈-++⁻ (dom (substCtx x v Δ))
                     (subst (y ∈_) (dom-++ (substCtx x v Δ) Γ) h)
    ... | inj₁ q = y∉ (subst (y ∈_) (sym (dom-++ Δ ((x , v) ∷ Γ)))
                             (∈-++⁺ˡ (subst (y ∈_) (dom-substCtx x v Δ) q)))
    ... | inj₂ q = y∉ (subst (y ∈_) (sym (dom-++ Δ ((x , v) ∷ Γ)))
                             (∈-++⁺ʳ (dom Δ) (there q)))
prevalid-subst x Δ fvv (P-Ctx3 {α = α} p fvα) =
  P-Ctx3 (prevalid-subst x Δ fvv p) (⊑-subst x Δ {α} fvv fvα)
```

## Lemma B.9 — promotion under substitution

By induction on the promotion derivation.

`Srs-Prom` is the case with content. Promoting the substituted variable itself yields
`v ⟶≤ v`, discharged by reflexivity of `⟶≡` (Lemma 2.2) through `Srs-Eq` — this is what the
paper's proof means by "holds by reflexivity". Promoting any *other* variable leaves its bound
untouched, because a bound recorded in `Γ` cannot mention `x`, which is introduced later.

`Srs-Eq` goes through Lemma B.10, which is `⟶≡-subst`.

```agda
⟶≤-subst : ∀ {Γ s u u' v} x (Δ : Ctx)
         → LC v
         → x ∉ fv v
         → fv v ⊑ dom Γ
         → (Δ ++ (x , v) ∷ Γ) ∣ s ⊢ u ⟶≤ u'
         → (substCtx x v Δ ++ Γ) ∣ substStack x v s ⊢ (u [ x := v ]) ⟶≤ (u' [ x := v ])

⟶≤-subst {Γ} {s} {v = v} x Δ lv x∉v fvv (Srs-Prom {_} {_} {y} {t} pv mem)
  with ∈-++⁻ Δ mem
... | inj₁ m = promote-Δ
  where
    y≢x : x ≢ y
    y≢x p = x∉-domΔ Δ pv (subst (_∈ dom Δ) (sym p) (∈-dom-of m))
      where
        ∈-dom-of : ∀ {Δ' y t} → (y , t) ∈ Δ' → y ∈ dom Δ'
        ∈-dom-of (here refl) = here refl
        ∈-dom-of (there q)   = there (∈-dom-of q)

    promote-Δ : (substCtx x v Δ ++ Γ) ∣ substStack x v s
                  ⊢ ((fvar y) [ x := v ]) ⟶≤ (t [ x := v ])
    promote-Δ rewrite subst-fvar-≢ {x} {y} v y≢x =
      Srs-Prom (prevalid-subst x Δ fvv pv)
               (∈-++⁺ˡ (∈-substCtx x v Δ m))

⟶≤-subst {Γ} {s} {v = v} x Δ lv x∉v fvv (Srs-Prom {_} {_} {y} {t} pv mem)
    | inj₂ (here refl) = promote-self
  where
    promote-self : (substCtx x v Δ ++ Γ) ∣ substStack x v s
                     ⊢ ((fvar x) [ x := v ]) ⟶≤ (v [ x := v ])
    promote-self rewrite subst-fvar-≡ {x} v | subst-fresh {v} x v x∉v =
      Srs-Eq (prevalid-subst x Δ fvv pv) (⟶≡-refl lv)

⟶≤-subst {Γ} {s} {v = v} x Δ lv x∉v fvv (Srs-Prom {_} {_} {y} {t} pv mem)
    | inj₂ (there m) = promote-Γ
  where
    y≢x : x ≢ y
    y≢x p = x∉-domΓ Δ pv (subst (_∈ dom Γ) (sym p) (∈-dom-of m))
      where
        ∈-dom-of : ∀ {Γ' y t} → (y , t) ∈ Γ' → y ∈ dom Γ'
        ∈-dom-of (here refl) = here refl
        ∈-dom-of (there q)   = there (∈-dom-of q)

    promote-Γ : (substCtx x v Δ ++ Γ) ∣ substStack x v s
                  ⊢ ((fvar y) [ x := v ]) ⟶≤ (t [ x := v ])
    promote-Γ rewrite subst-fvar-≢ {x} {y} v y≢x
                    | subst-fresh {t} x v (x∉-boundΓ Δ pv m) =
      Srs-Prom (prevalid-subst x Δ fvv pv)
               (∈-++⁺ʳ (substCtx x v Δ) m)

⟶≤-subst x Δ lv x∉v fvv (Srs-Top pv) = Srs-Top (prevalid-subst x Δ fvv pv)

⟶≤-subst x Δ lv x∉v fvv (Srs-Eq pv e) =
  Srs-Eq (prevalid-subst x Δ fvv pv) (⟶≡-subst x lv lv e (⟶≡-refl lv))

⟶≤-subst x Δ lv x∉v fvv (Srs-App d) = Srs-App (⟶≤-subst x Δ lv x∉v fvv d)

⟶≤-subst {Γ} {v = v} x Δ lv x∉v fvv (Srs-Fun {_} {t} {u} {u'} L F) =
  Srs-Fun (x ∷ L ++ fv v) body
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v)
         → ((y , t [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ []
             ⊢ ((u [ x := v ]) ^ fvar y) ⟶≤ ((u' [ x := v ]) ^ fvar y)
    body {y} y∉ = transport (⟶≤-subst x ((y , t) ∷ Δ) lv x∉v fvv (F (∉-++ˡ (∉-tail y∉))))
      where
        x≢y : x ≢ y
        x≢y p = y∉ (here (sym p))

        eq : ∀ w → ((w ^ fvar y) [ x := v ]) ≡ ((w [ x := v ]) ^ fvar y)
        eq w = trans (subst-open lv 0 (fvar y) w x)
                     (cong (λ z → openRec 0 z (w [ x := v ])) (subst-fvar-≢ v x≢y))

        transport : ((y , t [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ []
                      ⊢ ((u ^ fvar y) [ x := v ]) ⟶≤ ((u' ^ fvar y) [ x := v ])
                  → ((y , t [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ []
                      ⊢ ((u [ x := v ]) ^ fvar y) ⟶≤ ((u' [ x := v ]) ^ fvar y)
        transport h rewrite sym (eq u) | sym (eq u') = h

⟶≤-subst {Γ} {v = v} x Δ lv x∉v fvv (Srs-FunOp {_} {s} {α} {t} {u} {u'} L F) =
  Srs-FunOp (x ∷ L ++ fv v) body
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v)
         → ((y , α [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ substStack x v s
             ⊢ ((u [ x := v ]) ^ fvar y) ⟶≤ ((u' [ x := v ]) ^ fvar y)
    body {y} y∉ = transport (⟶≤-subst x ((y , α) ∷ Δ) lv x∉v fvv (F (∉-++ˡ (∉-tail y∉))))
      where
        x≢y : x ≢ y
        x≢y p = y∉ (here (sym p))

        eq : ∀ w → ((w ^ fvar y) [ x := v ]) ≡ ((w [ x := v ]) ^ fvar y)
        eq w = trans (subst-open lv 0 (fvar y) w x)
                     (cong (λ z → openRec 0 z (w [ x := v ])) (subst-fvar-≢ v x≢y))

        transport : ((y , α [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ substStack x v s
                      ⊢ ((u ^ fvar y) [ x := v ]) ⟶≤ ((u' ^ fvar y) [ x := v ])
                  → ((y , α [ x := v ]) ∷ (substCtx x v Δ ++ Γ)) ∣ substStack x v s
                      ⊢ ((u [ x := v ]) ^ fvar y) ⟶≤ ((u' [ x := v ]) ^ fvar y)
        transport h rewrite sym (eq u) | sym (eq u') = h
```

## What this establishes

Lemmas B.6 and B.9. With B.10 (`⟶≡-subst`) and B.19 (the diamond) already in hand, all four
inputs to Theorem 4.5 are available.

**Next:** Theorem 4.5 itself.
