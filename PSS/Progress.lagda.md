# System λ⊲: Theorem 4.1 — progress

A well-formed term is a normal form or reduces. Computation in λ⊲ never gets stuck.

The load-bearing input is Theorem 4.3: in an application `u v`, well-formedness makes `u` a
subtype of some `λx≤w.Top`, and if `u` were `Top` that would be a supertype of an abstraction —
impossible. So a normal `u` in operator position is either an abstraction, and the redex fires,
or a neutral, and the application is itself neutral.

Reduction goes under binders (λ⊲'s normal forms have normal annotation *and* body), so the
congruence rules are cofinitely quantified and both `NF` and `↦` need renaming.

```agda
{-# OPTIONS --safe #-}

module PSS.Progress where

open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Subtyping
open import PSS.WellFormed
open import PSS.Close
open import PSS.Equivalence
open import PSS.Transitivity
```

## Renaming preserves normal forms

```agda
NF-subst      : ∀ {t x y} → NF t → NF (t [ x := fvar y ])
Neutral-subst : ∀ {t x y} → Neutral t → Neutral (t [ x := fvar y ])

Neutral-subst {x = x} {y} (ne-var {z}) = go (x ≟ z)
  where
    go : Dec (x ≡ z) → Neutral ((fvar z) [ x := fvar y ])
    go (yes refl) rewrite subst-fvar-≡ {x} (fvar y) = ne-var
    go (no  q)    rewrite subst-fvar-≢ {x} {z} (fvar y) q = ne-var
Neutral-subst (ne-app ne nf) = ne-app (Neutral-subst ne) (NF-subst nf)

NF-subst nf-Top = nf-Top
NF-subst (nf-ne ne) = nf-ne (Neutral-subst ne)
NF-subst {x = x} {y} (nf-lam {t} {u} L nt F) =
  nf-lam (x ∷ L) (NF-subst nt) body
  where
    body : ∀ {z} → z ∉ (x ∷ L) → NF ((u [ x := fvar y ]) ^ fvar z)
    body {z} z∉ = transport (NF-subst (F (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq : ((u ^ fvar z) [ x := fvar y ]) ≡ ((u [ x := fvar y ]) ^ fvar z)
        eq = trans (subst-open lc-fvar 0 (fvar z) u x)
                   (cong (λ q → openRec 0 q (u [ x := fvar y ]))
                         (subst-fvar-≢ (fvar y) x≢z))

        transport : NF ((u ^ fvar z) [ x := fvar y ]) → NF ((u [ x := fvar y ]) ^ fvar z)
        transport h rewrite sym eq = h

NF-open-rename : ∀ {b} x y → x ∉ fv b → NF (b ^ fvar x) → NF (b ^ fvar y)
NF-open-rename {b} x y x∉b nf
  rewrite subst-intro {b} (lc-fvar {y}) x x∉b = NF-subst nf
```

## Substitution and renaming for `↦`

```agda
↦-lc : ∀ {t t'} → LC t → t ↦ t' → LC t'
↦-lc lt (E-App llam lv)      = open-lc llam lv
↦-lc (lc-lam L₀ la F₀) (E-Lam-l st) = lc-lam L₀ (↦-lc la st) F₀
↦-lc (lc-lam L₀ la F₀) (E-Lam-r L F) =
  lc-lam (L₀ ++ L) la (λ {x} x∉ → ↦-lc (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
↦-lc (lc-app lu lv) (E-App-l st) = lc-app (↦-lc lu st) lv
↦-lc (lc-app lu lv) (E-App-r st) = lc-app lu (↦-lc lv st)

↦-subst : ∀ {t t' v} x → LC v → t ↦ t' → (t [ x := v ]) ↦ (t' [ x := v ])
↦-subst {v = v} x lv (E-App {a} {b} {c} llam lc) = transport
  (E-App {a [ x := v ]} {b [ x := v ]} {c [ x := v ]} (subst-lc llam lv) (subst-lc lc lv))
  where
    eq : ((b ^ c) [ x := v ]) ≡ ((b [ x := v ]) ^ (c [ x := v ]))
    eq = subst-open lv 0 c b x

    transport : (app (lam (a [ x := v ]) (b [ x := v ])) (c [ x := v ]))
                  ↦ ((b [ x := v ]) ^ (c [ x := v ]))
              → (app (lam (a [ x := v ]) (b [ x := v ])) (c [ x := v ]))
                  ↦ ((b ^ c) [ x := v ])
    transport h rewrite eq = h

↦-subst x lv (E-Lam-l st) = E-Lam-l (↦-subst x lv st)

↦-subst {v = v} x lv (E-Lam-r {t} {u} {u'} L F) = E-Lam-r (x ∷ L ++ fv v) body
  where
    body : ∀ {z} → z ∉ (x ∷ L ++ fv v)
         → ((u [ x := v ]) ^ fvar z) ↦ ((u' [ x := v ]) ^ fvar z)
    body {z} z∉ = transport (↦-subst x lv (F (∉-++ˡ (∉-tail z∉))))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))

        eq : ∀ w → ((w ^ fvar z) [ x := v ]) ≡ ((w [ x := v ]) ^ fvar z)
        eq w = trans (subst-open lv 0 (fvar z) w x)
                     (cong (λ q → openRec 0 q (w [ x := v ])) (subst-fvar-≢ v x≢z))

        transport : ((u ^ fvar z) [ x := v ]) ↦ ((u' ^ fvar z) [ x := v ])
                  → ((u [ x := v ]) ^ fvar z) ↦ ((u' [ x := v ]) ^ fvar z)
        transport h rewrite sym (eq u) | sym (eq u') = h

↦-subst x lv (E-App-l st) = E-App-l (↦-subst x lv st)
↦-subst x lv (E-App-r st) = E-App-r (↦-subst x lv st)

↦-close-rename : ∀ {b w} x y → LC w → x ∉ fv b
               → (b ^ fvar x) ↦ w
               → (b ^ fvar y) ↦ ((closeRec 0 x w) ^ fvar y)
↦-close-rename {b} {w} x y lw x∉b st = go
  where
    st' : (b ^ fvar x) ↦ ((closeRec 0 x w) ^ fvar x)
    st' rewrite open-close lw 0 x = st

    go : (b ^ fvar y) ↦ ((closeRec 0 x w) ^ fvar y)
    go rewrite subst-intro {b} (lc-fvar {y}) x x∉b
             | subst-intro {closeRec 0 x w} (lc-fvar {y}) x (fv-close 0 x w)
             = ↦-subst x lc-fvar st'
```

## Theorem 4.1 — progress

By induction on local closure, reading the well-formedness derivation alongside it.

```agda
Thm-4·1 : ∀ {Γ s t} → LC t → Γ ∣ s ⊢ t wf → NF t ⊎ ∃[ t' ] (t ↦ t')

Thm-4·1 lc-fvar (W-Var _ _ _) = inj₁ (nf-ne ne-var)
Thm-4·1 lc-Top  (W-Top _)     = inj₁ nf-Top
```

**Abstractions.** Try the annotation, then the body. A step in the body is found at one fresh
name and transported to a cofinite family by closing and renaming; likewise for concluding the
body is normal.

```agda
Thm-4·1 {Γ} (lc-lam {a} {b} L₀ la F₀) (W-Fun L F wa) = result
  where
    A  = L₀ ++ L ++ fv b
    x  = fresh A
    a∉ = fresh-∉ A

    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ (∉-++ʳ L₀ a∉)
    x∉b : x ∉ fv b
    x∉b  = ∉-++ʳ L (∉-++ʳ L₀ a∉)

    result : NF (lam a b) ⊎ ∃[ t' ] (lam a b ↦ t')
    result with Thm-4·1 la wa
    ... | inj₂ (a' , st) = inj₂ (lam a' b , E-Lam-l st)
    ... | inj₁ na with Thm-4·1 (F₀ x∉L₀) (F x∉L)
    ...   | inj₁ nb = inj₁ (nf-lam [] na (λ {y} _ → NF-open-rename {b} x y x∉b nb))
    ...   | inj₂ (w , stw) =
             inj₂ ( lam a (closeRec 0 x w)
                  , E-Lam-r [] (λ {y} _ →
                      ↦-close-rename {b} {w} x y (↦-lc (F₀ x∉L₀) stw) x∉b stw) )

Thm-4·1 {Γ} (lc-lam {a} {b} L₀ la F₀) (W-FunOp L F wa) = result
  where
    A  = L₀ ++ L ++ fv b
    x  = fresh A
    a∉ = fresh-∉ A

    x∉L₀ = ∉-++ˡ a∉
    x∉L  = ∉-++ˡ (∉-++ʳ L₀ a∉)
    x∉b : x ∉ fv b
    x∉b  = ∉-++ʳ L (∉-++ʳ L₀ a∉)

    result : NF (lam a b) ⊎ ∃[ t' ] (lam a b ↦ t')
    result with Thm-4·1 la wa
    ... | inj₂ (a' , st) = inj₂ (lam a' b , E-Lam-l st)
    ... | inj₁ na with Thm-4·1 (F₀ x∉L₀) (F x∉L)
    ...   | inj₁ nb = inj₁ (nf-lam [] na (λ {y} _ → NF-open-rename {b} x y x∉b nb))
    ...   | inj₂ (w , stw) =
             inj₂ ( lam a (closeRec 0 x w)
                  , E-Lam-r [] (λ {y} _ →
                      ↦-close-rename {b} {w} x y (↦-lc (F₀ x∉L₀) stw) x∉b stw) )
```

**Applications.** This is where Theorem 4.3 is spent. Well-formedness makes the operator a
subtype of an abstraction `λx≤w.Top`; a normal operator is therefore not `Top`, since that
would be a supertype of an abstraction. So it is either an abstraction — and the redex fires —
or a neutral, and the application is neutral once the operand is normal too.

```agda
Thm-4·1 (lc-app {u} {v} lu lv) (W-App d₁ d₂)
  with Thm-4·1 lu (proj₁ (≤*wf⇒both d₁))
... | inj₂ (u' , st)              = inj₂ (app u' v , E-App-l st)
... | inj₁ nf-Top                 = ⊥-elim (Thm-4·3 d₁)
... | inj₁ (nf-lam {a} {b} _ _ _) = inj₂ ((b ^ v) , E-App lu lv)
... | inj₁ (nf-ne ne) with Thm-4·1 lv (proj₁ (≤*wf⇒both d₂))
...   | inj₂ (v' , st) = inj₂ (app u v' , E-App-r st)
...   | inj₁ nv        = inj₁ (nf-ne (ne-app ne nv))
```

## What this establishes

**Theorem 4.1.** Together with preservation it gives type safety: a well-formed term never gets
stuck.
