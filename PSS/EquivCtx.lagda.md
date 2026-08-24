# System λ⊲: a context-sensitive equivalence

v1 states plainly that "the extended context `Γ ∣ B` is **immaterial** to the equivalence
reduction", and `PSS/Faithfulness` proves it — the index is decorative. That makes λ⊲'s
equational theory strictly blinder than the subtyping theory built on top of it: `⟶≤` consults
the context, `⟶≡` cannot. The analogy is untyped versus typed conversion, not heterogeneous
equality — λ⊲ has one syntactic category, so there are no types to cross.

This module closes that gap. We index equivalence by an **equational context** `Δ` of exact
identifications `x ≡ α`, kept separate from λ⊲'s subtyping context so that nothing already
proved is disturbed, and add one rule:

> `Ce-Pro : (x , α) ∈ Δ  →  LC α  →  Δ ⊢ x ⟶≐ α`

The rule is deliberately **not simultaneous**: it unfolds `x` to `α` and stops, rather than also
reducing `α`. MPSS's `Me-Pro` does reduce it, and that is precisely what forces v2's diamond to
quantify over *two* reduced extended contexts with a per-variable proviso. Keeping the unfolding
atomic costs one trivial case in the diamond instead, as `⟶≐-diamond` below shows.

```agda
{-# OPTIONS --safe #-}

module PSS.EquivCtx where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import PSS.Syntax
open import PSS.Reduction
open import PSS.Close
open import PSS.Equivalence
```

## Equational contexts

`fvEq Δ` collects every name `Δ` mentions — both the variables it identifies and the free
variables of what they are identified with. A name fresh for `fvEq Δ` is invisible to `Ce-Pro`,
which is what makes renaming and substitution go through.

```agda
EqCtx : Set
EqCtx = List (Name × Tm)

fvEq : EqCtx → List Name
fvEq []            = []
fvEq ((x , α) ∷ Δ) = x ∷ (fv α ++ fvEq Δ)

∈-fvEq : ∀ {Δ x α} → (x , α) ∈ Δ → x ∈ fvEq Δ
∈-fvEq (here refl) = here refl
∈-fvEq {(y , β) ∷ Δ} (there m) = there (∈-++⁺ʳ (fv β) (∈-fvEq m))
  where open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)

fv-fvEq : ∀ {Δ x α} → (x , α) ∈ Δ → fv α ⊑ fvEq Δ
fv-fvEq (here refl) = λ h → there (∈-++⁺ˡ h)
  where open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
fv-fvEq {(y , β) ∷ Δ} (there m) = λ h → there (∈-++⁺ʳ (fv β) (fv-fvEq m h))
  where open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
```

## The relation

Every rule of `⟶≡` reappears verbatim, plus `Ce-Pro`.

```agda
infix 3 _⊢_⟶≐_
data _⊢_⟶≐_ : EqCtx → Tm → Tm → Set where

  Ce-Var    : ∀ {Δ x} → Δ ⊢ fvar x ⟶≐ fvar x

  Ce-Top    : ∀ {Δ} → Δ ⊢ Top ⟶≐ Top

  Ce-Pro    : ∀ {Δ x α}
            → (x , α) ∈ Δ → LC α
            → Δ ⊢ fvar x ⟶≐ α

  Ce-App    : ∀ {Δ u u' v v'}
            → Δ ⊢ u ⟶≐ u' → Δ ⊢ v ⟶≐ v'
            → Δ ⊢ app u v ⟶≐ app u' v'

  Ce-Fun    : ∀ {Δ t t' u u'} (L : List Name)
            → Δ ⊢ t ⟶≐ t'
            → (∀ {x} → x ∉ L → Δ ⊢ (u ^ fvar x) ⟶≐ (u' ^ fvar x))
            → Δ ⊢ lam t u ⟶≐ lam t' u'

  Ce-Beta   : ∀ {Δ t u u' v v'} (L : List Name)
            → (∀ {x} → x ∉ L → Δ ⊢ (u ^ fvar x) ⟶≐ (u' ^ fvar x))
            → Δ ⊢ v ⟶≐ v'
            → Δ ⊢ app (lam t u) v ⟶≐ (u' ^ v')

  Ce-TopApp : ∀ {Δ u} → Δ ⊢ app Top u ⟶≐ Top
```

## Conservativity

The point of the design: `⟶≐` extends `⟶≡` and **collapses back to it** when the equational
context is empty. Nothing in `PSS/` is disturbed.

```agda
⟶≡⇒⟶≐ : ∀ {Δ u v} → u ⟶≡ v → Δ ⊢ u ⟶≐ v
⟶≡⇒⟶≐ Cr-Var          = Ce-Var
⟶≡⇒⟶≐ Cr-Top          = Ce-Top
⟶≡⇒⟶≐ (Cr-App d e)    = Ce-App (⟶≡⇒⟶≐ d) (⟶≡⇒⟶≐ e)
⟶≡⇒⟶≐ (Cr-Fun L d F)  = Ce-Fun L (⟶≡⇒⟶≐ d) (λ x∉ → ⟶≡⇒⟶≐ (F x∉))
⟶≡⇒⟶≐ (Cr-Beta {u' = u'} L F e) =
  Ce-Beta {u' = u'} L (λ x∉ → ⟶≡⇒⟶≐ (F x∉)) (⟶≡⇒⟶≐ e)
⟶≡⇒⟶≐ Cr-TopApp       = Ce-TopApp

⟶≐-nil : ∀ {u v} → [] ⊢ u ⟶≐ v → u ⟶≡ v
⟶≐-nil Ce-Var          = Cr-Var
⟶≐-nil Ce-Top          = Cr-Top
⟶≐-nil (Ce-Pro () _)
⟶≐-nil (Ce-App d e)    = Cr-App (⟶≐-nil d) (⟶≐-nil e)
⟶≐-nil (Ce-Fun L d F)  = Cr-Fun L (⟶≐-nil d) (λ x∉ → ⟶≐-nil (F x∉))
⟶≐-nil (Ce-Beta {u' = u'} L F e) =
  Cr-Beta {u' = u'} L (λ x∉ → ⟶≐-nil (F x∉)) (⟶≐-nil e)
⟶≐-nil Ce-TopApp       = Cr-TopApp
```

And it is **strictly** larger as soon as `Δ` is non-empty — the variable moves, which
`PSS/Faithfulness`'s `v1-fvar-stuck` shows `⟶≡` can never do.

```agda
Δ₁ : EqCtx
Δ₁ = (0 , Top) ∷ []

moves : Δ₁ ⊢ fvar 0 ⟶≐ Top
moves = Ce-Pro (here refl) lc-Top

strictly-larger : ¬ (∀ {Δ u v} → Δ ⊢ u ⟶≐ v → u ⟶≡ v)
strictly-larger collapse with collapse moves
... | ()
```

## Weakening and local closure

```agda
⟶≐-mono : ∀ {Δ Δ' u v} → (∀ {x α} → (x , α) ∈ Δ → (x , α) ∈ Δ')
        → Δ ⊢ u ⟶≐ v → Δ' ⊢ u ⟶≐ v
⟶≐-mono f Ce-Var         = Ce-Var
⟶≐-mono f Ce-Top         = Ce-Top
⟶≐-mono f (Ce-Pro m lα)  = Ce-Pro (f m) lα
⟶≐-mono f (Ce-App d e)   = Ce-App (⟶≐-mono f d) (⟶≐-mono f e)
⟶≐-mono f (Ce-Fun L d F) = Ce-Fun L (⟶≐-mono f d) (λ x∉ → ⟶≐-mono f (F x∉))
⟶≐-mono f (Ce-Beta {u' = u'} L F e) =
  Ce-Beta {u' = u'} L (λ x∉ → ⟶≐-mono f (F x∉)) (⟶≐-mono f e)
⟶≐-mono f Ce-TopApp      = Ce-TopApp

⟶≐-refl : ∀ {Δ t} → LC t → Δ ⊢ t ⟶≐ t
⟶≐-refl lt = ⟶≡⇒⟶≐ (⟶≡-refl lt)

⟶≐-lc : ∀ {Δ u v} → LC u → Δ ⊢ u ⟶≐ v → LC v
⟶≐-lc lu Ce-Var          = lc-fvar
⟶≐-lc lu Ce-Top          = lc-Top
⟶≐-lc lu (Ce-Pro _ lα)   = lα
⟶≐-lc (lc-app lu lv) (Ce-App d e) = lc-app (⟶≐-lc lu d) (⟶≐-lc lv e)
⟶≐-lc (lc-lam L₀ lt F₀) (Ce-Fun L d F) =
  lc-lam (L₀ ++ L) (⟶≐-lc lt d)
         (λ x∉ → ⟶≐-lc (F₀ (∉-++ˡ x∉)) (F (∉-++ʳ L₀ x∉)))
⟶≐-lc (lc-app (lc-lam L₀ lt F₀) lv) (Ce-Beta {t = t} {u' = u'} L F e) =
  open-lc {t} {u'} lam-u' (⟶≐-lc lv e)
  where
    lam-u' : LC (lam t u')
    lam-u' = lc-lam (L ++ L₀) lt
                    (λ {x} x∉ → ⟶≐-lc (F₀ (∉-++ʳ L x∉)) (F (∉-++ˡ x∉)))
⟶≐-lc lu Ce-TopApp       = lc-Top
```

## Functional equational contexts

The diamond needs each variable identified at most once — otherwise two `Ce-Pro` steps at the
same variable land on unrelated terms with nothing to join them.

```agda
domEq : EqCtx → List Name
domEq []            = []
domEq ((x , _) ∷ Δ) = x ∷ domEq Δ

data EqOK : EqCtx → Set where
  eq-nil  : EqOK []
  eq-cons : ∀ {Δ x α} → EqOK Δ → x ∉ domEq Δ → EqOK ((x , α) ∷ Δ)

∈-dom-eq : ∀ {Δ x α} → (x , α) ∈ Δ → x ∈ domEq Δ
∈-dom-eq (here refl) = here refl
∈-dom-eq (there m)   = there (∈-dom-eq m)

eq-unique : ∀ {Δ x α β} → EqOK Δ → (x , α) ∈ Δ → (x , β) ∈ Δ → α ≡ β
eq-unique (eq-cons _ _) (here refl) (here refl) = refl
eq-unique (eq-cons _ x∉) (here refl) (there n)  = ⊥-elim (x∉ (∈-dom-eq n))
eq-unique (eq-cons _ x∉) (there m) (here refl)  = ⊥-elim (x∉ (∈-dom-eq m))
eq-unique (eq-cons ok _) (there m) (there n)    = eq-unique ok m n
```

## Substitution and renaming

`Ce-Pro` is not stable under arbitrary substitution — substituting for an identified variable
would replace the source of the rule while leaving its target. It *is* stable for names fresh
for `Δ`, which is all the binder cases ever need, so freshness for `fvEq Δ` is carried as a
premise.

```agda
⟶≐-subst : ∀ {Δ t t' v v'} x
         → x ∉ fvEq Δ → LC v → LC v'
         → Δ ⊢ t ⟶≐ t' → Δ ⊢ v ⟶≐ v'
         → Δ ⊢ (t [ x := v ]) ⟶≐ (t' [ x := v' ])

⟶≐-subst {Δ} {v = v} {v'} x x∉Δ lv lv' (Ce-Var {x = y}) sv = go
  where
    go : Δ ⊢ (fvar y [ x := v ]) ⟶≐ (fvar y [ x := v' ])
    go with x ≟ y
    ... | yes _ = sv
    ... | no  _ = Ce-Var

⟶≐-subst x x∉Δ lv lv' Ce-Top sv = Ce-Top
```

The new case. A variable identified by `Δ` is never the one being substituted for — `x` is fresh
for `fvEq Δ` — and the target `α` is untouched for the same reason, so the rule survives intact.

```agda
⟶≐-subst {Δ} {v = v} {v'} x x∉Δ lv lv' (Ce-Pro {x = y} {α} m lα) sv = go
  where
    x≢y : x ≢ y
    x≢y p = x∉Δ (subst (_∈ fvEq Δ) (sym p) (∈-fvEq m))

    x∉α : x ∉ fv α
    x∉α h = x∉Δ (fv-fvEq m h)

    go : Δ ⊢ (fvar y [ x := v ]) ⟶≐ (α [ x := v' ])
    go rewrite subst-fresh {α} x v' x∉α with x ≟ y
    ... | yes p = ⊥-elim (x≢y p)
    ... | no  _ = Ce-Pro m lα

⟶≐-subst x x∉Δ lv lv' (Ce-App d e) sv =
  Ce-App (⟶≐-subst x x∉Δ lv lv' d sv) (⟶≐-subst x x∉Δ lv lv' e sv)

⟶≐-subst {Δ} {v = v} {v'} x x∉Δ lv lv' (Ce-Fun {u = u} {u'} L d F) sv =
  Ce-Fun (x ∷ L ++ fv v ++ fv v') (⟶≐-subst x x∉Δ lv lv' d sv) body
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v ++ fv v')
         → Δ ⊢ ((u [ x := v ]) ^ fvar y) ⟶≐ ((u' [ x := v' ]) ^ fvar y)
    body {y} y∉ = transport (⟶≐-subst x x∉Δ lv lv' (F (∉-++ˡ (∉-tail y∉))) sv)
      where
        x≢y : x ≢ y
        x≢y refl = y∉ (here refl)

        eq  = trans (subst-open lv 0 (fvar y) u x)
                    (cong (λ z → openRec 0 z (u [ x := v ])) (subst-fvar-≢ v x≢y))
        eq' = trans (subst-open lv' 0 (fvar y) u' x)
                    (cong (λ z → openRec 0 z (u' [ x := v' ])) (subst-fvar-≢ v' x≢y))

        transport : Δ ⊢ ((u ^ fvar y) [ x := v ]) ⟶≐ ((u' ^ fvar y) [ x := v' ])
                  → Δ ⊢ ((u [ x := v ]) ^ fvar y) ⟶≐ ((u' [ x := v' ]) ^ fvar y)
        transport h rewrite sym eq | sym eq' = h

⟶≐-subst {Δ} {v = v} {v'} x x∉Δ lv lv'
         (Ce-Beta {t = t} {u} {u'} {w} {w'} L F sw) sv =
  transport (Ce-Beta {t = t [ x := v ]} {u [ x := v ]} {u' [ x := v' ]}
                     {w [ x := v ]} {w' [ x := v' ]}
                     (x ∷ L ++ fv v ++ fv v') body (⟶≐-subst x x∉Δ lv lv' sw sv))
  where
    body : ∀ {y} → y ∉ (x ∷ L ++ fv v ++ fv v')
         → Δ ⊢ ((u [ x := v ]) ^ fvar y) ⟶≐ ((u' [ x := v' ]) ^ fvar y)
    body {y} y∉ = go (⟶≐-subst x x∉Δ lv lv' (F (∉-++ˡ (∉-tail y∉))) sv)
      where
        x≢y : x ≢ y
        x≢y refl = y∉ (here refl)

        eq  = trans (subst-open lv 0 (fvar y) u x)
                    (cong (λ z → openRec 0 z (u [ x := v ])) (subst-fvar-≢ v x≢y))
        eq' = trans (subst-open lv' 0 (fvar y) u' x)
                    (cong (λ z → openRec 0 z (u' [ x := v' ])) (subst-fvar-≢ v' x≢y))

        go : Δ ⊢ ((u ^ fvar y) [ x := v ]) ⟶≐ ((u' ^ fvar y) [ x := v' ])
           → Δ ⊢ ((u [ x := v ]) ^ fvar y) ⟶≐ ((u' [ x := v' ]) ^ fvar y)
        go h rewrite sym eq | sym eq' = h

    eqβ : ((u' ^ w') [ x := v' ]) ≡ ((u' [ x := v' ]) ^ (w' [ x := v' ]))
    eqβ = subst-open lv' 0 w' u' x

    transport : Δ ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶≐ ((u' [ x := v' ]) ^ (w' [ x := v' ]))
              → Δ ⊢ (app (lam (t [ x := v ]) (u [ x := v ])) (w [ x := v ]))
                  ⟶≐ ((u' ^ w') [ x := v' ])
    transport h rewrite eqβ = h

⟶≐-subst x x∉Δ lv lv' Ce-TopApp sv = Ce-TopApp
```

Renaming and closing a join back into a body, exactly as for `⟶≡` but carrying freshness for
`Δ`.

```agda
⟶≐-rename : ∀ {Δ u u'} x y
          → x ∉ fvEq Δ → x ∉ fv u → x ∉ fv u'
          → Δ ⊢ (u ^ fvar x) ⟶≐ (u' ^ fvar x)
          → Δ ⊢ (u ^ fvar y) ⟶≐ (u' ^ fvar y)
⟶≐-rename {Δ} {u} {u'} x y x∉Δ x∉u x∉u' s
  rewrite subst-intro {u}  (lc-fvar {y}) x x∉u
        | subst-intro {u'} (lc-fvar {y}) x x∉u'
  = ⟶≐-subst x x∉Δ lc-fvar lc-fvar s Ce-Var

close-rename≐ : ∀ {Δ b w} x y
              → LC w → x ∉ fvEq Δ → x ∉ fv b
              → Δ ⊢ (b ^ fvar x) ⟶≐ w
              → Δ ⊢ (b ^ fvar y) ⟶≐ ((closeRec 0 x w) ^ fvar y)
close-rename≐ {Δ} {b} {w} x y lw x∉Δ x∉b s =
  ⟶≐-rename {Δ} {b} {closeRec 0 x w} x y x∉Δ x∉b (fv-close 0 x w) s'
  where
    s' : Δ ⊢ (b ^ fvar x) ⟶≐ ((closeRec 0 x w) ^ fvar x)
    s' rewrite open-close lw 0 x = s

⟶≐-open : ∀ {Δ u u' v v'} (L : List Name)
        → LC v → LC v'
        → (∀ {z} → z ∉ L → Δ ⊢ (u ^ fvar z) ⟶≐ (u' ^ fvar z))
        → Δ ⊢ v ⟶≐ v'
        → Δ ⊢ (u ^ v) ⟶≐ (u' ^ v')
⟶≐-open {Δ} {u} {u'} {v} {v'} L lv lv' F sv = go
  where
    A    = L ++ fvEq Δ ++ fv u ++ fv u'
    x    = fresh A
    a∉   = fresh-∉ A
    x∉L  = ∉-++ˡ a∉
    r₁   = ∉-++ʳ L a∉
    x∉Δ  = ∉-++ˡ r₁
    r₂   = ∉-++ʳ (fvEq Δ) r₁
    x∉u  = ∉-++ˡ r₂
    x∉u' = ∉-++ʳ (fv u) r₂

    go : Δ ⊢ (u ^ v) ⟶≐ (u' ^ v')
    go rewrite subst-intro {u} lv x x∉u | subst-intro {u'} lv' x x∉u' =
      ⟶≐-subst x x∉Δ lv lv' (F x∉L) sv
```

## The diamond

`Ce-Pro` fires only on a variable, and a variable has no other redex, so the new rule cannot
create a critical pair with `Ce-Beta` or any congruence. The proof is therefore the existing
`⟶≡` diamond verbatim — the same fresh-name-and-close argument — plus four variable cases, three
of which are immediate and the fourth of which is where `EqOK` is spent.

```agda
⟶≐-diamond : ∀ {Δ t u v} → EqOK Δ → LC t
           → Δ ⊢ t ⟶≐ u → Δ ⊢ t ⟶≐ v
           → ∃[ w ] ((Δ ⊢ u ⟶≐ w) × (Δ ⊢ v ⟶≐ w))
```

The four new cases. Unfolding a variable races only against leaving it alone, or against
unfolding it again — and `EqOK` makes the latter the same unfolding.

```agda
⟶≐-diamond ok lt Ce-Var Ce-Var = _ , Ce-Var , Ce-Var
⟶≐-diamond ok lt Ce-Var (Ce-Pro m lα)         = _ , Ce-Pro m lα , ⟶≐-refl lα
⟶≐-diamond ok lt (Ce-Pro m lα) Ce-Var         = _ , ⟶≐-refl lα , Ce-Pro m lα
⟶≐-diamond ok lt (Ce-Pro m₁ lα₁) (Ce-Pro m₂ lα₂)
  with eq-unique ok m₁ m₂
... | refl = _ , ⟶≐-refl lα₁ , ⟶≐-refl lα₂
```

Everything else is the `⟶≡` proof with `Δ` threaded and `fvEq Δ` added to each avoid-set.

```agda
⟶≐-diamond ok lt Ce-Top Ce-Top = _ , Ce-Top , Ce-Top

⟶≐-diamond ok lt Ce-TopApp Ce-TopApp             = Top , Ce-Top    , Ce-Top
⟶≐-diamond ok lt Ce-TopApp (Ce-App Ce-Top _)     = Top , Ce-Top    , Ce-TopApp
⟶≐-diamond ok lt (Ce-App Ce-Top _) Ce-TopApp     = Top , Ce-TopApp , Ce-Top

⟶≐-diamond ok (lc-app lf la) (Ce-App s₁ s₂) (Ce-App s₁' s₂')
  with ⟶≐-diamond ok lf s₁ s₁' | ⟶≐-diamond ok la s₂ s₂'
... | w₁ , p₁ , q₁ | w₂ , p₂ , q₂ = app w₁ w₂ , Ce-App p₁ p₂ , Ce-App q₁ q₂

⟶≐-diamond {Δ} ok (lc-lam {t} {b} L₀ lt F₀)
           (Ce-Fun {t' = t₁} {u' = b₁} L₁ st₁ F₁)
           (Ce-Fun {t' = t₂} {u' = b₂} L₂ st₂ F₂) =
  lam (proj₁ jt) b₃ , Ce-Fun [] (proj₁ (proj₂ jt)) (λ _ → r₁)
                    , Ce-Fun [] (proj₂ (proj₂ jt)) (λ _ → r₂)
  where
    A = L₀ ++ L₁ ++ L₂ ++ fvEq Δ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂
    rest₄ = ∉-++ʳ (fvEq Δ) rest₃

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉Δ  = ∉-++ˡ rest₃
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₄
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₄

    jt = ⟶≐-diamond ok lt st₁ st₂
    jb = ⟶≐-diamond ok (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lw : LC (proj₁ jb)
    lw = ⟶≐-lc (⟶≐-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → Δ ⊢ (b₁ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₁ {y} = close-rename≐ {Δ} {b₁} {proj₁ jb} x y lw x∉Δ x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → Δ ⊢ (b₂ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₂ {y} = close-rename≐ {Δ} {b₂} {proj₁ jb} x y lw x∉Δ x∉b₂ (proj₂ (proj₂ jb))

⟶≐-diamond {Δ} ok (lc-app (lc-lam {a} {b} L₀ la F₀) lc)
           (Ce-App {v' = c₁} (Ce-Fun {t' = a₁} {u' = b₁} L₁ sa₁ F₁) sc₁)
           (Ce-Beta {u' = b₂} {v' = c₂} L₂ F₂ sc₂) =
  (b₃ ^ proj₁ jc)
  , Ce-Beta {t = a₁} {b₁} {b₃} {c₁} {proj₁ jc} [] (λ _ → r₁) (proj₁ (proj₂ jc))
  , ⟶≐-open {Δ} {b₂} {b₃} {c₂} {proj₁ jc} [] lc₂ lc₃ (λ _ → r₂) (proj₂ (proj₂ jc))
  where
    A = L₀ ++ L₁ ++ L₂ ++ fvEq Δ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂
    rest₄ = ∉-++ʳ (fvEq Δ) rest₃

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉Δ  = ∉-++ˡ rest₃
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₄
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₄

    jc = ⟶≐-diamond ok lc sc₁ sc₂
    jb = ⟶≐-diamond ok (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lc₂ : LC c₂
    lc₂ = ⟶≐-lc lc sc₂
    lc₃ : LC (proj₁ jc)
    lc₃ = ⟶≐-lc lc₂ (proj₂ (proj₂ jc))

    lw : LC (proj₁ jb)
    lw = ⟶≐-lc (⟶≐-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → Δ ⊢ (b₁ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₁ {y} = close-rename≐ {Δ} {b₁} {proj₁ jb} x y lw x∉Δ x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → Δ ⊢ (b₂ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₂ {y} = close-rename≐ {Δ} {b₂} {proj₁ jb} x y lw x∉Δ x∉b₂ (proj₂ (proj₂ jb))

⟶≐-diamond {Δ} ok (lc-app (lc-lam {a} {b} L₀ la F₀) lc)
           (Ce-Beta {u' = b₁} {v' = c₁} L₁ F₁ sc₁)
           (Ce-App {v' = d₂} (Ce-Fun {t' = a₂} {u' = b₂} L₂ sa₂ F₂) sc₂) =
  (b₃ ^ proj₁ jc)
  , ⟶≐-open {Δ} {b₁} {b₃} {c₁} {proj₁ jc} [] lc₁ lc₃ (λ _ → r₁) (proj₁ (proj₂ jc))
  , Ce-Beta {t = a₂} {b₂} {b₃} {d₂} {proj₁ jc} [] (λ _ → r₂) (proj₂ (proj₂ jc))
  where
    A = L₀ ++ L₁ ++ L₂ ++ fvEq Δ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂
    rest₄ = ∉-++ʳ (fvEq Δ) rest₃

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉Δ  = ∉-++ˡ rest₃
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₄
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₄

    jc = ⟶≐-diamond ok lc sc₁ sc₂
    jb = ⟶≐-diamond ok (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lc₁ : LC c₁
    lc₁ = ⟶≐-lc lc sc₁
    lc₃ : LC (proj₁ jc)
    lc₃ = ⟶≐-lc lc₁ (proj₁ (proj₂ jc))

    lw : LC (proj₁ jb)
    lw = ⟶≐-lc (⟶≐-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → Δ ⊢ (b₁ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₁ {y} = close-rename≐ {Δ} {b₁} {proj₁ jb} x y lw x∉Δ x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → Δ ⊢ (b₂ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₂ {y} = close-rename≐ {Δ} {b₂} {proj₁ jb} x y lw x∉Δ x∉b₂ (proj₂ (proj₂ jb))

⟶≐-diamond {Δ} ok (lc-app (lc-lam {a} {b} L₀ la F₀) lc)
           (Ce-Beta {u' = b₁} {v' = c₁} L₁ F₁ sc₁)
           (Ce-Beta {u' = b₂} {v' = c₂} L₂ F₂ sc₂) =
  (b₃ ^ proj₁ jc)
  , ⟶≐-open {Δ} {b₁} {b₃} {c₁} {proj₁ jc} [] lc₁ lc₃ (λ _ → r₁) (proj₁ (proj₂ jc))
  , ⟶≐-open {Δ} {b₂} {b₃} {c₂} {proj₁ jc} [] lc₂ lc₃ (λ _ → r₂) (proj₂ (proj₂ jc))
  where
    A = L₀ ++ L₁ ++ L₂ ++ fvEq Δ ++ fv b₁ ++ fv b₂
    x = fresh A
    a∉    = fresh-∉ A
    rest₁ = ∉-++ʳ L₀ a∉
    rest₂ = ∉-++ʳ L₁ rest₁
    rest₃ = ∉-++ʳ L₂ rest₂
    rest₄ = ∉-++ʳ (fvEq Δ) rest₃

    x∉L₀ = ∉-++ˡ a∉
    x∉L₁ = ∉-++ˡ rest₁
    x∉L₂ = ∉-++ˡ rest₂
    x∉Δ  = ∉-++ˡ rest₃
    x∉b₁ : x ∉ fv b₁
    x∉b₁ = ∉-++ˡ rest₄
    x∉b₂ : x ∉ fv b₂
    x∉b₂ = ∉-++ʳ (fv b₁) rest₄

    jc = ⟶≐-diamond ok lc sc₁ sc₂
    jb = ⟶≐-diamond ok (F₀ x∉L₀) (F₁ x∉L₁) (F₂ x∉L₂)

    lc₁ : LC c₁
    lc₁ = ⟶≐-lc lc sc₁
    lc₂ : LC c₂
    lc₂ = ⟶≐-lc lc sc₂
    lc₃ : LC (proj₁ jc)
    lc₃ = ⟶≐-lc lc₁ (proj₁ (proj₂ jc))

    lw : LC (proj₁ jb)
    lw = ⟶≐-lc (⟶≐-lc (F₀ x∉L₀) (F₁ x∉L₁)) (proj₁ (proj₂ jb))

    b₃ = closeRec 0 x (proj₁ jb)

    r₁ : ∀ {y} → Δ ⊢ (b₁ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₁ {y} = close-rename≐ {Δ} {b₁} {proj₁ jb} x y lw x∉Δ x∉b₁ (proj₁ (proj₂ jb))

    r₂ : ∀ {y} → Δ ⊢ (b₂ ^ fvar y) ⟶≐ (b₃ ^ fvar y)
    r₂ {y} = close-rename≐ {Δ} {b₂} {proj₁ jb} x y lw x∉Δ x∉b₂ (proj₂ (proj₂ jb))
```

## Church–Rosser

The diamond gives confluence by the usual strip argument, unchanged.

```agda
infix 3 _⊢_⟶≐*_
data _⊢_⟶≐*_ : EqCtx → Tm → Tm → Set where
  ε≐   : ∀ {Δ t} → Δ ⊢ t ⟶≐* t
  _◅≐_ : ∀ {Δ t u v} → Δ ⊢ t ⟶≐ u → Δ ⊢ u ⟶≐* v → Δ ⊢ t ⟶≐* v

_++≐_ : ∀ {Δ t u v} → Δ ⊢ t ⟶≐* u → Δ ⊢ u ⟶≐* v → Δ ⊢ t ⟶≐* v
ε≐        ++≐ c = c
(e ◅≐ c₁) ++≐ c = e ◅≐ (c₁ ++≐ c)

⟶≐*-lc : ∀ {Δ t u} → LC t → Δ ⊢ t ⟶≐* u → LC u
⟶≐*-lc lt ε≐        = lt
⟶≐*-lc lt (e ◅≐ c) = ⟶≐*-lc (⟶≐-lc lt e) c

⟶≐-strip : ∀ {Δ t u v} → EqOK Δ → LC t
         → Δ ⊢ t ⟶≐ u → Δ ⊢ t ⟶≐* v
         → ∃[ w ] ((Δ ⊢ u ⟶≐* w) × (Δ ⊢ v ⟶≐* w))
⟶≐-strip ok lt e ε≐ = _ , ε≐ , (e ◅≐ ε≐)
⟶≐-strip ok lt e (e₁ ◅≐ c) with ⟶≐-diamond ok lt e e₁
... | w₁ , p , q with ⟶≐-strip ok (⟶≐-lc lt e₁) q c
...   | w , c₁ , c₂ = w , (p ◅≐ c₁) , c₂

⟶≐-confluent : ∀ {Δ t u v} → EqOK Δ → LC t
             → Δ ⊢ t ⟶≐* u → Δ ⊢ t ⟶≐* v
             → ∃[ w ] ((Δ ⊢ u ⟶≐* w) × (Δ ⊢ v ⟶≐* w))
⟶≐-confluent ok lt ε≐ c = _ , c , ε≐
⟶≐-confluent ok lt (e ◅≐ c₁) c with ⟶≐-strip ok lt e c
... | w₁ , d₁ , d₂ with ⟶≐-confluent ok (⟶≐-lc lt e) c₁ d₁
...   | w , f₁ , f₂ = w , f₁ , (d₂ ++≐ f₂)
```

## What this establishes

A **context-sensitive equivalence for λ⊲** with its full basic metatheory:

- **Conservative.** `⟶≡ ⊆ ⟶≐` at every `Δ`, with equality at `Δ = []` (`⟶≐-nil`). Nothing in
  `PSS/` is disturbed, and every existing theorem about `⟶≡` transfers by `⟶≡⇒⟶≐`.
- **Strictly stronger** as soon as `Δ` is non-empty (`strictly-larger`): a variable can move,
  which `⟶≡` can never do.
- **Substitution, renaming and opening**, for names fresh for `fvEq Δ` — which is all the binder
  rules ever need.
- **The diamond** (`⟶≐-diamond`) and **Church–Rosser** (`⟶≐-confluent`), given a functional `Δ`.

The finding worth recording: **the two-reduced-context complication in MPSS is not intrinsic to
context-sensitive equivalence.** v2 needs its diamond quantified over two reduced extended
contexts, with a per-variable side condition on `Me-Pro`, because its unfolding rule is
*simultaneous* — it reduces the annotation as well as substituting it. Making the unfolding
atomic costs exactly four variable cases here, three of them one-liners, and the fourth spending
only functionality of `Δ`. Every other case of the `⟶≡` diamond carries over verbatim, because
`Ce-Pro` fires only on a variable and a variable has no other redex, so no new critical pair
with `Ce-Beta` or any congruence can arise.

What is bought is the thing v1 gives up by fiat when it declares the context "immaterial to the
equivalence reduction": the equational theory can now see what the subtyping theory sees. The
price is `EqOK` — an equational context must identify each variable once.
