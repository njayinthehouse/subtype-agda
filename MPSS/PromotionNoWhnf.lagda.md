# MPSS: a closed term that reduces to no abstraction is promoted to no abstraction

`MPSS/Conj8NoAbstraction` refutes `Conj-8ʷᶜ` from five hypotheses, the fifth being that no chain
of promotions from the application `f q` ends in an abstraction (`NoAbs`). This module reduces
that hypothesis to one about equivalence reduction alone:

> `NR t`: no `⟶ᵉ*`-reduct of `t` is an abstraction.

For a closed, locally closed `t`, `NR t` gives `NoAbs t`. The reason: in a context with no `≤`
entry, a promotion `Γ ∣ s ⊢ u ⟶ˢ u′` walks down the head of `u` — `Ms-App` pushes an operand,
`Ms-FOp` pops one and binds the parameter by `≡` — and ends in one of four rules. `Ms-Pro` needs
a `≤` entry and there is none. `Ms-Equ`: the promotion is an equivalence step. `Ms-Top`: the
result has `⊤` at the end of its head path, and reduces to `⊤`, from which no abstraction is
reached. `Ms-Fun`: the head path of `u` reaches an abstraction with the stack empty, and then
contracting the redexes along the path reduces `u` to an abstraction, which `NR` excludes.

β at a stack is two equivalence steps, as in `MPSS/Prop17Chain`: bind the parameter to the operand
and unfold it (`Me-App` over `Me-FOp`), then `Me-Bet` on a body that no longer mentions it.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.PromotionNoWhnf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import MPSS.WellFormed
open import MPSS.StackPush
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
open import MPSS.Congruence using (refl-head)
open import MPSS.Narrowing24 using (fv-⟶ˢ-dom)
open import MPSS.Prop17Chain using (unfold; ⊑-there)
open import MPSS.AppClass using (NoSub; ns-eqv)
open import MPSS.Conj8Push using (spine; spine-e)
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_; confluent)
  renaming (_++_ to _++ᵉ_)
open import MPSS.WfCtx using (Conj-8ʷᶜ)
open import MPSS.Conj8NoAbstraction using (_⟶ˢ*_; εˢ; _◅ˢ_; NoAbs; Reaches; refutes)
open import PSS.Syntax
open import PSS.Scope using (fv-open-split)
```

## The two shapes of a head path

Both are read off the raw term, bodies unopened, against the number of operands on the stack.
`TS h n u`: the head path of `u` ends in `⊤`. `FH h n u`: it ends in an abstraction with the
stack empty. `h` is the length of the path, which opening a body does not change; it is what the
reductions below recurse on.

```agda
data TS : ℕ → ℕ → Tm → Set where
  ts-top : ∀ {n} → TS 0 n Top
  ts-app : ∀ {h n u v} → TS h (suc n) u → TS (suc h) n (app u v)
  ts-fop : ∀ {h n t b} → TS h n b → TS (suc h) (suc n) (lam t b)

data FH : ℕ → ℕ → Tm → Set where
  fh-fun : ∀ {t b} → FH 0 0 (lam t b)
  fh-app : ∀ {h n u v} → FH h (suc n) u → FH (suc h) n (app u v)
  fh-fop : ∀ {h n t b} → FH h n b → FH (suc h) (suc n) (lam t b)

TS-open : ∀ {h n u} k w → TS h n u → TS h n (openRec k w u)
TS-open k w ts-top     = ts-top
TS-open k w (ts-app p) = ts-app (TS-open k w p)
TS-open k w (ts-fop p) = ts-fop (TS-open (suc k) w p)

FH-open : ∀ {h n u} k w → FH h n u → FH h n (openRec k w u)
FH-open k w fh-fun     = fh-fun
FH-open k w (fh-app p) = fh-app (FH-open k w p)
FH-open k w (fh-fop p) = fh-fop (FH-open (suc k) w p)

TS-unopen : ∀ {h n} k x u → TS h n (openRec k (fvar x) u) → TS h n u
TS-unopen k x (bvar i) p with k ≟ i
TS-unopen k x (bvar i) () | yes _
TS-unopen k x (bvar i) () | no  _
TS-unopen k x Top       ts-top     = ts-top
TS-unopen k x (app u v) (ts-app p) = ts-app (TS-unopen k x u p)
TS-unopen k x (lam t b) (ts-fop p) = ts-fop (TS-unopen (suc k) x b p)

FH-unopen : ∀ {h n} k x u → FH h n (openRec k (fvar x) u) → FH h n u
FH-unopen k x (bvar i) p with k ≟ i
FH-unopen k x (bvar i) () | yes _
FH-unopen k x (bvar i) () | no  _
FH-unopen k x (app u v) (fh-app p) = fh-app (FH-unopen k x u p)
FH-unopen k x (lam t b) fh-fun     = fh-fun
FH-unopen k x (lam t b) (fh-fop p) = fh-fop (FH-unopen (suc k) x b p)
```

## A promotion that is neither is an equivalence step

```agda
promotion-is-e : ∀ {Γ s u u′} → NoSub Γ
               → LC u → fv u ⊑ dom Γ
               → (∀ {h} → ¬ TS h (length s) u′)
               → (∀ {h} → ¬ FH h (length s) u)
               → Γ ∣ s ⊢ u ⟶ˢ u′ → Γ ∣ s ⊢ u ⟶ᵉ u′
promotion-is-e ns lu fu ¬ts ¬fh (Ms-Pro _ m) = ⊥-elim (ns m)
promotion-is-e ns lu fu ¬ts ¬fh (Ms-Top _)   = ⊥-elim (¬ts ts-top)
promotion-is-e ns lu fu ¬ts ¬fh (Ms-Equ _ e) = e
promotion-is-e ns (lc-app {u} {v} lu lv) fu ¬ts ¬fh (Ms-App d) =
  Me-App (promotion-is-e ns lu (fv-app-op {u} {v} fu) (λ p → ¬ts (ts-app p)) (λ p → ¬fh (fh-app p)) d)
         (refl-head (⟶ˢ-prevalid d))
promotion-is-e ns lu fu ¬ts ¬fh (Ms-Fun _ _) = ⊥-elim (¬fh fh-fun)
promotion-is-e {Γ} ns (lc-lam {t} {b} L₀ lt F₀) fu ¬ts ¬fh d@(Ms-FOp {α = α} {u' = u′} L F) =
  Me-FOp (L ++ L₀) (⟶ᵉ-refl (prevalid-nil pv) lt (fv-lam-ann {t} {b} fu)) body
  where
    pv = ⟶ˢ-prevalid d
    body : ∀ {x} → x ∉ (L ++ L₀) → ((x , eqv , α) ∷ Γ) ∣ _ ⊢ (b ^ fvar x) ⟶ᵉ (u′ ^ fvar x)
    body {x} x∉ =
      promotion-is-e (ns-eqv ns) (F₀ (∉-++ʳ L x∉)) (fv-open-cons {b} x (fv-lam-body {t} {b} fu))
                     (λ p → ¬ts (ts-fop (TS-unopen 0 x u′ p)))
                     (λ p → ¬fh (fh-fop (FH-unopen 0 x b p)))
                     (F (∉-++ˡ x∉))
```

## β at a stack, in two equivalence steps

```agda
fv-open⊑ : ∀ {b c N} → fv b ⊑ N → fv c ⊑ N → fv (b ^ c) ⊑ N
fv-open⊑ {b} {c} fb fc h with fv-open-split 0 c b h
... | inj₁ p = fb p
... | inj₂ p = fc p

β₁ : ∀ {Γ s t b c} → Γ ∣ s prevalid
   → LC (lam t b) → fv (lam t b) ⊑ dom Γ → LC c → fv c ⊑ dom Γ
   → Γ ∣ s ⊢ app (lam t b) c ⟶ᵉ app (lam t (b ^ c)) c
β₁ {Γ} {s} {t} {b} {c} pv ll@(lc-lam L lt F) fl lc fc =
  Me-App (Me-FOp {u = b} {u' = b ^ c} (L ++ fv b ++ dom Γ)
                 (⟶ᵉ-refl (prevalid-nil pv) lt (fv-lam-ann {t} {b} fl)) body)
         (⟶ᵉ-refl (prevalid-nil pv) lc fc)
  where
    lb : LC (b ^ c)
    lb = open-lc {t} {b} {c} ll lc
    body : ∀ {x} → x ∉ (L ++ fv b ++ dom Γ)
         → ((x , eqv , c) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ ((b ^ c) ^ fvar x)
    body {x} x∉ =
      subst (λ q → ((x , eqv , c) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ q) eq
            (unfold (prevalid-cons pv (∉-++ʳ (fv b) (∉-++ʳ L x∉)) lc fc)
                    (here refl) lc (⊑-there fc) (F (∉-++ˡ x∉))
                    (fv-open-cons {b} x (fv-lam-body {t} {b} fl)))
      where
        eq : (b ^ fvar x) [ x := c ] ≡ (b ^ c) ^ fvar x
        eq = trans (sym (subst-intro {b} lc x (∉-++ˡ (∉-++ʳ L x∉)))) (open-lc-id lb 0 (fvar x))

β₂ : ∀ {Γ s t b c} → Γ ∣ s prevalid
   → LC (lam t b) → fv (lam t b) ⊑ dom Γ → LC c → fv c ⊑ dom Γ
   → Γ ∣ s ⊢ app (lam t (b ^ c)) c ⟶ᵉ (b ^ c)
β₂ {Γ} {s} {t} {b} {c} pv ll fl lc fc =
  subst (λ q → Γ ∣ s ⊢ app (lam t (b ^ c)) c ⟶ᵉ q) (sym (open-lc-id lb 0 c))
        (Me-Bet {u = b ^ c} {u' = b ^ c} {v = c} {v' = c} (dom Γ) body
                (⟶ᵉ-refl (prevalid-nil pv) lc fc))
  where
    lb : LC (b ^ c)
    lb = open-lc {t} {b} {c} ll lc
    fb : fv (b ^ c) ⊑ dom Γ
    fb = fv-open⊑ {b} {c} (fv-lam-body {t} {b} fl) fc
    body : ∀ {x} → x ∉ dom Γ → Γ ∣ s ⊢ ((b ^ c) ^ fvar x) ⟶ᵉ ((b ^ c) ^ fvar x)
    body {x} _ = subst (λ q → Γ ∣ s ⊢ q ⟶ᵉ q) (open-lc-id lb 0 (fvar x)) (⟶ᵉ-refl pv lb fb)
```

## The head path, contracted

In the empty context, for a closed term under a stack of closed operands (`[] ∣ s prevalid` says
exactly that of `s`).

```agda
Closed : Tm → Set
Closed t = fv t ⊑ []

β-spine : ∀ {s t b c} → [] ∣ s prevalid
        → LC (lam t b) → Closed (lam t b) → LC c → Closed c
        → [] ∣ [] ⊢ spine (app (lam t b) c) s ⟶ᵉ* spine (b ^ c) s
β-spine {s} pv ll fl lc fc =
  spine-e {s = s} (β₁ pv ll fl lc fc) ◅ (spine-e {s = s} (β₂ pv ll fl lc fc) ◅ ε (Pv-Nil Pv-Emp))

-- a head path ending in an abstraction: the term reduces to an abstraction
to-lam : ∀ h {n u} (s : Stack) → length s ≡ n → FH h n u
       → [] ∣ s prevalid → LC u → Closed u
       → Reaches (spine u s)
to-lam zero    []      _  fh-fun pv lu fu = _ , _ , ε pv
to-lam (suc h) s       eq (fh-app {u = u} {v = v} p) pv (lc-app lu lv) fu =
  to-lam h (v ∷ s) (cong suc eq) p (Pv-Sta pv lv (fv-app-arg {u} {v} fu)) lu (fv-app-op {u} {v} fu)
to-lam (suc h) (α ∷ s) eq (fh-fop {t = t} {b = b} p) pv ll fl
  with to-lam h s (suc-injective eq) (FH-open 0 α p) (prevalid-pop pv)
              (open-lc {t} {b} {α} ll (prevalid-head-lc pv))
              (fv-open⊑ {b} {α} (fv-lam-body {t} {b} fl) (prevalid-head-fv pv))
... | w , c , r = w , c , (β-spine (prevalid-pop pv) ll fl (prevalid-head-lc pv) (prevalid-head-fv pv) ++ᵉ r)

-- a head path ending in ⊤: the term reduces to ⊤
top-spine : ∀ (s : Stack) → [] ∣ s prevalid → [] ∣ [] ⊢ spine Top s ⟶ᵉ* Top
top-spine []      pv = ε pv
top-spine (v ∷ s) pv = spine-e {s = s} (Me-TAp (prevalid-pop pv)) ◅ top-spine s (prevalid-pop pv)

to-top : ∀ h {n u} (s : Stack) → length s ≡ n → TS h n u
       → [] ∣ s prevalid → LC u → Closed u
       → [] ∣ [] ⊢ spine u s ⟶ᵉ* Top
to-top zero    s       _  ts-top pv lu fu = top-spine s pv
to-top (suc h) s       eq (ts-app {u = u} {v = v} p) pv (lc-app lu lv) fu =
  to-top h (v ∷ s) (cong suc eq) p (Pv-Sta pv lv (fv-app-arg {u} {v} fu)) lu (fv-app-op {u} {v} fu)
to-top (suc h) (α ∷ s) eq (ts-fop {t = t} {b = b} p) pv ll fl =
  β-spine (prevalid-pop pv) ll fl (prevalid-head-lc pv) (prevalid-head-fv pv)
  ++ᵉ to-top h s (suc-injective eq) (TS-open 0 α p) (prevalid-pop pv)
                 (open-lc {t} {b} {α} ll (prevalid-head-lc pv))
                 (fv-open⊑ {b} {α} (fv-lam-body {t} {b} fl) (prevalid-head-fv pv))
```

## `⊤` and an abstraction have no common reduct

```agda
top-red : ∀ {m} → [] ∣ [] ⊢ Top ⟶ᵉ* m → m ≡ Top
top-red (ε _)          = refl
top-red (Me-Top _ ◅ p) = top-red p

data IsLam : Tm → Set where
  is-lam : ∀ {w b} → IsLam (lam w b)

lam-red : ∀ {a m} → IsLam a → [] ∣ [] ⊢ a ⟶ᵉ* m → IsLam m
lam-red il     (ε _)              = il
lam-red is-lam (Me-Fun _ _ _ ◅ p) = lam-red is-lam p

lam≢Top : IsLam Top → ⊥
lam≢Top ()
```

## `NR` is preserved by promotion, and gives `NoAbs`

```agda
NR : Tm → Set
NR t = ∀ {w b} → ¬ ([] ∣ [] ⊢ t ⟶ᵉ* lam w b)

em : ∀ {P : Set} → ¬ ¬ (P ⊎ ¬ P)
em k = k (inj₂ (λ p → k (inj₁ p)))

pv[] : [] ∣ [] prevalid
pv[] = Pv-Nil Pv-Emp

no-sub[] : NoSub []
no-sub[] ()

NR-step : ∀ {t t′} → LC t → Closed t → NR t → [] ∣ [] ⊢ t ⟶ˢ t′ → NR t′
NR-step {t} {t′} lt ft nr st r′ =
  em {∃[ h ] TS h 0 t′} λ where
    (inj₁ (h , ts)) → top-case (to-top h [] refl ts pv[] lt′ ft′)
    (inj₂ ¬ts) → em {∃[ h ] FH h 0 t} λ where
      (inj₁ (h , fh)) → nr (proj₂ (proj₂ (to-lam h [] refl fh pv[] lt ft)))
      (inj₂ ¬fh) →
        nr (promotion-is-e no-sub[] lt ft (λ p → ¬ts (_ , p)) (λ p → ¬fh (_ , p)) st ◅ r′)
  where
    lt′ = ⟶ˢ-lc lt st
    ft′ = fv-⟶ˢ-dom st ft
    top-case : [] ∣ [] ⊢ t′ ⟶ᵉ* Top → ⊥
    top-case c with confluent lt′ r′ c
    ... | m , p , q = lam≢Top (subst IsLam (top-red q) (lam-red is-lam p))

NR⇒NoAbs : ∀ {t} → LC t → Closed t → NR t → NoAbs t
NR⇒NoAbs lt ft nr εˢ        = nr (ε pv[])
NR⇒NoAbs lt ft nr (st ◅ˢ p) =
  NR⇒NoAbs (⟶ˢ-lc lt st) (fv-⟶ˢ-dom st ft) (NR-step lt ft nr st) p
```

## The refutation, with the fifth hypothesis about equivalence reduction only

```agda
refutes-NR : ∀ {f q A B}
           → LC f → LC (lam A B) → LC q → Closed (app f q)
           → [] ⊢ f ≤*wf lam A B
           → [] ⊢ app f q wf
           → [] ⊢ app (lam A B) q wf
           → Reaches (app (lam A B) q)
           → NR (app f q)
           → ¬ Conj-8ʷᶜ
refutes-NR lf lt lq cl f≤t wf-fq wf-tq rt nr =
  refutes lf lt lq f≤t wf-fq wf-tq rt (NR⇒NoAbs (lc-app lf lq) cl nr)
```

## What this establishes

- `promotion-is-e`: in a context without `≤` entries, a promotion whose result does not have `⊤`
  at the end of its head path, and whose source does not have an abstraction at the end of its
  head path with the stack empty, is an equivalence step.
- `to-lam`, `to-top`: a closed term of the second kind reduces to an abstraction, one of the first
  kind to `⊤`.
- `NR-step`, `NR⇒NoAbs`: for closed terms, "no `⟶ᵉ*`-reduct is an abstraction" is preserved by
  promotion, so no chain of promotions ends in an abstraction.
- `refutes-NR`: `¬ Conj-8ʷᶜ` from the four static hypotheses of `MPSS/Conj8NoAbstraction` and
  `NR (f q)`.

For Hurkens' paradox (`MPSS/CONJ8.md` §21) what is left is therefore: the four static facts, and
that no `⟶ᵉ*`-reduct of `[L₀ R₀]` is an abstraction. Neither is mechanized.
