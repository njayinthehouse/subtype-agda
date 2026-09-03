# MPSS: Lemmas 33, 34 and 35 — congruence

> **Lemma 34 (Congruence of `⟶≤`).** If `Γ;v::s ⊢ u ⟶≤↠ u′` then `Γ;s ⊢ u v ⟶≤↠ u′ v`. If
> `Γ,x≤t;nil ⊢ u ⟶≤↠ u′` then `Γ;nil ⊢ λx≤t.u ⟶≤↠ λx≤t.u′`. If `Γ,x≡α;s ⊢ u ⟶≤↠ u′` then
> `Γ;α::s ⊢ λx≤t.u ⟶≤↠ λx≤t.u′`.
>
> **Lemma 35 (Congruence of `⟶≡`).** The same three, for `⟶≡↠`.
>
> **Lemma 33 (Congruence of `≤`).** The same three, for `≤` and for `≤*`.

The single-step wrapping is already done — `MPSS/Wrap` builds `Me-Fun`, `Ms-Fun`, `Me-FOp` and
`Ms-FOp` instances from a step in the extended context, closing the open term over the witness
name. Because those lemmas close with `closeRec 0 x` on both sides, consecutive steps line up
without any further transport, and the chain versions are a plain map over the chain.

The application case differs between the two relations, and the difference is worth stating.
`Ms-App` carries the operand through untouched, so promotion needs nothing. `Me-App` reduces the
operand too, so keeping it fixed needs `v ⟶≡ v` — reflexivity, at a term the stack holds.
Proposition 18 is false as printed, but this is exactly the case where its repaired form applies:
the derivation's own prevalidity at `v::s` gives `LC v` and `fv v ⊆ dom Γ` through `Pv-Sta`, which
is what `⟶ᵉ-refl` asks for. So Lemma 35 is fine, and it is fine for a reason the paper does not
have available.

**A slip in the paper's Lemma 33.** Its proof reads "we have a term `t` such that
`Γ;v::s ⊢ u ⟶≡↠ t` and `Γ;v::s ⊢ u′ ⟶≤↠ t`", then applies Lemma 35 to the first and Lemma 34 to
the second. The two are the wrong way round: the paper's own definition of `≤` (§1) is that `u ≤ t`
holds iff some `v` has `u ⟶≤↠ v` and `t ⟶≡↠ v` — the *left* side promotes and the right side
equivalence-reduces, which is also what rules `As-Left-1` and `As-Right` say. The conclusion is
unaffected, since both congruences hold; only the attribution is swapped.

The proofs below do not go through the common reduct at all. `⊲` is inductive, so the congruence
is a direct induction that applies the corresponding reduction rule at each node — which makes
Lemma 33 independent of Lemmas 34 and 35 rather than a corollary of them.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Congruence where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Product.Base using (_,_)

open import MPSS.WellFormed
open import MPSS.Scope using (⟶ᵉ-lc; ⟶ˢ-lc)
open import MPSS.StackPush using (⟶ᵉ-refl)
open import MPSS.Push using (_∣_⊢_⟶ˢ*_; εˢ; _◅ˢ_)
open import MPSS.Wrap using (wrapˢ-fun; wrapᵉ-fun; wrapˢ-fop; wrapᵉ-fop)

open import PSS.Syntax using (closeRec; subst-intro; subst-lc)
open import PSS.Close using (open-close; fv-close)
```

## Chains of equivalence steps

`⟶ˢ*` is already in `MPSS/Push`; its counterpart for equivalence reduction is not.

```agda
infixr 5 _◅ᵉ_
infix 3 _∣_⊢_⟶ᵉ*_
data _∣_⊢_⟶ᵉ*_ : Ctx → Stack → Tm → Tm → Set where
  εᵉ   : ∀ {Γ s a} → Γ ∣ s prevalid → Γ ∣ s ⊢ a ⟶ᵉ* a
  _◅ᵉ_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ b → Γ ∣ s ⊢ b ⟶ᵉ* c → Γ ∣ s ⊢ a ⟶ᵉ* c

_++ᵉ_ : ∀ {Γ s a b c} → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s ⊢ b ⟶ᵉ* c → Γ ∣ s ⊢ a ⟶ᵉ* c
εᵉ _     ++ᵉ q = q
(d ◅ᵉ p) ++ᵉ q = d ◅ᵉ (p ++ᵉ q)

⟶ᵉ*-prevalid : ∀ {Γ s a b} → Γ ∣ s ⊢ a ⟶ᵉ* b → Γ ∣ s prevalid
⟶ᵉ*-prevalid (εᵉ pv)  = pv
⟶ᵉ*-prevalid (d ◅ᵉ _) = ⟶ᵉ-prevalid d
```

## Reflexivity at a stack entry

The operand of an application sits on the stack, and prevalidity there is exactly the repaired
Proposition 18's hypothesis.

```agda
refl-head : ∀ {Γ s v} → Γ ∣ (v ∷ s) prevalid → Γ ∣ [] ⊢ v ⟶ᵉ v
refl-head pv = ⟶ᵉ-refl (prevalid-nil pv) (prevalid-head-lc pv) (prevalid-head-fv pv)
```

## Lemma 34 — congruence of promotion

```agda
⟶ˢ*-app : ∀ {Γ s v a c} → Γ ∣ (v ∷ s) ⊢ a ⟶ˢ* c → Γ ∣ s ⊢ app a v ⟶ˢ* app c v
⟶ˢ*-app (εˢ pv)    = εˢ (prevalid-pop pv)
⟶ˢ*-app (d ◅ˢ p)   = Ms-App d ◅ˢ ⟶ˢ*-app p

⟶ˢ*-fun : ∀ {Γ w a c} x → x ∉ dom Γ → LC a
        → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ˢ* c
        → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ˢ* lam w (closeRec 0 x c)
⟶ˢ*-fun x x∉ la (εˢ pv)   = εˢ (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
⟶ˢ*-fun x x∉ la (d ◅ˢ p)  =
  wrapˢ-fun x x∉ la (⟶ˢ-lc la d) d ◅ˢ ⟶ˢ*-fun x x∉ (⟶ˢ-lc la d) p

⟶ˢ*-fop : ∀ {Γ s w α a c} x → x ∉ dom Γ → x ∉ fvStack s → LC a
        → Γ ∣ (α ∷ s) prevalid
        → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ˢ* c
        → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ˢ* lam w (closeRec 0 x c)
⟶ˢ*-fop x x∉ x∉s la pvα (εˢ _)   = εˢ pvα
⟶ˢ*-fop x x∉ x∉s la pvα (d ◅ˢ p) =
  wrapˢ-fop x x∉ x∉s la (⟶ˢ-lc la d) d ◅ˢ ⟶ˢ*-fop x x∉ x∉s (⟶ˢ-lc la d) pvα p
```

## Lemma 35 — congruence of equivalence reduction

```agda
⟶ᵉ*-app : ∀ {Γ s v a c} → Γ ∣ (v ∷ s) ⊢ a ⟶ᵉ* c → Γ ∣ s ⊢ app a v ⟶ᵉ* app c v
⟶ᵉ*-app (εᵉ pv)   = εᵉ (prevalid-pop pv)
⟶ᵉ*-app (d ◅ᵉ p)  = Me-App d (refl-head (⟶ᵉ-prevalid d)) ◅ᵉ ⟶ᵉ*-app p

⟶ᵉ*-fun : ∀ {Γ w a c} x → x ∉ dom Γ → LC a
        → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⟶ᵉ* c
        → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⟶ᵉ* lam w (closeRec 0 x c)
⟶ᵉ*-fun x x∉ la (εᵉ pv)   = εᵉ (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
⟶ᵉ*-fun x x∉ la (d ◅ᵉ p)  =
  wrapᵉ-fun x x∉ la (⟶ᵉ-lc la d) d ◅ᵉ ⟶ᵉ*-fun x x∉ (⟶ᵉ-lc la d) p

⟶ᵉ*-fop : ∀ {Γ s w α a c} x → x ∉ dom Γ → x ∉ fvStack s → LC a
        → LC w → fv w ⊑ dom Γ → Γ ∣ (α ∷ s) prevalid
        → ((x , eqv , α) ∷ Γ) ∣ s ⊢ a ⟶ᵉ* c
        → Γ ∣ (α ∷ s) ⊢ lam w (closeRec 0 x a) ⟶ᵉ* lam w (closeRec 0 x c)
⟶ᵉ*-fop x x∉ x∉s la lw fw pvα (εᵉ _)   = εᵉ pvα
⟶ᵉ*-fop x x∉ x∉s la lw fw pvα (d ◅ᵉ p) =
  wrapᵉ-fop x x∉ x∉s la (⟶ᵉ-lc la d) lw fw d
    ◅ᵉ ⟶ᵉ*-fop x x∉ x∉s (⟶ᵉ-lc la d) lw fw pvα p
```

The `fop` cases carry the target extended context's prevalidity as a hypothesis. A wrapped step
supplies its own, but the empty chain has no step to take it from, and recovering it from the
source would mean strengthening a prevalidity across the removal of a context entry.

## Lemma 33 — congruence of subtyping

Direct induction: each node applies the reduction rule that matches it.

The transitive case needs the local closure of the intermediate term, and `Ast-Trans` does not
record it — nor is it derivable, since `As-Right` lets the right-hand side be any term that
reduces to the one below it, and `Me-Bet` never constrains a redex's annotation. This is an
artefact of the locally nameless encoding rather than a defect in the paper, whose named
presentation has local closure by construction. The relation below is `⊲*` with exactly that
information restored at the transitivity nodes — which is what the well-formed relation already
carries, since `Ws-Trs` has the intermediate's well-formedness as its middle premise.

```agda
infix 3 _∣_⊢_⊲*ᴸ[_]_
data _∣_⊢_⊲*ᴸ[_]_ (Γ : Ctx) (s : Stack) : Tm → Mode → Tm → Set where
  subᴸ : ∀ {a c m} → LC a → LC c → Γ ∣ s ⊢ a ⊲[ m ] c → Γ ∣ s ⊢ a ⊲*ᴸ[ m ] c
  trsᴸ : ∀ {a u c m} → Γ ∣ s ⊢ a ⊲*ᴸ[ m ] u → LC u → Γ ∣ s ⊢ u ⊲*ᴸ[ m ] c
       → Γ ∣ s ⊢ a ⊲*ᴸ[ m ] c

lc-close : ∀ {w a} x → LC w → LC a → LC (lam w (closeRec 0 x a))
lc-close {w} {a} x lw la = lc-lam [] lw body
  where
    body : ∀ {y} → y ∉ [] → LC ((closeRec 0 x a) ^ fvar y)
    body {y} _ rewrite subst-intro {closeRec 0 x a} (lc-fvar {y}) x (fv-close 0 x a)
                     | open-close la 0 x = subst-lc la (lc-fvar {y})
```

```agda
⊲-app : ∀ {Γ s m v a c} → Γ ∣ (v ∷ s) ⊢ a ⊲[ m ] c → Γ ∣ s ⊢ app a v ⊲[ m ] app c v
⊲-app (As-Refl pv)      = As-Refl (prevalid-pop pv)
⊲-app (As-Left-1 st d)  = As-Left-1 (Ms-App st) (⊲-app d)
⊲-app (As-Left-2 e d)   = As-Left-2 (Me-App e (refl-head (⟶ᵉ-prevalid e))) (⊲-app d)
⊲-app (As-Right d e)    = As-Right (⊲-app d) (Me-App e (refl-head (⟶ᵉ-prevalid e)))

⊲*-app : ∀ {Γ s m v a c} → Γ ∣ (v ∷ s) ⊢ a ⊲*[ m ] c → Γ ∣ s ⊢ app a v ⊲*[ m ] app c v
⊲*-app (Ast-Sub d)       = Ast-Sub (⊲-app d)
⊲*-app (Ast-Trans d₁ d₂) = Ast-Trans (⊲*-app d₁) (⊲*-app d₂)

⊲-fun : ∀ {Γ m w a c} x → x ∉ dom Γ → LC a → LC c
      → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⊲[ m ] c
      → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⊲[ m ] lam w (closeRec 0 x c)
⊲-fun x x∉ la lc (As-Refl pv)     = As-Refl (Pv-Nil (tail-prevalid (prevalid-ctx pv)))
⊲-fun x x∉ la lc (As-Left-1 st d) =
  As-Left-1 (wrapˢ-fun x x∉ la (⟶ˢ-lc la st) st) (⊲-fun x x∉ (⟶ˢ-lc la st) lc d)
⊲-fun x x∉ la lc (As-Left-2 e d)  =
  As-Left-2 (wrapᵉ-fun x x∉ la (⟶ᵉ-lc la e) e) (⊲-fun x x∉ (⟶ᵉ-lc la e) lc d)
⊲-fun x x∉ la lc (As-Right d e)   =
  As-Right (⊲-fun x x∉ la (⟶ᵉ-lc lc e) d) (wrapᵉ-fun x x∉ lc (⟶ᵉ-lc lc e) e)

⊲*-fun : ∀ {Γ m w a c} x → x ∉ dom Γ → LC w
       → ((x , sub , w) ∷ Γ) ∣ [] ⊢ a ⊲*ᴸ[ m ] c
       → Γ ∣ [] ⊢ lam w (closeRec 0 x a) ⊲*ᴸ[ m ] lam w (closeRec 0 x c)
⊲*-fun x x∉ lw (subᴸ la lc d) =
  subᴸ (lc-close x lw la) (lc-close x lw lc) (⊲-fun x x∉ la lc d)
⊲*-fun x x∉ lw (trsᴸ d₁ lu d₂) =
  trsᴸ (⊲*-fun x x∉ lw d₁) (lc-close x lw lu) (⊲*-fun x x∉ lw d₂)
```

## What this establishes

Lemmas 34 and 35 for the application and abstraction cases, and Lemma 33 in both the single-step
and transitive readings, all unconditionally. `⊲-lc` and `⊲*-lc` — subtyping preserves local
closure on the right — fall out of the same induction.
