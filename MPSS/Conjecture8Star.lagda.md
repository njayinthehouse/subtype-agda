# Conjecture 8 as printed — over transitive well-subtyping

`MPSS/Conjecture8` states the conjecture over the *single-layer* relation `≤wf`. That is a
misquote. v2's Conjecture 8 reads

> Let `Γ` be a logical context and `u` and `t` be terms such that `Γ ⊢ u ≤*wf t`. Let `Co` be a
> covariant context such that both `Co[u]` and `Co[t]` are well-formed in `Γ`. We conjecture
> that `Γ ⊢ Co[u] ≤*wf Co[t]`.

over the **transitive** relation `≤*wf`, and Lemma 9 in the appendix consumes it in that form.
The two statements are not interchangeable: `≤*wf` admits transitivity through arbitrary
well-formed middle terms, `≤wf` does not, and a proof of the single-layer form does not give the
transitive one (the hypothesis is weaker there). This module restates the conjecture as printed,
redoes the decomposition for it, and shows that the transitive layer costs nothing: the
application congruence needs only its single-layer instance, because a middle term of a
transitive chain applied to the operand is well-formed by the target's function type.

Nothing existing is modified; `MPSS/Conjecture8` is left as the record of the earlier
statement.

```agda
{-# OPTIONS --safe #-}

module MPSS.Conjecture8Star where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import MPSS.WellFormed
open import MPSS.Conjecture8 using (CoCtx; ∙; co-fun; co-app; plug; CoLC; colc-∙; colc-fun;
                                    colc-app; plug-lc; op-wf)
open import PSS.Syntax using (open-lc-id)
```

## The statement

```agda
Conjecture8* : Set
Conjecture8* = ∀ {Γ u t} (C : CoCtx)
             → CoLC C → LC u → LC t
             → Γ ⊢ u ≤*wf t
             → Γ ⊢ plug C u wf
             → Γ ⊢ plug C t wf
             → Γ ⊢ plug C u ≤*wf plug C t
```

## The three pieces, over `≤*wf`

```agda
Weakening* : Set
Weakening* = ∀ {Γ x a u t}
           → x ∉ dom Γ → Γ ⊢ a wf
           → Γ ⊢ u ≤*wf t
           → ((x , sub , a) ∷ Γ) ⊢ u ≤*wf t

FunCongr* : Set
FunCongr* = ∀ {Γ a b b'} (L : List Name)
          → (∀ {x} → x ∉ L → ((x , sub , a) ∷ Γ) ⊢ b ≤*wf b')
          → Γ ⊢ lam a b wf → Γ ⊢ lam a b' wf
          → Γ ⊢ lam a b ≤*wf lam a b'

AppCongr* : Set
AppCongr* = ∀ {Γ f f' v}
          → Γ ⊢ f ≤*wf f'
          → Γ ⊢ app f v wf → Γ ⊢ app f' v wf
          → Γ ⊢ app f v ≤*wf app f' v
```

The induction on the context is the same as before.

```agda
conj8*-from : Weakening* → FunCongr* → AppCongr* → Conjecture8*

conj8*-from wk fc ac ∙ _ _ _ d wfu wft = d

conj8*-from wk fc ac {Γ} {u} {t} (co-fun a C) (colc-fun la cc) lu lt d wfu wft =
  go wfu wft
  where
    go : Γ ⊢ lam a (plug C u) wf → Γ ⊢ lam a (plug C t) wf
       → Γ ⊢ lam a (plug C u) ≤*wf lam a (plug C t)
    go w₁@(Wf-Fun L₁ F₁ da) w₂@(Wf-Fun L₂ F₂ _) = fc (L₁ ++ L₂ ++ dom Γ) fam w₁ w₂
      where
        fam : ∀ {x} → x ∉ (L₁ ++ L₂ ++ dom Γ)
            → ((x , sub , a) ∷ Γ) ⊢ plug C u ≤*wf plug C t
        fam {x} x∉ =
          conj8*-from wk fc ac C cc lu lt
            (wk (∉-++ʳ L₂ (∉-++ʳ L₁ x∉)) da d)
            (subst (λ z → ((x , sub , a) ∷ Γ) ⊢ z wf)
                   (sym (open-lc-id (plug-lc C cc lu) 0 (fvar x)))
                   (F₁ (∉-++ˡ x∉)))
            (subst (λ z → ((x , sub , a) ∷ Γ) ⊢ z wf)
                   (sym (open-lc-id (plug-lc C cc lt) 0 (fvar x)))
                   (F₂ (∉-++ˡ (∉-++ʳ L₁ x∉))))

conj8*-from wk fc ac (co-app C v) (colc-app cc lv) lu lt d wfu wft =
  ac (conj8*-from wk fc ac C cc lu lt d (op-wf wfu) (op-wf wft)) wfu wft
```

## The transitive layer is free

A middle term of a transitive chain, applied to the operand, is well-formed: it is below the
right end of the chain, which is below a function type by well-formedness of the right-hand
application, and the operand is below that function's annotation for the same reason.

```agda
app-wf-mid : ∀ {Γ m f' v}
           → Γ ⊢ m ≤*wf f' → Γ ⊢ m wf
           → Γ ⊢ app f' v wf
           → Γ ⊢ app m v wf
app-wf-mid d wm (Wf-App d₁ d₂) = Wf-App (Ws-Trs d (⊑*wf⇒wfˡ d₁) d₁) d₂
```

So `AppCongr*` follows from its instance at a single `≤wf` layer between well-formed terms.

```agda
AppCongr₁ : Set
AppCongr₁ = ∀ {Γ f f' v}
          → Γ ⊢ f wf → Γ ⊢ f ≤wf f' → Γ ⊢ f' wf
          → Γ ⊢ app f v wf → Γ ⊢ app f' v wf
          → Γ ⊢ app f v ≤*wf app f' v

appcongr-from : AppCongr₁ → AppCongr*
appcongr-from ac (Ws-Sub wf d wf') w w'   = ac wf d wf' w w'
appcongr-from ac (Ws-Trs d₁ wm d₂) w w'   =
  Ws-Trs (appcongr-from ac d₁ w wm') wm' (appcongr-from ac d₂ wm' w')
  where
    wm' = app-wf-mid d₂ wm w'
```

## Where the difficulty now sits

`AppCongr₁` is a statement about one `≤wf` derivation between well-formed terms, at the empty
stack, and the operand `v`. Such a derivation is a sequence of left steps (`Ws-Lf1`, an
equivalence step; `Ws-Lf2`, a promotion step between well-formed terms) and right steps
(`Ws-Rgh`, an equivalence step on the target), in any order, ending in `Ws-Rfl`. Two kinds of
step transfer to the applied terms without difficulty:

- an equivalence step at `[]` transfers to `[v]` (equivalence reduction is stack-monotone:
  `Me-Fun` at `[]` becomes `Me-FOp` at `[v]`, and a body derivation under `x ≤ t` never uses
  `Me-Pro` on `x`, so it is valid under `x ≡ v`), and then `Me-App` lifts it;
- a promotion step by `Ms-Pro`, `Ms-Top`, `Ms-Equ` or `Ms-App` transfers to `[v]` by the same
  rule, with `Ms-App` recursing into its premise at a deeper stack.

The one step that does not transfer is a promotion whose head is an abstraction promoted under
its own binder — `Ms-Fun` at `[]`, or `Ms-FOp` whose body derivation eventually meets `Ms-Fun`
on a nested abstraction. At `[v]` the parameter is bound `x ≡ v` instead of `x ≤ w`, and the body
step must be *replayed* under the new binding. That is the residual:

```agda
FunStep : Set
FunStep = ∀ {Γ w e e' v} (L : List Name)
        → (∀ {x} → x ∉ L → ((x , sub , w) ∷ Γ) ∣ [] ⊢ (e ^ fvar x) ⟶ˢ (e' ^ fvar x))
        → Γ ⊢ lam w e wf → Γ ⊢ lam w e' wf
        → Γ ⊢ app (lam w e) v wf → Γ ⊢ app (lam w e') v wf
        → Γ ⊢ app (lam w e) v ≤*wf app (lam w e') v
```

**The reduction of `AppCongr₁` to `FunStep` is prose, not yet mechanized**, and it needs two
further facts that are unconditional but unbuilt here: stack-monotonicity of `⟶ᵉ`, and the
observation that every promotion intermediate `aᵢ` of the derivation satisfies `aᵢ v wf`, since
`aᵢ` is well-formed (premise of `Ws-Lf2`) and below the target `f'` by the suffix of the same
derivation, and `f'` is below a function type by well-formedness of `f' v`.

**Why `FunStep` is where the circularity lives.** Replaying the body step under `x ≡ v` given
`v ≤*wf w` (which `Wf-App` supplies, up to the inversion lemma) goes through every rule except
`Ms-Pro` on `x` itself, which becomes: unfold `x` to `v` by `Me-Pro`, then relate `Co[v]` to
`Co[w]` for the covariant context `Co` in which `x` was promoted — an instance of Conjecture 8
for a *smaller* context but a *new* pair of terms, whose application congruence again meets a
`FunStep` inside the derivation of `v ≤*wf w`, and so on. Each round descends into a proper
sub-derivation of the well-formedness derivation that supplied the previous round's hypothesis,
so the recursion is plausibly well-founded on the pair of well-formedness derivations of the two
applications — but the terms and derivations it constructs along the way are not sub-objects of
anything, so no structural induction on terms or on a single derivation carries it. That is the
shape a proof would have to take. `MPSS/BetaScope` shows the alternative route, contracting the
redex, is unavailable in the literal system.

## What this establishes

- Conjecture 8 **as printed**, over `≤*wf`, and its decomposition into `Weakening*`,
  `FunCongr*` and `AppCongr*` (`conj8*-from`).
- `AppCongr*` reduces to its single-layer instance `AppCongr₁` (`appcongr-from`), with the
  middle-term well-formedness supplied by `app-wf-mid`. The transitive layer is therefore not
  where the difficulty is.
- The residual `FunStep`, stated exactly, with the reduction of `AppCongr₁` to it recorded as
  prose and owed.
