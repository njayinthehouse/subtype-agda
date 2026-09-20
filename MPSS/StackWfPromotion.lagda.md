# MPSS, candidate C: the machine's two reductions and the stack-reading well-formedness

For the judgements of `MPSS/StackWf`.

**Proved.**

- `⟶ᵉ-wfˢ`: equivalence reduction preserves `wfˢ`, at every configuration. It is the instance at
  `Ct-Refl` of `⟶ᵉ-wfˢ-↣`, where the context and the stack are reduced (`↣`, Figure 3) in the same
  move as the term. The general form is what the induction needs: `Me-App` reduces the operand,
  which is an entry of the stack at which the operator is checked, and `Me-Fun` reduces the
  annotation under which the body is checked. `WfStep` of `MPSS/StackWfNarrow` is not available
  for a `⟶ᵉ` step, because a `⟶ᵉ` step reads the context (`Me-Pro`) and so does not keep
  well-formedness at *every* configuration.
- `⟶ˢ-wfˢ`, as a statement about all of `⟶ˢ`, is **false**: `¬⟶ˢ-wfˢ`. `(λx≤⊤. x) ⊤` is `wfˢ`,
  promotes by `Ms-App (Ms-Top)` to `⊤ ⊤`, and `⊤ ⊤` is not `wfˢ` (`Thm-11ˢ`).
- What promotion does keep is a judgement `wf⁻` with premises of `wfˢ` dropped: nothing is asked of
  the body of an abstraction at the empty stack, nor of the annotation of one that meets an
  operand, nor of an operator against its operand's bound. `wfˢ` implies it (`K-Wf`), both
  reductions preserve it (`⟶ˢ-wf⁻`, `⟶ᵉ-wf⁻-↣`), and an abstraction at the empty stack that
  satisfies it has a `wfˢ` annotation.
- `reach-lam-wfˢ`: if `f` is `wfˢ` at `Γ ∣ []` and `Γ ∣ [] ⊢ f ≤ lam d Top`, then `d` reduces by a
  chain of `⟶ᵉ` steps to some `d′` that is `wfˢ` at `Γ ∣ []`, and `Γ ∣ [] ⊢ f ≤ lam d′ Top`.
  Hypotheses beyond those two: `d` locally closed and scoped in `Γ`. They are not derivable from
  the machine relation (`Me-TAp` discards an arbitrary operand), and are used only for the last
  conjunct.

Nothing is assumed. Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.StackWfPromotion where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import MPSS.Subtyping
open import MPSS.StackWf
open import MPSS.StackWfNarrow using (wfˢ-fv)
open import MPSS.StackWfSubst using (wfˢ-subst≡; wfˢ-subst≡-head)
open import MPSS.StackWfExample using (id⊤; wf-redex; pv₁)
open import MPSS.CtxReduction
open import MPSS.CtxReduce using (↣-nil; ↣-sub; ↣-eqv; ↣-empty)
open import MPSS.CtxPrevalid using (↣-prevalid)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Preserve using (ann-unique; fv-⟶ᵉ-dom)
open import MPSS.StackPush using (⟶ᵉ-refl; pushᵉ; prevalid-cons)
open import MPSS.Weakening using (⟶ᵉ-weaken)
open import MPSS.MachineNarrow using (≤-↣)
open import MPSS.Congruence using (subᴸ; trsᴸ)
open import MPSS.VariantTransfer using (Thm-3ᴸ)
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_)
open import MPSS.EvalChain using (lam-l-chain; chain⇒≤)
open import MPSS.Rename using (substCtx; substStack; substStack-id)
open import PSS.Syntax using (subst-open; subst-fvar-≢; subst-intro; ∉-tail)
```

## Lookups and context reductions

A prevalid context binds a name once, so a name has one kind of annotation.

```agda
kind-clash : ∀ {Γ x t α} → Γ prevalid → x ≤ t ∈ Γ → x ≐ α ∈ Γ → ⊥
kind-clash (Pv-Ctx _ x∉ _ _) (here refl) (there n) = x∉ (∈-dom n)
kind-clash (Pv-Ctx pv _ _ _) (there m)   (there n) = kind-clash pv m n
kind-clash (Pv-EqA _ x∉ _ _) (there m)   (here refl) = x∉ (∈-dom m)
kind-clash (Pv-EqA pv _ _ _) (there m)   (there n) = kind-clash pv m n
```

A context reduction under a non-empty stack reduces the head of the stack and the rest. The
head's step is taken at some tail of the context (`Ct-Ann` passes to the tail), so it is returned
weakened into a context `Γ₁` of the caller's choice.

```agda
↣-cons : ∀ {Γ Γ₁ δ s Γ′ s″}
       → (∀ {a b} → Γ ∣ [] ⊢ a ⟶ᵉ b → Γ₁ ∣ [] ⊢ a ⟶ᵉ b)
       → Γ prevalid → Γ₁ prevalid → LC δ → fv δ ⊑ dom Γ₁
       → Γ ∣ (δ ∷ s) ↣ Γ′ ∣ s″
       → ∃[ δ′ ] ∃[ s′ ] ((s″ ≡ δ′ ∷ s′) × (Γ ∣ s ↣ Γ′ ∣ s′) × (Γ₁ ∣ [] ⊢ δ ⟶ᵉ δ′))
↣-cons {δ = δ} {s} wk pv pv₁ lδ fδ Ct-Refl =
  δ , s , refl , Ct-Refl , ⟶ᵉ-refl (Pv-Nil pv₁) lδ fδ
↣-cons wk pv pv₁ lδ fδ (Ct-Stk c e) = _ , _ , refl , c , wk e
↣-cons wk pv pv₁ lδ fδ (Ct-Ann {x = y} {c = k} {t = t₀} c e)
  with ↣-cons (λ h → wk (⟶ᵉ-weaken [] ((y , k , t₀) ∷ []) (Pv-Nil pv) h))
              (tail-prevalid pv) pv₁ lδ fδ c
... | δ′ , s′ , refl , c′ , e′ = δ′ , s′ , refl , Ct-Ann c′ e , e′

↣-cons′ : ∀ {Γ δ s Γ′ s″} → Γ ∣ (δ ∷ s) prevalid
        → Γ ∣ (δ ∷ s) ↣ Γ′ ∣ s″
        → ∃[ δ′ ] ∃[ s′ ] ((s″ ≡ δ′ ∷ s′) × (Γ ∣ s ↣ Γ′ ∣ s′) × (Γ ∣ [] ⊢ δ ⟶ᵉ δ′))
↣-cons′ pv cr =
  ↣-cons (λ h → h) (prevalid-ctx pv) (prevalid-ctx pv) (prevalid-head-lc pv) (prevalid-head-fv pv) cr
```

## The machine relation after a step of its left end, in a reduced configuration

The reduct is below the redex (`As-Right`), transitivity is `Thm-3ᴸ`, and the machine relation
follows a context reduction by `≤-↣`.

```agda
≤-after : ∀ {Γ s Γ′ s′ u u′ t}
        → LC u → fv u ⊑ dom Γ → LC t → fv t ⊑ dom Γ
        → Γ ∣ s ⊢ u ≤ t → Γ ∣ s ⊢ u ⟶ᵉ u′ → Γ ∣ s ↣ Γ′ ∣ s′
        → Γ′ ∣ s′ ⊢ u′ ≤ t
≤-after lu fu lt ft d e cr =
  ≤-↣ lu′ lt (fv-⟶ᵉ-dom e fu) ft cr
      (Thm-3ᴸ (trsᴸ (subᴸ lu′ lu (As-Right (As-Refl (⟶ᵉ-prevalid e)) e)) lu (subᴸ lu lt d)))
  where
    lu′ = ⟶ᵉ-lc lu e
```

## Equivalence reduction preserves `wfˢ`

By induction on the well-formedness derivation; the context and stack are reduced along with the
term.

- `Wc-PrS`, `Wc-PrE` against `Me-Var`: the annotation in the reduced context is a reduct of the
  old one (`↣-sub`, `↣-eqv`), by a step at the empty stack that `pushᵉ` moves under the stack in
  hand; the induction hypothesis on the annotation's derivation applies to that step.
- `Wc-PrE` against `Me-Pro`: the induction hypothesis on the annotation's derivation, with the
  premise of `Me-Pro`.
- `Wc-Fun`, `Wc-FOp`: the body is under an entry whose annotation — the abstraction's, or the
  operand — takes a step, which is `Ct-Ann`.
- `Wc-App` against `Me-App`: the operator is checked at the stack whose head is the operand; the
  operand's step is `Ct-Stk`. Both ends of the two well-subtypings are well-formed in the reduced
  configuration by the induction hypothesis (the right ends by a reflexive step), and the machine
  relation is `≤-after`.
- `Wc-App` against `Me-Bet`: the operator is an abstraction well-formed by `Wc-FOp`, its body under
  `x ≡ v`. The body's step is weakened by that entry, the entry's operand takes its step by
  `Ct-Ann`, and `wfˢ-subst≡-head` substitutes.
- `Wc-App` against `Me-TAp`: `⊤` is below no abstraction (`Thm-11ˢ`).

```agda
⟶ᵉ-wfˢ-↣ : ∀ {Γ s Γ′ s′ u u′}
          → Γ ∣ s ⊢ u wfˢ → Γ ∣ s ↣ Γ′ ∣ s′ → Γ ∣ s ⊢ u ⟶ᵉ u′ → Γ′ ∣ s′ ⊢ u′ wfˢ
⟶ᵉ-≤*wfˢˡ : ∀ {Γ s Γ′ s′ u u′ t}
          → Γ ∣ s ⊢ u ≤*wfˢ t → Γ ∣ s ↣ Γ′ ∣ s′ → Γ ∣ s ⊢ u ⟶ᵉ u′ → Γ′ ∣ s′ ⊢ u′ wfˢ
⟶ᵉ-≤*wfˢʳ : ∀ {Γ s Γ′ s′ u t t′}
          → Γ ∣ s ⊢ u ≤*wfˢ t → Γ ∣ s ↣ Γ′ ∣ s′ → Γ ∣ s ⊢ t ⟶ᵉ t′ → Γ′ ∣ s′ ⊢ t′ wfˢ
⟶ᵉ-β : ∀ {Γ s Γ′ s′ a b b′ v v′ T} (L′ : List Name)
      → Γ ∣ (v ∷ s) ⊢ lam a b ≤*wfˢ T → Γ ∣ s ↣ Γ′ ∣ s′
      → (∀ {x} → x ∉ L′ → Γ ∣ s ⊢ (b ^ fvar x) ⟶ᵉ (b′ ^ fvar x))
      → Γ ∣ [] ⊢ v ⟶ᵉ v′
      → Γ′ ∣ s′ ⊢ (b′ ^ v′) wfˢ

⟶ᵉ-≤*wfˢˡ (Wc-Sub (Wc-Rule wu _ _)) cr e = ⟶ᵉ-wfˢ-↣ wu cr e
⟶ᵉ-≤*wfˢˡ (Wc-Trs d _)              cr e = ⟶ᵉ-≤*wfˢˡ d cr e

⟶ᵉ-≤*wfˢʳ (Wc-Sub (Wc-Rule _ wt _)) cr e = ⟶ᵉ-wfˢ-↣ wt cr e
⟶ᵉ-≤*wfˢʳ (Wc-Trs _ d)              cr e = ⟶ᵉ-≤*wfˢʳ d cr e

⟶ᵉ-β {b′ = b′} L′ (Wc-Trs d _) cr Fb dv = ⟶ᵉ-β {b′ = b′} L′ d cr Fb dv
⟶ᵉ-β {Γ} {s} {Γ′} {s′} {b′ = b′} {v = v} L′ (Wc-Sub (Wc-Rule (Wc-FOp L F _) _ _)) cr Fb dv =
  wfˢ-subst≡-head {u = b′} x x∉b′ x∉s′
    (⟶ᵉ-wfˢ-↣ (F x∉L) (Ct-Ann cr dv)
               (⟶ᵉ-weaken [] ((x , eqv , v) ∷ []) (wfˢ⇒prevalid (F x∉L)) (Fb x∉L′)))
  where
    A  = L ++ L′ ++ fv b′ ++ fvStack s′
    x  = fresh A
    a∉ = fresh-∉ A
    x∉L  = ∉-++ˡ a∉
    x∉L′ = ∉-++ˡ (∉-++ʳ L a∉)
    x∉b′ : x ∉ fv b′
    x∉b′ = ∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L a∉))
    x∉s′ : x ∉ fvStack s′
    x∉s′ = ∉-++ʳ (fv b′) (∉-++ʳ L′ (∉-++ʳ L a∉))

⟶ᵉ-wfˢ-↣ (Wc-Top pv) cr (Me-Top _) = Wc-Top (↣-prevalid pv cr)

⟶ᵉ-wfˢ-↣ (Wc-PrS pv m wt) cr (Me-Var _) with ↣-sub (prevalid-ctx pv) cr m
... | t′ , m′ , e = Wc-PrS (↣-prevalid pv cr) m′ (⟶ᵉ-wfˢ-↣ wt cr (pushᵉ e pv))
⟶ᵉ-wfˢ-↣ (Wc-PrS pv m wt) cr (Me-Pro _ m′ _) = ⊥-elim (kind-clash (prevalid-ctx pv) m m′)

⟶ᵉ-wfˢ-↣ (Wc-PrE pv m wα) cr (Me-Var _) with ↣-eqv (prevalid-ctx pv) cr m
... | α′ , m′ , e = Wc-PrE (↣-prevalid pv cr) m′ (⟶ᵉ-wfˢ-↣ wα cr (pushᵉ e pv))
⟶ᵉ-wfˢ-↣ (Wc-PrE pv m wα) cr (Me-Pro _ m′ d) with ann-unique (prevalid-ctx pv) m m′
... | refl = ⟶ᵉ-wfˢ-↣ wα cr d

⟶ᵉ-wfˢ-↣ (Wc-Fun L F wt) cr (Me-Fun L′ d F′) with ↣-nil cr
... | refl = Wc-Fun (L ++ L′)
                    (λ x∉ → ⟶ᵉ-wfˢ-↣ (F (∉-++ˡ x∉)) (Ct-Ann cr d) (F′ (∉-++ʳ L x∉)))
                    (⟶ᵉ-wfˢ-↣ wt cr d)

⟶ᵉ-wfˢ-↣ (Wc-FOp L F wt) cr st@(Me-FOp L′ d F′)
  with ↣-cons′ (⟶ᵉ-prevalid st) cr
... | δ′ , s′ , refl , cr₀ , e =
  Wc-FOp (L ++ L′)
         (λ x∉ → ⟶ᵉ-wfˢ-↣ (F (∉-++ˡ x∉)) (Ct-Ann cr₀ e) (F′ (∉-++ʳ L x∉)))
         (⟶ᵉ-wfˢ-↣ wt (↣-empty cr) d)

⟶ᵉ-wfˢ-↣ (Wc-App d₁ d₂) cr (Me-TAp _) = ⊥-elim (Thm-11ˢ d₁)

⟶ᵉ-wfˢ-↣ (Wc-App d₁ d₂) cr (Me-Bet {u' = b′} L′ Fb dv) = ⟶ᵉ-β {b′ = b′} L′ d₁ cr Fb dv

⟶ᵉ-wfˢ-↣ (Wc-App d₁ d₂) cr (Me-App du dv) =
  Wc-App (Wc-Sub (Wc-Rule (⟶ᵉ-≤*wfˢˡ d₁ cr₁ du)
                          (⟶ᵉ-≤*wfˢʳ d₁ cr₁ (⟶ᵉ-refl pv₁′ lλ fλ))
                          (≤-after lu fu lλ fλ (Thm-3ˢ d₁) du cr₁)))
         (Wc-Sub (Wc-Rule (⟶ᵉ-≤*wfˢˡ d₂ cr₀ dv)
                          (⟶ᵉ-≤*wfˢʳ d₂ cr₀ (⟶ᵉ-refl pv₀ lt ft))
                          (≤-after lv fv-v lt ft (Thm-3ˢ d₂) dv cr₀)))
  where
    cr₁ = Ct-Stk cr dv
    cr₀ = ↣-empty cr
    wu  = proj₁ (≤*wfˢ⇒both d₁)
    wλ  = proj₂ (≤*wfˢ⇒both d₁)
    wv  = proj₁ (≤*wfˢ⇒both d₂)
    wt  = proj₂ (≤*wfˢ⇒both d₂)
    pv₁′ = wfˢ⇒prevalid wu
    pv₀ = wfˢ⇒prevalid wv
    lu = wfˢ⇒lc wu
    fu = wfˢ-fv wu
    lλ = wfˢ⇒lc wλ
    fλ = wfˢ-fv wλ
    lv = wfˢ⇒lc wv
    fv-v = wfˢ-fv wv
    lt = wfˢ⇒lc wt
    ft = wfˢ-fv wt
```

At a fixed configuration:

```agda
⟶ᵉ-wfˢ : ∀ {Γ s u u′} → Γ ∣ s ⊢ u wfˢ → Γ ∣ s ⊢ u ⟶ᵉ u′ → Γ ∣ s ⊢ u′ wfˢ
⟶ᵉ-wfˢ w e = ⟶ᵉ-wfˢ-↣ w Ct-Refl e
```

## Subtyping reduction does not preserve `wfˢ`

`Ms-Top` applies in operator position, under `Ms-App`; `⊤` applied to anything is not `wfˢ`.

```agda
¬wfˢ-Top-app : ∀ {Γ s v} → ¬ (Γ ∣ s ⊢ app Top v wfˢ)
¬wfˢ-Top-app (Wc-App d₁ _) = Thm-11ˢ d₁

¬⟶ˢ-wfˢ : ¬ (∀ {Γ s u u′} → Γ ∣ s ⊢ u wfˢ → Γ ∣ s ⊢ u ⟶ˢ u′ → Γ ∣ s ⊢ u′ wfˢ)
¬⟶ˢ-wfˢ h = ¬wfˢ-Top-app (h wf-redex (Ms-App {u = id⊤} (Ms-Top pv₁)))
```

## What subtyping reduction keeps

`wfˢ` with premises dropped. `K-Fun` asks nothing of the body; `K-FOp` nothing of the annotation;
`K-App` asks the operand well-formed and nothing of the operator beyond this judgement at the
stack holding the operand.

```agda
infix 3 _∣_⊢_wf⁻

data _∣_⊢_wf⁻ : Ctx → Stack → Tm → Set where

  K-Wf  : ∀ {Γ s u}
        → Γ ∣ s ⊢ u wfˢ
        → Γ ∣ s ⊢ u wf⁻

  K-Fun : ∀ {Γ t u}
        → Γ ∣ [] ⊢ t wfˢ
        → Γ ∣ [] ⊢ lam t u wf⁻

  K-FOp : ∀ {Γ s δ t u} (L : List Name)
        → (∀ {x} → x ∉ L → ((x , eqv , δ) ∷ Γ) ∣ s ⊢ (u ^ fvar x) wf⁻)
        → Γ ∣ (δ ∷ s) ⊢ lam t u wf⁻

  K-App : ∀ {Γ s u v}
        → Γ ∣ (v ∷ s) ⊢ u wf⁻
        → Γ ∣ [] ⊢ v wfˢ
        → Γ ∣ s ⊢ app u v wf⁻
```

An abstraction at the empty stack has a well-formed annotation.

```agda
wf⁻-lam : ∀ {Γ t u} → Γ ∣ [] ⊢ lam t u wf⁻ → Γ ∣ [] ⊢ t wfˢ
wf⁻-lam (K-Wf (Wc-Fun _ _ wt)) = wt
wf⁻-lam (K-Fun wt)             = wt
```

### Substitution for a parameter bound to its operand

`wfˢ-subst≡` of `MPSS/StackWfSubst`, for `wf⁻`. Local closure of the operand is a hypothesis
because `wf⁻` does not carry prevalidity.

```agda
wf⁻-subst≡ : ∀ (Δ : Ctx) {Γ s t v} x → LC v
           → (Δ ++ (x , eqv , v) ∷ Γ) ∣ s ⊢ t wf⁻
           → (substCtx x v Δ ++ Γ) ∣ (substStack x v s) ⊢ (t [ x := v ]) wf⁻
wf⁻-subst≡ Δ x lv (K-Wf w)     = K-Wf (wfˢ-subst≡ Δ x w)
wf⁻-subst≡ Δ x lv (K-Fun wt)   = K-Fun (wfˢ-subst≡ Δ x wt)
wf⁻-subst≡ Δ x lv (K-App wu wv) = K-App (wf⁻-subst≡ Δ x lv wu) (wfˢ-subst≡ Δ x wv)
wf⁻-subst≡ Δ {Γ} {v = v} x lv (K-FOp {s = s} {δ = δ} {u = u} L F) = K-FOp (x ∷ L) body
  where
    body : ∀ {z} → z ∉ (x ∷ L)
         → ((z , eqv , δ [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
             ⊢ ((u [ x := v ]) ^ fvar z) wf⁻
    body {z} z∉ = transport (wf⁻-subst≡ ((z , eqv , δ) ∷ Δ) x lv (F (∉-tail z∉)))
      where
        x≢z : x ≢ z
        x≢z p = z∉ (here (sym p))
        eq  = trans (subst-open lv 0 (fvar z) u x)
                    (cong (λ w → openRec 0 w (u [ x := v ])) (subst-fvar-≢ v x≢z))
        transport : ((z , eqv , δ [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u ^ fvar z) [ x := v ]) wf⁻
                  → ((z , eqv , δ [ x := v ]) ∷ substCtx x v Δ ++ Γ) ∣ (substStack x v s)
                      ⊢ ((u [ x := v ]) ^ fvar z) wf⁻
        transport h rewrite sym eq = h

wf⁻-subst≡-head : ∀ {Γ s u v} x → LC v
                → x ∉ fv u → x ∉ fvStack s
                → ((x , eqv , v) ∷ Γ) ∣ s ⊢ (u ^ fvar x) wf⁻
                → Γ ∣ s ⊢ (u ^ v) wf⁻
wf⁻-subst≡-head {Γ} {s} {u} {v} x lv x∉u x∉s w =
  subst (λ σ → Γ ∣ σ ⊢ (u ^ v) wf⁻) (substStack-id x v s x∉s) step
  where
    step : Γ ∣ (substStack x v s) ⊢ (u ^ v) wf⁻
    step = subst (λ q → Γ ∣ (substStack x v s) ⊢ q wf⁻)
                 (sym (subst-intro {u} lv x x∉u)) (wf⁻-subst≡ [] x lv w)
```

### Equivalence reduction preserves `wf⁻`

As `⟶ᵉ-wfˢ-↣`, which supplies every case on a `wfˢ` premise.

```agda
⟶ᵉ-wf⁻-↣ : ∀ {Γ s Γ′ s′ u u′}
          → Γ ∣ s ⊢ u wf⁻ → Γ ∣ s ↣ Γ′ ∣ s′ → Γ ∣ s ⊢ u ⟶ᵉ u′ → Γ′ ∣ s′ ⊢ u′ wf⁻
⟶ᵉ-wf⁻-↣ (K-Wf w) cr e = K-Wf (⟶ᵉ-wfˢ-↣ w cr e)

⟶ᵉ-wf⁻-↣ (K-Fun wt) cr (Me-Fun L d F) with ↣-nil cr
... | refl = K-Fun (⟶ᵉ-wfˢ-↣ wt cr d)

⟶ᵉ-wf⁻-↣ (K-FOp L F) cr st@(Me-FOp L′ d F′)
  with ↣-cons′ (⟶ᵉ-prevalid st) cr
... | δ′ , s′ , refl , cr₀ , e =
  K-FOp (L ++ L′) (λ x∉ → ⟶ᵉ-wf⁻-↣ (F (∉-++ˡ x∉)) (Ct-Ann cr₀ e) (F′ (∉-++ʳ L x∉)))

⟶ᵉ-wf⁻-↣ (K-App wu wv) cr (Me-App du dv) =
  K-App (⟶ᵉ-wf⁻-↣ wu (Ct-Stk cr dv) du) (⟶ᵉ-wfˢ-↣ wv (↣-empty cr) dv)

⟶ᵉ-wf⁻-↣ (K-App wu wv) cr (Me-TAp pv) = K-Wf (Wc-Top (↣-prevalid pv cr))

⟶ᵉ-wf⁻-↣ {Γ} {s} {Γ′} {s′} (K-App {v = v} (K-Wf (Wc-FOp L F _)) wv) cr
          (Me-Bet {u' = b′} L′ Fb dv) =
  K-Wf (wfˢ-subst≡-head {u = b′} x x∉b′ x∉s′
         (⟶ᵉ-wfˢ-↣ (F x∉L) (Ct-Ann cr dv)
                    (⟶ᵉ-weaken [] ((x , eqv , v) ∷ []) (wfˢ⇒prevalid (F x∉L)) (Fb x∉L′))))
  where
    A  = L ++ L′ ++ fv b′ ++ fvStack s′
    x  = fresh A
    a∉ = fresh-∉ A
    x∉L  = ∉-++ˡ a∉
    x∉L′ = ∉-++ˡ (∉-++ʳ L a∉)
    x∉b′ : x ∉ fv b′
    x∉b′ = ∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L a∉))
    x∉s′ : x ∉ fvStack s′
    x∉s′ = ∉-++ʳ (fv b′) (∉-++ʳ L′ (∉-++ʳ L a∉))

⟶ᵉ-wf⁻-↣ {Γ} {s} {Γ′} {s′} (K-App {v = v} (K-FOp L F) wv) cr
          (Me-Bet {u' = b′} {v' = v′} L′ Fb dv) =
  wf⁻-subst≡-head {u = b′} x (⟶ᵉ-lc lv dv) x∉b′ x∉s′
    (⟶ᵉ-wf⁻-↣ (F x∉L) (Ct-Ann cr dv)
               (⟶ᵉ-weaken [] ((x , eqv , v) ∷ []) pvx (Fb x∉L′)))
  where
    A  = L ++ L′ ++ fv b′ ++ fvStack s′ ++ dom Γ
    x  = fresh A
    a∉ = fresh-∉ A
    x∉L  = ∉-++ˡ a∉
    x∉L′ = ∉-++ˡ (∉-++ʳ L a∉)
    x∉b′ : x ∉ fv b′
    x∉b′ = ∉-++ˡ (∉-++ʳ L′ (∉-++ʳ L a∉))
    x∉s′ : x ∉ fvStack s′
    x∉s′ = ∉-++ˡ (∉-++ʳ (fv b′) (∉-++ʳ L′ (∉-++ʳ L a∉)))
    x∉Γ : x ∉ dom Γ
    x∉Γ = ∉-++ʳ (fvStack s′) (∉-++ʳ (fv b′) (∉-++ʳ L′ (∉-++ʳ L a∉)))
    lv  = wfˢ⇒lc wv
    pvx : ((x , eqv , v) ∷ Γ) ∣ s prevalid
    pvx = prevalid-cons (⟶ᵉ-prevalid (Fb x∉L′)) x∉Γ lv (wfˢ-fv wv)

⟶ᵉ-wf⁻ : ∀ {Γ s u u′} → Γ ∣ s ⊢ u wf⁻ → Γ ∣ s ⊢ u ⟶ᵉ u′ → Γ ∣ s ⊢ u′ wf⁻
⟶ᵉ-wf⁻ w e = ⟶ᵉ-wf⁻-↣ w Ct-Refl e
```

### Subtyping reduction preserves `wf⁻`

By induction on the step. `Ms-Pro`: the annotation is well-formed at the same stack, which
`Wc-PrS` carries. `Ms-Top`: `Wc-Top`. `Ms-Equ`: above. `Ms-App`: the operator, at the stack holding
the operand; the operand is untouched. `Ms-Fun`: the annotation is untouched and nothing is asked
of the body. `Ms-FOp`: the body.

```agda
⟶ˢ-wf⁻ : ∀ {Γ s u u′} → Γ ∣ s ⊢ u wf⁻ → Γ ∣ s ⊢ u ⟶ˢ u′ → Γ ∣ s ⊢ u′ wf⁻
⟶ˢ-wf⁻ w (Ms-Top pv)   = K-Wf (Wc-Top pv)
⟶ˢ-wf⁻ w (Ms-Equ _ e)  = ⟶ᵉ-wf⁻ w e
⟶ˢ-wf⁻ (K-Wf (Wc-PrS pv m wt)) (Ms-Pro _ m′) with ann-unique (prevalid-ctx pv) m m′
... | refl = K-Wf wt
⟶ˢ-wf⁻ (K-Wf (Wc-PrE pv m _)) (Ms-Pro _ m′) = ⊥-elim (kind-clash (prevalid-ctx pv) m′ m)
⟶ˢ-wf⁻ (K-Wf (Wc-App d₁ d₂)) (Ms-App st) =
  K-App (⟶ˢ-wf⁻ (K-Wf (proj₁ (≤*wfˢ⇒both d₁))) st) (proj₁ (≤*wfˢ⇒both d₂))
⟶ˢ-wf⁻ (K-App wu wv) (Ms-App st) = K-App (⟶ˢ-wf⁻ wu st) wv
⟶ˢ-wf⁻ (K-Wf (Wc-Fun _ _ wt)) (Ms-Fun _ _) = K-Fun wt
⟶ˢ-wf⁻ (K-Fun wt) (Ms-Fun _ _) = K-Fun wt
⟶ˢ-wf⁻ (K-Wf (Wc-FOp L F _)) (Ms-FOp L′ F′) =
  K-FOp (L ++ L′) (λ x∉ → ⟶ˢ-wf⁻ (K-Wf (F (∉-++ˡ x∉))) (F′ (∉-++ʳ L x∉)))
⟶ˢ-wf⁻ (K-FOp L F) (Ms-FOp L′ F′) =
  K-FOp (L ++ L′) (λ x∉ → ⟶ˢ-wf⁻ (F (∉-++ˡ x∉)) (F′ (∉-++ʳ L x∉)))
```

## An abstraction above a well-formed term, at the empty stack

Along the machine derivation: the left end keeps `wf⁻` under `As-Left-1`; the right end, an
abstraction at the empty stack, steps by `Me-Fun`, whose first premise is a step of the
annotation. At `As-Refl` the two ends are the same abstraction, and its annotation is `wfˢ`.

```agda
reach-lam : ∀ {Γ f d c} → Γ ∣ [] ⊢ f wf⁻ → Γ ∣ [] ⊢ f ≤ lam d c
          → ∃[ d′ ] ((Γ ∣ [] ⊢ d ⟶ᵉ* d′) × (Γ ∣ [] ⊢ d′ wfˢ))
reach-lam {d = d} w (As-Refl pv)               = d , ε pv , wf⁻-lam w
reach-lam w (As-Left-1 st r)                   = reach-lam (⟶ˢ-wf⁻ w st) r
reach-lam w (As-Right r (Me-Fun L e F)) with reach-lam w r
... | d′ , p , wd′ = d′ , e ◅ p , wd′
```

With the machine relation to the new abstraction: `lam d Top` reduces to `lam d′ Top` by
`lam-l-chain`, a chain is a machine derivation (`chain⇒≤`), and transitivity is `Thm-3ᴸ`.

```agda
reach-lam-wfˢ : ∀ {Γ f d} → LC d → fv d ⊑ dom Γ
              → Γ ∣ [] ⊢ f wfˢ → Γ ∣ [] ⊢ f ≤ lam d Top
              → ∃[ d′ ] ((Γ ∣ [] ⊢ d ⟶ᵉ* d′) × (Γ ∣ [] ⊢ d′ wfˢ) × (Γ ∣ [] ⊢ f ≤ lam d′ Top))
reach-lam-wfˢ {Γ} {f} {d} ld fd wf r with reach-lam (K-Wf wf) r
... | d′ , p , wd′ = d′ , p , wd′ , Thm-3ᴸ (trsᴸ (subᴸ lf lλ r) lλ (subᴸ lλ lλ′ up))
  where
    pv = wfˢ⇒prevalid wf
    lf = wfˢ⇒lc wf
    lλ : LC (lam d Top)
    lλ = lc-lam [] ld (λ _ → lc-Top)
    lλ′ : LC (lam d′ Top)
    lλ′ = lc-lam [] (wfˢ⇒lc wd′) (λ _ → lc-Top)
    up : Γ ∣ [] ⊢ lam d Top ≤ lam d′ Top
    up = chain⇒≤ (lam-l-chain pv ld fd [] (λ _ → lc-Top) (λ ()) p)
```

## What this establishes

`⟶ᵉ-wfˢ`: equivalence reduction preserves the stack-reading well-formedness, at every
configuration, also when the context and the stack reduce with the term (`⟶ᵉ-wfˢ-↣`).
`¬⟶ˢ-wfˢ`: subtyping reduction does not, because `Ms-Top` applies to an operator. It preserves
`wf⁻` (`⟶ˢ-wf⁻`), as does equivalence reduction (`⟶ᵉ-wf⁻`), and `wf⁻` of an abstraction at the
empty stack gives a `wfˢ` annotation. Hence `reach-lam-wfˢ`: an abstraction `lam d Top` above a
`wfˢ` term in the machine relation at the empty stack can be replaced by `lam d′ Top` with `d′` a
`⟶ᵉ*`-reduct of `d` that is `wfˢ`. Nothing is assumed. What is spent: `↣-sub`, `↣-eqv`
(`MPSS/CtxReduce`), `pushᵉ` (`MPSS/StackPush`), `⟶ᵉ-weaken` (`MPSS/Weakening`), `≤-↣`
(`MPSS/MachineNarrow`), `Thm-3ᴸ` (`MPSS/VariantTransfer`), `wfˢ-subst≡` (`MPSS/StackWfSubst`),
`lam-l-chain` and `chain⇒≤` (`MPSS/EvalChain`).
