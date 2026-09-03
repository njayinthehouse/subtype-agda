# MPSS: the statements assumed, and why

Where a result is refuted, the repaired statement is assumed here and the repair documented, so
the obligations downstream can be discharged against it. Where a result is merely unproved, it is
assumed as printed.

Assumptions are **declared statement types**, taken as explicit arguments by the modules that use
them, not `postulate` blocks: every module stays `--safe`, nothing is silently trusted, and each
dependency is visible in the type of the theorem that rests on it. `../PLAN.md` and `AUDIT.md`
record which is which.

| assumed | status of the printed original |
| --- | --- |
| `Lem-1` | unproved here; the paper's main theorem |
| `Lem-2` | unproved here; no induction principle in the printed proof |
| `Conj-8` | the paper's own conjecture |
| `Prop-17ʳ` | **repaired** — the printed Proposition 17 is refuted (`MPSS/BetaScope`, `MPSS/BetaScopeWf`) |

Proposition 18 needs no entry: its printed form is refuted, and the repaired form — reflexivity
with the scoping premise — is *proved*, as `⟶ᵉ-refl` and `⟶ˢ-refl` in `MPSS/StackPush`.

```agda
{-# OPTIONS --safe #-}

module MPSS.Assumed where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax)

open import MPSS.WellFormed
open import MPSS.CtxReduction
open import MPSS.Conjecture8 using (CoCtx; plug; CoLC)
```

## Lemma 1 — strong commutation

> If `Γ;s ⊢ t₀ ⟶ᵉ t₁` and `Γ;s ⊢ t₀ ⟶ˢ t₂`, then for any `Γ′;s′` with `Γ;s ↣ Γ′;s′` there is
> `t₃` with `Γ;s ⊢ t₂ ⟶ᵉ t₃` and `Γ′;s′ ⊢ t₁ ⟶ˢ t₃`.

```agda
Lem-1 : Set
Lem-1 = ∀ {Γ s Γ′ s′ t₀ t₁ t₂}
      → Γ ∣ s ⊢ t₀ ⟶ᵉ t₁
      → Γ ∣ s ⊢ t₀ ⟶ˢ t₂
      → Γ ∣ s ↣ Γ′ ∣ s′
      → ∃[ t₃ ] ((Γ ∣ s ⊢ t₂ ⟶ᵉ t₃) × (Γ′ ∣ s′ ⊢ t₁ ⟶ˢ t₃))
```

## Lemma 2 — the diamond

```agda
Lem-2 : Set
Lem-2 = ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂}
      → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₁
      → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂
      → Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁
      → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂
      → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ t₁ ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ t₂ ⟶ᵉ t₃))
```

## Conjecture 8

```agda
Conj-8 : Set
Conj-8 = ∀ {Γ u t} (C : CoCtx)
       → CoLC C → LC u → LC t
       → Γ ⊢ u ≤*wf t
       → Γ ⊢ plug C u wf
       → Γ ⊢ plug C t wf
       → Γ ⊢ plug C u ≤*wf plug C t
```

## Proposition 17, repaired

The printed statement — `u ↦ v` implies `Γ;s ⊢ u ⟶ᵉ v` for every extended context — is false, and
stays false on well-formed subjects. The failure is not in the proposition but in the rule it
appeals to:

> `Me-Bet`: `Γ;s ⊢ u ⟶≡ u′    Γ;nil ⊢ v ⟶≡ v′  /  Γ;s ⊢ (λx≤t.u) v ⟶≡ u′[x\v′]`

reduces the redex body `u` — in which the abstraction's parameter is free — in a context that
does not bind it, while `Me-App` pushes operands onto the stack and `Pv-Sta` scopes every stack
entry in the domain. A body that passes its parameter as an operand therefore has no derivation
at all, so the reflexive instance the proposition's base case needs does not exist.

The repair is to bind the parameter in that premise, as `Me-Fun` and `Me-FOp` already do. Under
it the body is scoped and the base case goes through. Since the repair changes `⟶ᵉ`, and with it
the relation Lemmas 1 and 2 quantify over, it is not made here; the repaired conclusion is
assumed instead, with the scoping premise that the repaired rule would supply.

```agda
Prop-17ʳ : Set
Prop-17ʳ = ∀ {Γ s u v}
         → Γ ∣ s prevalid → LC u → fv u ⊑ dom Γ
         → u ↦ v
         → Γ ∣ s ⊢ u ⟶ᵉ v
```

## What this establishes

Nothing — by design. It fixes the four statements the remaining obligations are allowed to lean
on, three of them as printed and one repaired, so that what is proved downstream is exactly
"modulo these, and nothing else".
