# MPSS: Lemma 28 — substitution preserves prevalidity

> **Lemma 28 (Substitution preserves prevalidity).** If `Γ, x◁t, Γ′; s` is prevalid then
> `Γ, Γ′[x\t]; s[x\t]` is prevalid. If `Γ, x◁t, Γ′` is prevalid then `Γ, Γ′[x\t]` is prevalid.

Proved here for an arbitrary substituend `α`, not only for the annotation `t`, with the side
conditions that make it true: `α` locally closed and scoped in `Γ`. For `α = t` both come free
from the prevalidity of `Γ, x◁t, Γ′`, so this is a strict generalisation of the printed statement.

**Why the generalisation is needed.** Lemma 7 opens with "we establish that `Γ, Γ′[x\α]` is
prevalid by Lemma 28", substituting the arbitrary `α` of its own statement — but Lemma 28 as
printed only ever substitutes the annotation `t`, so as cited it does not apply. The gap is
repairable, and repaired here: Lemma 7 has `Γ ⊢ α ≤*wf t` in hand, which yields both side
conditions through `⊑*wf-fvˡ` and `⊑*wf⇒lcˡ`.

Substitution never changes a domain, so scoping transfers by rewriting along
`dom (Γ′[x\α]) ≡ dom Γ′`. The content is that `x` cannot survive its own substitution, which is
what lets the middle entry be dropped from the domain — and that is why `fv-subst` below returns
the disequality rather than only the membership.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Subst28 where

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import MPSS.WellFormed
open import MPSS.Rename using (substCtx; substStack; x∉-domΓ)
open import MPSS.Subst.Base using (dom-++)

open import Data.Nat.Properties using (_≟_)
open import PSS.Syntax using (subst-lc)
```

## Free variables under substitution

The substituted variable is reported as absent from the residue, which is the half of the lemma
that does the work later.

```agda
fv-subst : ∀ t x α {z}
         → z ∈ fv (t [ x := α ])
         → ((z ∈ fv t) × (z ≡ x → ⊥)) ⊎ (z ∈ fv α)
fv-subst (bvar _) x α ()
fv-subst (fvar y) x α {z} h with x ≟ y
... | yes refl = inj₂ h
... | no  q    = inj₁ (h , λ { refl → q (name-of h) })
  where
    name-of : z ∈ (y ∷ []) → z ≡ y
    name-of (here p) = p
fv-subst Top x α ()
fv-subst (lam a b) x α {z} h = join (∈-++⁻ (fv (a [ x := α ])) h)
  where
    join : (z ∈ fv (a [ x := α ])) ⊎ (z ∈ fv (b [ x := α ]))
         → ((z ∈ fv (lam a b)) × (z ≡ x → ⊥)) ⊎ (z ∈ fv α)
    join (inj₁ p) with fv-subst a x α p
    ... | inj₁ (q , ne) = inj₁ (∈-++⁺ˡ q , ne)
    ... | inj₂ q        = inj₂ q
    join (inj₂ p) with fv-subst b x α p
    ... | inj₁ (q , ne) = inj₁ (∈-++⁺ʳ (fv a) q , ne)
    ... | inj₂ q        = inj₂ q
fv-subst (app a b) x α {z} h = join (∈-++⁻ (fv (a [ x := α ])) h)
  where
    join : (z ∈ fv (a [ x := α ])) ⊎ (z ∈ fv (b [ x := α ]))
         → ((z ∈ fv (app a b)) × (z ≡ x → ⊥)) ⊎ (z ∈ fv α)
    join (inj₁ p) with fv-subst a x α p
    ... | inj₁ (q , ne) = inj₁ (∈-++⁺ˡ q , ne)
    ... | inj₂ q        = inj₂ q
    join (inj₂ p) with fv-subst b x α p
    ... | inj₁ (q , ne) = inj₁ (∈-++⁺ʳ (fv a) q , ne)
    ... | inj₂ q        = inj₂ q
```

## Domains are untouched

```agda
dom-substCtx : ∀ x α (Δ : Ctx) → dom (substCtx x α Δ) ≡ dom Δ
dom-substCtx x α []                = refl
dom-substCtx x α ((z , c , w) ∷ Δ) = cong (z ∷_) (dom-substCtx x α Δ)

dom-sub-eq : ∀ x α (Δ Γ : Ctx) → dom (substCtx x α Δ ++ Γ) ≡ dom (Δ ++ Γ)
dom-sub-eq x α Δ Γ =
  trans (dom-++ (substCtx x α Δ) Γ)
        (trans (cong (_++ dom Γ) (dom-substCtx x α Δ)) (sym (dom-++ Δ Γ)))

into : ∀ x α (Δ Γ : Ctx) {z} → z ∈ dom (Δ ++ Γ) → z ∈ dom (substCtx x α Δ ++ Γ)
into x α Δ Γ {z} h = subst (z ∈_) (sym (dom-sub-eq x α Δ Γ)) h

outof : ∀ x α (Δ Γ : Ctx) {z} → z ∈ dom (substCtx x α Δ ++ Γ) → z ∈ dom (Δ ++ Γ)
outof x α Δ Γ {z} h = subst (z ∈_) (dom-sub-eq x α Δ Γ) h

inject : ∀ (Δ Γ : Ctx) {z} → (z ∈ dom Δ) ⊎ (z ∈ dom Γ) → z ∈ dom (Δ ++ Γ)
inject Δ Γ {z} (inj₁ p) = subst (z ∈_) (sym (dom-++ Δ Γ)) (∈-++⁺ˡ p)
inject Δ Γ {z} (inj₂ p) = subst (z ∈_) (sym (dom-++ Δ Γ)) (∈-++⁺ʳ (dom Δ) p)

widen : ∀ (Δ : Ctx) {Γ x c t z} → z ∈ dom (Δ ++ Γ) → z ∈ dom (Δ ++ (x , c , t) ∷ Γ)
widen Δ {Γ} {x} {c} {t} {z} h with ∈-++⁻ (dom Δ) (subst (z ∈_) (dom-++ Δ Γ) h)
... | inj₁ p = inject Δ ((x , c , t) ∷ Γ) (inj₁ p)
... | inj₂ p = inject Δ ((x , c , t) ∷ Γ) (inj₂ (there p))
```

## Scoping of a substituted annotation

```agda
entry-scope : ∀ x α (Δ : Ctx) {Γ c t} w
            → x ∉ dom Γ → fv α ⊑ dom Γ
            → fv w ⊑ dom (Δ ++ (x , c , t) ∷ Γ)
            → fv (w [ x := α ]) ⊑ dom (substCtx x α Δ ++ Γ)
entry-scope x α Δ {Γ} {c} {t} w x∉ fα fw {y} h with fv-subst w x α h
... | inj₂ q          = into x α Δ Γ (inject Δ Γ (inj₂ (fα q)))
... | inj₁ (q , y≢x)  = drop (subst (y ∈_) (dom-++ Δ ((x , c , t) ∷ Γ)) (fw q))
  where
    drop : y ∈ dom Δ ++ (x ∷ dom Γ) → y ∈ dom (substCtx x α Δ ++ Γ)
    drop hh with ∈-++⁻ (dom Δ) hh
    ... | inj₁ p         = into x α Δ Γ (inject Δ Γ (inj₁ p))
    ... | inj₂ (here p)  = ⊥-elim (y≢x p)
    ... | inj₂ (there p) = into x α Δ Γ (inject Δ Γ (inj₂ p))
```

## Lemma 28

```agda
Lem-28-ctx : ∀ (Δ : Ctx) {Γ x c t α}
           → LC α → fv α ⊑ dom Γ
           → (Δ ++ (x , c , t) ∷ Γ) prevalid
           → (substCtx x α Δ ++ Γ) prevalid
Lem-28-ctx [] lα fα pv = tail-prevalid pv
Lem-28-ctx ((z , sub , w) ∷ Δ) {Γ} {x} {c} {t} {α} lα fα (Pv-Ctx pv z∉ lw fw) =
  Pv-Ctx (Lem-28-ctx Δ lα fα pv)
         (λ h → z∉ (widen Δ (outof x α Δ Γ h)))
         (subst-lc lw lα)
         (entry-scope x α Δ w (x∉-domΓ Δ pv) fα fw)
Lem-28-ctx ((z , eqv , w) ∷ Δ) {Γ} {x} {c} {t} {α} lα fα (Pv-EqA pv z∉ lw fw) =
  Pv-EqA (Lem-28-ctx Δ lα fα pv)
         (λ h → z∉ (widen Δ (outof x α Δ Γ h)))
         (subst-lc lw lα)
         (entry-scope x α Δ w (x∉-domΓ Δ pv) fα fw)

Lem-28-stk : ∀ (Δ : Ctx) {Γ x c t α s}
           → LC α → fv α ⊑ dom Γ
           → (Δ ++ (x , c , t) ∷ Γ) ∣ s prevalid
           → (substCtx x α Δ ++ Γ) ∣ substStack x α s prevalid
Lem-28-stk Δ lα fα (Pv-Nil pv) = Pv-Nil (Lem-28-ctx Δ lα fα pv)
Lem-28-stk Δ {Γ} {x} {c} {t} {α} lα fα (Pv-Sta {α = β} pv lβ fβ) =
  Pv-Sta (Lem-28-stk Δ lα fα pv)
         (subst-lc lβ lα)
         (entry-scope x α Δ β (x∉-domΓ Δ (prevalid-ctx pv)) fα fβ)
```

## What this establishes

Lemma 28 in both readings, for an arbitrary scoped substituend, and the observation that the
printed statement is not general enough for the use Lemma 7 makes of it.
