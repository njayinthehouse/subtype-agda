# MPSS: what a generated side condition says

`MPSS/Conj8FromLeaves` leaves one obligation, quantified over the side conditions `𝒲` generated
from "`z` applied to `v` is well-formed" by the application and binder wrappers. This module
reads such a condition back: every `ok : 𝒲 Γ σ P` has a base context and a closing function, and
`P z` says exactly that the closed-up term is well-formed there (with `z` locally closed under
each binder it passed).

It is the first piece of the proof of the obligation: the side condition at the points of a
lifted chain has to be established as well-formedness of closed-up terms, and this is the
dictionary.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.Wrapper where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)

open import MPSS.WellFormed
open import MPSS.Frame using (App; Wf)
open import MPSS.Wrap using (Fun)
open import MPSS.Conj8FromLeaves using (𝒲; w-top; w-app; w-fop; w-fun)
open import PSS.Syntax using (closeRec)
```

## Base context and closing

```agda
base : ∀ {Γ σ P} → 𝒲 Γ σ P → Ctx
base (w-top {Γ = Γ} _) = Γ
base (w-app ok)        = base ok
base (w-fop ok _)      = base ok
base (w-fun ok _)      = base ok

close : ∀ {Γ σ P} → 𝒲 Γ σ P → Tm → Tm
close (w-top {v = v} _)             z = app z v
close (w-app {v = v} ok)            z = close ok (app z v)
close (w-fop {t = t} {x = x} ok _)  z = close ok (lam t (closeRec 0 x z))
close (w-fun {t = t} {x = x} ok _)  z = close ok (lam t (closeRec 0 x z))
```

## The side condition is well-formedness of the closed-up term

```agda
holds⇒wf : ∀ {Γ σ P z} (ok : 𝒲 Γ σ P) → P z → base ok ⊢ close ok z wf
holds⇒wf (w-top _)    p = p
holds⇒wf (w-app ok)   p = holds⇒wf ok p
holds⇒wf (w-fop ok _) p = holds⇒wf ok (proj₂ p)
holds⇒wf (w-fun ok _) p = holds⇒wf ok (proj₂ p)

-- local closure under every binder passed
data LCs : ∀ {Γ σ P} → 𝒲 Γ σ P → Tm → Set₁ where
  lcs-top : ∀ {Γ v z} {w : Γ ⊢ v wf} → LCs (w-top w) z
  lcs-app : ∀ {Γ s P v z} {ok : 𝒲 Γ s P} → LCs ok (app z v) → LCs (w-app {v = v} ok) z
  lcs-fop : ∀ {Γ s P α t x z} {ok : 𝒲 Γ (α ∷ s) P} {x∉ : x ∉ dom Γ}
          → LC z → LCs ok (lam t (closeRec 0 x z)) → LCs (w-fop {t = t} ok x∉) z
  lcs-fun : ∀ {Γ P t x z} {ok : 𝒲 Γ [] P} {x∉ : x ∉ dom Γ}
          → LC z → LCs ok (lam t (closeRec 0 x z)) → LCs (w-fun {t = t} ok x∉) z

wf⇒holds : ∀ {Γ σ P z} (ok : 𝒲 Γ σ P) → LCs ok z → base ok ⊢ close ok z wf → P z
wf⇒holds (w-top _)    lcs-top         w = w
wf⇒holds (w-app ok)   (lcs-app l)     w = wf⇒holds ok l w
wf⇒holds (w-fop ok _) (lcs-fop lz l)  w = lz , wf⇒holds ok l w
wf⇒holds (w-fun ok _) (lcs-fun lz l)  w = lz , wf⇒holds ok l w
```

## What this establishes

`holds⇒wf` and `wf⇒holds`: a generated side condition at `z` is well-formedness, in the base
context, of `z` closed up through the wrappers that generated it.
