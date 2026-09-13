# MPSS: Lemma 1 for the variant, proved

`MPSS/Commutation` reduces Lemma 1 to Lemma 2 plus four named statements, three of which are
cases of the theorem itself (`Bet-App`, `Fun-Fun`, `FOp-FOp`). For the variant relations
`⟶ᵉ′`/`⟶ˢ′` all three are proved here, so the lemma is unconditional:

> **Lemma 1′.** If `Γ;s ⊢ t₀ ⟶ᵉ′ t₁` and `Γ;s ⊢ t₀ ⟶ˢ′ t₂`, then for any `Γ′;s′` with
> `Γ;s ↣′ Γ′;s′` there is `t₃` with `Γ;s ⊢ t₂ ⟶ᵉ′ t₃` and `Γ′;s′ ⊢ t₁ ⟶ˢ′ t₃`.

The induction is on the size of the subject, so the binder cases may call the hypothesis on
the opened body. The `Bet-App′` case — `Ms-App′` promoting the operator of a redex under
`Ms-FOp′`, against `Me-Bet′` — puts the two body premises in different contexts (the promotion
binds the parameter, the contraction does not); it closes the way the diamond's `app-bet` does,
by carrying the invariant that the equivalence side of the join is derivable with any closed set
of names removed that the equivalence edge and the context reduction avoid, and asking for it
with the parameter added to the set.

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.VariantCommutation where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤m+n; m≤n+m; n≤1+n; ≤-reflexive; +-assoc; +-comm)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import PSS.Syntax using (fresh; fresh-∉; ∉-++ˡ; ∉-++ʳ; closeRec)
open import PSS.Close using (open-close; fv-close)
open import MPSS.WellFormed
open import MPSS.EmptyStackPro
open import MPSS.VariantLemmas using (⟶ᵉ′-lc; ⟶ᵉ′-prevalid; ⟶ᵉ′-weaken; ⟶ᵉ′-refl; ⟶ᵉ′-rename-head; fv-⟶ᵉ′)
open import MPSS.VariantPush using (pushᵉ′)
open import MPSS.VariantCtx
open import MPSS.VariantSub
open import MPSS.VariantAvoids using (Avoids′; Avoids*′; stack-free′; avoids-push′; avoids-weaken′; unbound-avoids′)
open import MPSS.VariantSubstEqv using (close-rename₀′)
open import MPSS.VariantDiamond
  using (join′; Pieces′; Pieces*′; unbound-pieces′; pieces-empty′; ↣′-pop; pop-piece′;
         pieces-pop′; avoids-pop′; ↣′-closed)
open import MPSS.DiamondStep using (remove; remove-⊑; ∉-remove; ∖-remove; closed-remove)
open import MPSS.VariantDrop
open import MPSS.VariantMeasure using (tsize; tsize-open)
open import MPSS.Closed
open import MPSS.Drop
open import MPSS.Subst.Base using (∉-stack)
```

## Small facts

```agda
Top-⟶ˢ′ : ∀ {Γ s w} → Γ ∣ s ⊢ Top ⟶ˢ′ w → w ≡ Top
Top-⟶ˢ′ (Ms-Top′ _)            = refl
Top-⟶ˢ′ (Ms-Equ′ _ (Me-Top′ _)) = refl

clash : ∀ {Γ x α t} → Γ prevalid → x ≐ α ∈ Γ → x ≤ t ∈ Γ → ∀ {A : Set} → A
clash (Pv-Ctx pv x∉ _ _) (there me) (here refl) = ⊥-elim (x∉ (∈-dom me))
clash (Pv-EqA pv x∉ _ _) (here refl) (there ms) = ⊥-elim (x∉ (∈-dom ms))
clash (Pv-Ctx pv _ _ _)  (there me) (there ms)  = clash pv me ms
clash (Pv-EqA pv _ _ _)  (there me) (there ms)  = clash pv me ms

tsize-op : ∀ u v → tsize u < tsize (app u v)
tsize-op u v = s≤s (m≤m+n (tsize u) (tsize v))

tsize-lam-body : ∀ x w b → tsize (b ^ fvar x) < tsize (lam w b)
tsize-lam-body x w b rewrite tsize-open 0 x b = s≤s (m≤n+m (tsize b) (tsize w))

tsize-bet-body : ∀ x w b v → tsize (b ^ fvar x) < tsize (app (lam w b) v)
tsize-bet-body x w b v rewrite tsize-open 0 x b =
  s≤s (≤-trans (m≤n+m (tsize b) (tsize w)) (≤-trans (n≤1+n _) (m≤m+n _ (tsize v))))
```

## The statement

```agda
Join₁ : ∀ {Γ s Γ′ s′ t₀ t₁ t₂}
      → Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁ → Γ ∣ s ⊢ t₀ ⟶ˢ′ t₂ → Γ ∣ s ↣′ Γ′ ∣ s′ → Set
Join₁ {Γ} {s} {Γ′} {s′} {t₀} {t₁} {t₂} e st c =
  ∃[ t₃ ] ((∀ B → Closed Γ B → Avoids*′ B e → Pieces*′ B c → (Γ ∖ B) ∣ s ⊢ t₂ ⟶ᵉ′ t₃)
         × (Γ′ ∣ s′ ⊢ t₁ ⟶ˢ′ t₃))

IH : ℕ → Set
IH n = ∀ {Γ s Γ′ s′ t₀ t₁ t₂} → tsize t₀ < n → LC t₀
     → (e : Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁) (st : Γ ∣ s ⊢ t₀ ⟶ˢ′ t₂) (c : Γ ∣ s ↣′ Γ′ ∣ s′)
     → Join₁ e st c
```

## The cases

```agda
module _ (n : ℕ) (ih : IH n) where
```

`Ms-Top′`, `Ms-Equ′`, `Ms-Pro′`: no recursion. The equivalence case is one application of the
variant's diamond in its invariant form; the promotion case reads the annotation's reduct off
the context reduction and drops the avoided names.

```agda
  top-case : ∀ {Γ s Γ′ s′ t₀ t₁} (e : Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁) (pv : Γ ∣ s prevalid) (c : Γ ∣ s ↣′ Γ′ ∣ s′)
      → Join₁ e (Ms-Top′ pv) c
  top-case e pv c = Top , (λ B cl av pc → Me-Top′ (prevalid-∖-ext cl (stack-free′ e av) pv))
                   , Ms-Top′ (↣′-prevalid pv c)

  equ-case : ∀ {Γ s Γ′ s′ t₀ t₁ t₂} → LC t₀
      → (e : Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁) (pv : Γ ∣ s prevalid) (e₂ : Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₂) (c : Γ ∣ s ↣′ Γ′ ∣ s′)
      → Join₁ e (Ms-Equ′ pv e₂) c
  equ-case {Γ′ = Γ′} lc e pv e₂ c with join′ lc e₂ e Ct-Refl′ c
  ... | t₃ , f₁ , f₂ = t₃ , f₁ , Ms-Equ′ (⟶ᵉ′-prevalid g) g
    where
      g : Γ′ ∣ _ ⊢ _ ⟶ᵉ′ t₃
      g = subst (λ Γ → Γ ∣ _ ⊢ _ ⟶ᵉ′ t₃) (∖-[] Γ′) (f₂ [] (λ _ ()) (λ ()) (λ ()))

  pro-case : ∀ {Γ s Γ′ s′ x t} (pv pv′ : Γ ∣ s prevalid) (m : x ≤ t ∈ Γ) (c : Γ ∣ s ↣′ Γ′ ∣ s′)
      → Join₁ (Me-Var′ {x = x} pv) (Ms-Pro′ pv′ m) c
  pro-case {Γ} {s} {x = x} pv pv′ m c with ↣′-sub (prevalid-ctx pv′) c m | avoids-sub″
    where
      avoids-sub″ : ∀ {b} → Pieces′ b c → Avoids′ b (proj₂ (proj₂ (↣′-sub (prevalid-ctx pv′) c m)))
      avoids-sub″ = avoids-sub′ (prevalid-ctx pv′) c m
  ... | t″ , m′ , e′ | av-e′ =
    t″ , (λ B cl av pc → ⟶ᵉ′-drop cl (pushᵉ′ {s = []} {s′ = s} e′ pv)
                                   (λ b∈ → avoids-push′ e′ pv (av-e′ (pc b∈)) (av b∈)))
       , Ms-Pro′ (↣′-prevalid pv′ c) m′
```

`Ms-App′`: against `Me-App′` the operator's premises sit at the pushed stack, and the operand's
reduct is what the target stack is pushed with; against `Me-TAp′` the operator is `Top`.

```agda
  app-case : ∀ {Γ s Γ′ s′ u v u₁ v₁ u₂} → LC u
      → (du : Γ ∣ (v ∷ s) ⊢ u ⟶ᵉ′ u₁) (dv : Γ ∣ [] ⊢ v ⟶ᵉ′ v₁) (st : Γ ∣ (v ∷ s) ⊢ u ⟶ˢ′ u₂)
        (c : Γ ∣ s ↣′ Γ′ ∣ s′)
      → tsize (app u v) ≤ n
      → Join₁ (Me-App′ du dv) (Ms-App′ st) c
  app-case {u = u} {v = v} lu du dv st c bd with ih (≤-trans (tsize-op u v) bd) lu du st (Ct-Stk′ c dv)
  ... | a₃ , f₁ , stʳ =
    app a₃ _ , (λ B cl av pc → Me-App′ (f₁ B cl (λ b∈ → proj₁ (av b∈)) (λ b∈ → pc b∈ , proj₂ (av b∈)))
                                       (⟶ᵉ′-drop cl dv (λ b∈ → proj₂ (av b∈))))
             , Ms-App′ stʳ

  tap-case : ∀ {Γ s Γ′ s′ u a′} (pv : Γ ∣ s prevalid) (st : Γ ∣ (u ∷ s) ⊢ Top ⟶ˢ′ a′) (c : Γ ∣ s ↣′ Γ′ ∣ s′)
      → Join₁ (Me-TAp′ {u = u} pv) (Ms-App′ st) c
  tap-case {u = u} pv st c with Top-⟶ˢ′ st
  ... | refl = Top , (λ B cl av pc → Me-TAp′ (prevalid-∖-ext cl (stack-free′ (Me-TAp′ {u = u} pv) av) pv))
                   , Ms-Top′ (↣′-prevalid pv c)
```

`Ms-App′` over a redex against `Me-Bet′` — the `Bet-App` case. The operator's promotion is one
of three: to `Top`; by an equivalence step, which makes the whole thing two equivalence steps and
hence the diamond; or under `Ms-FOp′`, with the body promoted under `x ≡ v`. In the last, the
contraction's body is weakened to the same extended context, the hypothesis is applied there,
and the invariant with the parameter added to the set puts the equivalence side of the join back
at `Γ ∖ B`, while the subtyping side is reopened by substituting the operand's reduct for the
parameter.

```agda
  bet-case : ∀ {Γ s Γ′ s′ w b v b₁ v₁ a′} (L₀ : List Name) → LC w
      → (F₀ : ∀ {x} → x ∉ L₀ → LC (b ^ fvar x)) → LC v
      → (L : List Name) (F : ∀ {x} → x ∉ L → Γ ∣ s ⊢ (b ^ fvar x) ⟶ᵉ′ (b₁ ^ fvar x))
        (dv : Γ ∣ [] ⊢ v ⟶ᵉ′ v₁)
      → (st : Γ ∣ (v ∷ s) ⊢ lam w b ⟶ˢ′ a′) (c : Γ ∣ s ↣′ Γ′ ∣ s′)
      → tsize (app (lam w b) v) ≤ n
      → Join₁ (Me-Bet′ {t = w} {u = b} {u' = b₁} L F dv) (Ms-App′ st) c
  bet-case {Γ} {s} {Γ′} {s′} {w} {b} {v} {b₁} {v₁} L₀ lw F₀ lv L F dv (Ms-Top′ pv₁) c bd =
    Top , (λ B cl av pc → Me-TAp′ (prevalid-∖-ext cl (stack-free′ e av) pv))
        , Ms-Top′ (↣′-prevalid pv c)
    where
      e  = Me-Bet′ {t = w} {u = b} {u' = b₁} L F dv
      pv = ⟶ᵉ′-prevalid e
  bet-case {Γ} {s} {Γ′} {s′} {w} {b} {v} {b₁} {v₁} L₀ lw F₀ lv L F dv (Ms-Equ′ pv₁ e₂) c bd
    with join′ (lc-app (lc-lam L₀ lw F₀) lv)
               (Me-App′ e₂ (⟶ᵉ′-refl (prevalid-nil pv₁) lv (prevalid-head-fv pv₁)))
               (Me-Bet′ {t = w} {u = b} {u' = b₁} L F dv) Ct-Refl′ c
  ... | t₃ , f₁ , f₂ = t₃ , f₁ , Ms-Equ′ (⟶ᵉ′-prevalid g) g
    where
      g : Γ′ ∣ s′ ⊢ (b₁ ^ v₁) ⟶ᵉ′ t₃
      g = subst (λ Γ → Γ ∣ s′ ⊢ (b₁ ^ v₁) ⟶ᵉ′ t₃) (∖-[] Γ′) (f₂ [] (λ _ ()) (λ ()) (λ ()))
  bet-case {Γ} {s} {Γ′} {s′} {w} {b} {v} {b₁} {v₁} L₀ lw F₀ lv L F dv (Ms-FOp′ {u' = b₂} L₂ G) c bd =
    (b₃ ^ v₁) , side₁ , side₂
    where
      A = L₀ ++ L ++ L₂ ++ dom Γ ++ dom Γ′ ++ fv b ++ fv b₁ ++ fv b₂
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ : x ∉ dom Γ
      x∉Γ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ) r₃
      x∉Γ′ : x ∉ dom Γ′
      x∉Γ′ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ′) r₄
      r₆ = ∉-++ʳ (fv b) r₅
      x∉b₁ : x ∉ fv b₁
      x∉b₁ = ∉-++ˡ r₆
      x∉b₂ : x ∉ fv b₂
      x∉b₂ = ∉-++ʳ (fv b₁) r₆

      e = Me-Bet′ {t = w} {u = b} {u' = b₁} L F dv
      pv : Γ ∣ s prevalid
      pv = ⟶ᵉ′-prevalid e
      pvx : ((x , eqv , v) ∷ Γ) ∣ s prevalid
      pvx = ⟶ˢ′-prevalid (G x∉L₂)
      fvv : fv v ⊑ dom Γ
      fvv = head-fv (prevalid-ctx pvx)

      Fʷ : ((x , eqv , v) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ′ (b₁ ^ fvar x)
      Fʷ = ⟶ᵉ′-weaken [] ((x , eqv , v) ∷ []) pvx (F x∉L)

      jb = ih (≤-trans (tsize-bet-body x w b v) bd) (F₀ x∉L₀) Fʷ (G x∉L₂) (Ct-Ann′ {x = x} {c = eqv} c dv)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ′-lc (⟶ˢ′-lc (F₀ x∉L₀) (G x∉L₂)) (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ B → Avoids*′ B e → Pieces*′ B c
            → (Γ ∖ B) ∣ s ⊢ app (lam w b₂) v ⟶ᵉ′ (b₃ ^ v₁)
      side₁ B cl av pc =
        Me-Bet′ {t = w} {u = b₂} {u' = b₃} A
                (λ {y} y∉ → close-rename₀′ {u = b₂} x y (∉-dom-∖ Γ x∉Γ) x∉b₂ lw₃ g′) h
        where
          cl′ : Closed ((x , eqv , v) ∷ Γ) (x ∷ B)
          cl′ = closed-add (prevalid-ctx pv) x∉Γ cl
          av′ : Avoids*′ (x ∷ B) Fʷ
          av′ (here refl) = avoids-weaken′ [] _ pvx (F x∉L) (unbound-avoids′ x x∉Γ (F x∉L))
          av′ (there b∈)  = avoids-weaken′ [] _ pvx (F x∉L) (proj₁ (av b∈) x∉L)
          pc′ : Pieces*′ (x ∷ B) (Ct-Ann′ {x = x} {c = eqv} c dv)
          pc′ (here refl) = unbound-pieces′ x x∉Γ c , unbound-avoids′ x x∉Γ dv
          pc′ (there b∈)  = pc b∈ , proj₂ (av b∈)
          g : (((x , eqv , v) ∷ Γ) ∖ (x ∷ B)) ∣ s ⊢ (b₂ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₁ (proj₂ jb) (x ∷ B) cl′ av′ pc′
          g′ : (Γ ∖ B) ∣ s ⊢ (b₂ ^ fvar x) ⟶ᵉ′ w₃
          g′ = subst (λ Γ₁ → Γ₁ ∣ s ⊢ (b₂ ^ fvar x) ⟶ᵉ′ w₃)
                     (trans (∖-∈ {Γ} {x ∷ B} {x} {eqv} {v} (here refl)) (∖-∉dom Γ x∉Γ)) g
          h : (Γ ∖ B) ∣ [] ⊢ v ⟶ᵉ′ v₁
          h = ⟶ᵉ′-drop cl dv (λ b∈ → proj₂ (av b∈))

      side₂ : Γ′ ∣ s′ ⊢ (b₁ ^ v₁) ⟶ˢ′ (b₃ ^ v₁)
      side₂ = ⟶ˢ′-subst≡-head {u = b₁} {u′ = b₃} x x∉b₁ (fv-close 0 x w₃) x∉s′ lv₁ fvv₁ g₂″
        where
          g₂ : ((x , eqv , v₁) ∷ Γ′) ∣ s′ ⊢ (b₁ ^ fvar x) ⟶ˢ′ w₃
          g₂ = proj₂ (proj₂ jb)
          g₂″ : ((x , eqv , v₁) ∷ Γ′) ∣ s′ ⊢ (b₁ ^ fvar x) ⟶ˢ′ (b₃ ^ fvar x)
          g₂″ rewrite open-close lw₃ 0 x = g₂
          lv₁ : LC v₁
          lv₁ = ⟶ᵉ′-lc lv dv
          x∉s′ : x ∉ fvStack s′
          x∉s′ = ∉-stack (↣′-prevalid pv c) x∉Γ′
          fvv₁ : fv v₁ ⊑ dom Γ′
          fvv₁ = fv-⟶ᵉ′ (λ q → subst (_ ∈_) (↣′-dom c) q) dv (λ q → subst (_ ∈_) (↣′-dom c) (fvv q))
```

Under a binder: the hypothesis applies to the opened body at the extended context; the joined
body is closed over the fresh name and both families are rebuilt by renaming. `Me-Fun′` moves
the annotation where `Ms-Fun′` leaves it, so the join carries the moved annotation.

```agda
  fun-case : ∀ {Γ Γ′ w w₁ b b₁ b₂} (L₀ : List Name) → LC w
      → (F₀ : ∀ {x} → x ∉ L₀ → LC (b ^ fvar x))
      → (L₁ : List Name) (dt : Γ ∣ [] ⊢ w ⟶ᵉ′ w₁)
        (F₁ : ∀ {x} → x ∉ L₁ → ((x , sub , w) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ᵉ′ (b₁ ^ fvar x))
      → (L₂ : List Name)
        (G₂ : ∀ {x} → x ∉ L₂ → ((x , sub , w) ∷ Γ) ∣ [] ⊢ (b ^ fvar x) ⟶ˢ′ (b₂ ^ fvar x))
      → (c : Γ ∣ [] ↣′ Γ′ ∣ [])
      → tsize (lam w b) ≤ n
      → Join₁ (Me-Fun′ {u = b} {u' = b₁} L₁ dt F₁) (Ms-Fun′ {u' = b₂} L₂ G₂) c
  fun-case {Γ} {Γ′} {w} {w₁} {b} {b₁} {b₂} L₀ lw F₀ L₁ dt F₁ L₂ G₂ c bd =
    lam w₁ b₃ , side₁ , side₂
    where
      A = L₀ ++ L₁ ++ L₂ ++ dom Γ ++ dom Γ′ ++ fv b ++ fv b₁ ++ fv b₂ ++ fv w ++ fv w₁
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L₁ = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L₁ r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ : x ∉ dom Γ
      x∉Γ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ) r₃
      x∉Γ′ : x ∉ dom Γ′
      x∉Γ′ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ′) r₄
      r₆ = ∉-++ʳ (fv b) r₅
      x∉b₁ : x ∉ fv b₁
      x∉b₁ = ∉-++ˡ r₆
      r₇ = ∉-++ʳ (fv b₁) r₆
      x∉b₂ : x ∉ fv b₂
      x∉b₂ = ∉-++ˡ r₇
      r₈ = ∉-++ʳ (fv b₂) r₇
      x∉w : x ∉ fv w
      x∉w = ∉-++ˡ r₈
      x∉w₁ : x ∉ fv w₁
      x∉w₁ = ∉-++ʳ (fv w) r₈

      e = Me-Fun′ {u = b} {u' = b₁} L₁ dt F₁

      jb = ih (≤-trans (tsize-lam-body x w b) bd) (F₀ x∉L₀) (F₁ x∉L₁) (G₂ x∉L₂)
              (Ct-Ann′ {x = x} {c = sub} c dt)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ′-lc (⟶ˢ′-lc (F₀ x∉L₀) (G₂ x∉L₂)) (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ B → Avoids*′ B e → Pieces*′ B c
            → (Γ ∖ B) ∣ [] ⊢ lam w b₂ ⟶ᵉ′ lam w₁ b₃
      side₁ B cl av pc = Me-Fun′ A (⟶ᵉ′-drop cl dt (λ b∈ → proj₁ (proj₂ (av b∈)))) body
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , sub , w) ∷ Γ) B′
          cl′ = closed-sub (closed-remove x∉Γ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids*′ B′ (F₁ x∉L₁)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₁
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces*′ B′ (Ct-Ann′ {x = x} {c = sub} c dt)
          pc′ b∈ = pc (remove-⊑ {x} {B} b∈) , proj₁ (proj₂ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , sub , w) ∷ Γ) ∖ B′) ∣ [] ⊢ (b₂ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₁ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , sub , w) ∷ (Γ ∖ B)) ∣ [] ⊢ (b₂ ^ fvar x) ⟶ᵉ′ w₃
          g′ rewrite sym (∖-remove Γ {B} x∉Γ) | sym (∖-∉ {Γ} {B′} {x} {sub} {w} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , sub , w) ∷ (Γ ∖ B)) ∣ [] ⊢ (b₂ ^ fvar y) ⟶ᵉ′ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ′-rename-head {b = b₂} x y (∉-dom-∖ Γ x∉Γ) (∉-dom-∖ Γ y∉Γ) x∉w x∉b₂ (λ ()) lw₃ g′
            where
              y∉Γ : y ∉ dom Γ
              y∉Γ = ∉-++ˡ (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉)))

      side₂ : Γ′ ∣ [] ⊢ lam w₁ b₁ ⟶ˢ′ lam w₁ b₃
      side₂ = Ms-Fun′ A body
        where
          g₂ : ((x , sub , w₁) ∷ Γ′) ∣ [] ⊢ (b₁ ^ fvar x) ⟶ˢ′ w₃
          g₂ = proj₂ (proj₂ jb)
          body : ∀ {y} → y ∉ A → ((y , sub , w₁) ∷ Γ′) ∣ [] ⊢ (b₁ ^ fvar y) ⟶ˢ′ (b₃ ^ fvar y)
          body {y} y∉ = ⟶ˢ′-rename-head {b = b₁} x y x∉Γ′ y∉Γ′ x∉w₁ x∉b₁ (λ ()) lw₃ g₂
            where
              y∉Γ′ : y ∉ dom Γ′
              y∉Γ′ = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉))))

  fop-case : ∀ {Γ s Γ′ s′ α w w₁ b b₁ b₂} (L₀ : List Name) → LC w
      → (F₀ : ∀ {x} → x ∉ L₀ → LC (b ^ fvar x))
      → (L₁ : List Name) (dt : Γ ∣ [] ⊢ w ⟶ᵉ′ w₁)
        (F₁ : ∀ {x} → x ∉ L₁ → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ᵉ′ (b₁ ^ fvar x))
      → (L₂ : List Name)
        (G₂ : ∀ {x} → x ∉ L₂ → ((x , eqv , α) ∷ Γ) ∣ s ⊢ (b ^ fvar x) ⟶ˢ′ (b₂ ^ fvar x))
      → (c : Γ ∣ (α ∷ s) ↣′ Γ′ ∣ s′)
      → tsize (lam w b) ≤ n
      → Join₁ (Me-FOp′ {u = b} {u' = b₁} L₁ dt F₁) (Ms-FOp′ {u' = b₂} L₂ G₂) c
  fop-case {Γ} {s} {Γ′} {s′} {α} {w} {w₁} {b} {b₁} {b₂} L₀ lw F₀ L₁ dt F₁ L₂ G₂ c bd =
    lam w₁ b₃ , side₁ , side₂
    where
      e = Me-FOp′ {u = b} {u' = b₁} L₁ dt F₁
      pv₀ : Γ ∣ (α ∷ s) prevalid
      pv₀ = ⟶ᵉ′-prevalid e
      pvn = prevalid-nil pv₀
      lα  = prevalid-head-lc pv₀
      fα  = prevalid-head-fv pv₀

      pop  = ↣′-pop c
      α₁   = proj₁ pop
      s₁   = proj₁ (proj₂ pop)
      eq   = proj₁ (proj₂ (proj₂ pop))
      c′   = proj₁ (proj₂ (proj₂ (proj₂ pop)))
      pp   = proj₂ (proj₂ (proj₂ (proj₂ pop)))
      q    = pop-piece′ pvn lα fα pp

      A = L₀ ++ L₁ ++ L₂ ++ dom Γ ++ dom Γ′ ++ fv b ++ fv b₁ ++ fv b₂ ++ fv α ++ fv α₁
          ++ fvStack s ++ fvStack s₁
      x = fresh A
      a∉ = fresh-∉ A
      x∉L₀ = ∉-++ˡ a∉
      r₁ = ∉-++ʳ L₀ a∉
      x∉L₁ = ∉-++ˡ r₁
      r₂ = ∉-++ʳ L₁ r₁
      x∉L₂ = ∉-++ˡ r₂
      r₃ = ∉-++ʳ L₂ r₂
      x∉Γ : x ∉ dom Γ
      x∉Γ = ∉-++ˡ r₃
      r₄ = ∉-++ʳ (dom Γ) r₃
      x∉Γ′ : x ∉ dom Γ′
      x∉Γ′ = ∉-++ˡ r₄
      r₅ = ∉-++ʳ (dom Γ′) r₄
      r₆ = ∉-++ʳ (fv b) r₅
      x∉b₁ : x ∉ fv b₁
      x∉b₁ = ∉-++ˡ r₆
      r₇ = ∉-++ʳ (fv b₁) r₆
      x∉b₂ : x ∉ fv b₂
      x∉b₂ = ∉-++ˡ r₇
      r₈ = ∉-++ʳ (fv b₂) r₇
      x∉α : x ∉ fv α
      x∉α = ∉-++ˡ r₈
      r₉ = ∉-++ʳ (fv α) r₈
      x∉α₁ : x ∉ fv α₁
      x∉α₁ = ∉-++ˡ r₉
      r₁₀ = ∉-++ʳ (fv α₁) r₉
      x∉s : x ∉ fvStack s
      x∉s = ∉-++ˡ r₁₀
      x∉s₁ : x ∉ fvStack s₁
      x∉s₁ = ∉-++ʳ (fvStack s) r₁₀

      jb = ih (≤-trans (tsize-lam-body x w b) bd) (F₀ x∉L₀) (F₁ x∉L₁) (G₂ x∉L₂)
              (Ct-Ann′ {x = x} {c = eqv} c′ q)
      w₃ = proj₁ jb
      b₃ = closeRec 0 x w₃

      lw₃ : LC w₃
      lw₃ = ⟶ᵉ′-lc (⟶ˢ′-lc (F₀ x∉L₀) (G₂ x∉L₂)) (proj₁ (proj₂ jb) [] (λ _ ()) (λ ()) (λ ()))

      side₁ : ∀ B → Closed Γ B → Avoids*′ B e → Pieces*′ B c
            → (Γ ∖ B) ∣ (α ∷ s) ⊢ lam w b₂ ⟶ᵉ′ lam w₁ b₃
      side₁ B cl av pc = Me-FOp′ A (⟶ᵉ′-drop cl dt (λ b∈ → proj₁ (proj₂ (av b∈)))) body
        where
          B′ = remove x B
          x∉B′ : x ∉ B′
          x∉B′ = ∉-remove {x} {B}
          cl′ : Closed ((x , eqv , α) ∷ Γ) B′
          cl′ = closed-eqv (closed-remove x∉Γ cl) (λ b∈ → proj₁ (av (remove-⊑ {x} {B} b∈)))
          av′ : Avoids*′ B′ (F₁ x∉L₁)
          av′ b∈ = proj₂ (proj₂ (av (remove-⊑ {x} {B} b∈))) x∉L₁
                         (λ eq → x∉B′ (subst (_∈ B′) (sym eq) b∈))
          pc′ : Pieces*′ B′ (Ct-Ann′ {x = x} {c = eqv} c′ q)
          pc′ b∈ = proj₁ (pieces-pop′ c (pc (remove-⊑ {x} {B} b∈)))
                 , avoids-pop′ pvn lα fα pp (proj₂ (pieces-pop′ c (pc (remove-⊑ {x} {B} b∈))))
                               (proj₁ (av (remove-⊑ {x} {B} b∈)))
          g : (((x , eqv , α) ∷ Γ) ∖ B′) ∣ s ⊢ (b₂ ^ fvar x) ⟶ᵉ′ w₃
          g = proj₁ (proj₂ jb) B′ cl′ av′ pc′
          g′ : ((x , eqv , α) ∷ (Γ ∖ B)) ∣ s ⊢ (b₂ ^ fvar x) ⟶ᵉ′ w₃
          g′ rewrite sym (∖-remove Γ {B} x∉Γ) | sym (∖-∉ {Γ} {B′} {x} {eqv} {α} x∉B′) = g
          body : ∀ {y} → y ∉ A → ((y , eqv , α) ∷ (Γ ∖ B)) ∣ s ⊢ (b₂ ^ fvar y) ⟶ᵉ′ (b₃ ^ fvar y)
          body {y} y∉ =
            ⟶ᵉ′-rename-head {b = b₂} x y (∉-dom-∖ Γ x∉Γ) (∉-dom-∖ Γ y∉Γ) x∉α x∉b₂ x∉s lw₃ g′
            where
              y∉Γ : y ∉ dom Γ
              y∉Γ = ∉-++ˡ (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉)))

      side₂ : Γ′ ∣ s′ ⊢ lam w₁ b₁ ⟶ˢ′ lam w₁ b₃
      side₂ = subst (λ σ → Γ′ ∣ σ ⊢ lam w₁ b₁ ⟶ˢ′ lam w₁ b₃) (sym eq) (Ms-FOp′ A body)
        where
          g₂ : ((x , eqv , α₁) ∷ Γ′) ∣ s₁ ⊢ (b₁ ^ fvar x) ⟶ˢ′ w₃
          g₂ = proj₂ (proj₂ jb)
          body : ∀ {y} → y ∉ A → ((y , eqv , α₁) ∷ Γ′) ∣ s₁ ⊢ (b₁ ^ fvar y) ⟶ˢ′ (b₃ ^ fvar y)
          body {y} y∉ = ⟶ˢ′-rename-head {b = b₁} x y x∉Γ′ y∉Γ′ x∉α₁ x∉b₁ x∉s₁ lw₃ g₂
            where
              y∉Γ′ : y ∉ dom Γ′
              y∉Γ′ = ∉-++ˡ (∉-++ʳ (dom Γ) (∉-++ʳ L₂ (∉-++ʳ L₁ (∉-++ʳ L₀ y∉))))
```

## One unfolding, and the induction

```agda
  step : IH (suc n)
  step (s≤s bd) lc e (Ms-Top′ pv) c = top-case e pv c
  step (s≤s bd) lc e (Ms-Equ′ pv e₂) c = equ-case lc e pv e₂ c
  step (s≤s bd) lc (Me-Var′ pv) (Ms-Pro′ pv′ m) c = pro-case pv pv′ m c
  step (s≤s bd) lc (Me-Pro′ pv me _) (Ms-Pro′ pv′ ms) c = clash (prevalid-ctx pv) me ms
  step (s≤s bd) (lc-app lu lv) (Me-App′ du dv) (Ms-App′ st) c = app-case lu du dv st c bd
  step (s≤s bd) lc (Me-TAp′ pv) (Ms-App′ st) c = tap-case pv st c
  step (s≤s bd) (lc-app (lc-lam L₀ lw F₀) lv) (Me-Bet′ {u' = b₁} L F dv) (Ms-App′ st) c =
    bet-case {b₁ = b₁} L₀ lw F₀ lv L F dv st c bd
  step (s≤s bd) (lc-lam L₀ lw F₀) (Me-Fun′ {u = b} {u' = b₁} L₁ dt F₁) (Ms-Fun′ {u' = b₂} L₂ G₂) c
    with ↣′-nil c
  ... | refl = fun-case {b = b} {b₁ = b₁} {b₂ = b₂} L₀ lw F₀ L₁ dt F₁ L₂ G₂ c bd
  step (s≤s bd) (lc-lam L₀ lw F₀) (Me-FOp′ {u = b} {u' = b₁} L₁ dt F₁) (Ms-FOp′ {u' = b₂} L₂ G₂) c =
    fop-case {b = b} {b₁ = b₁} {b₂ = b₂} L₀ lw F₀ L₁ dt F₁ L₂ G₂ c bd

commute : ∀ n → IH n
commute zero    ()
commute (suc n) = step n (commute n)
```

## Lemma 1′

```agda
join₁ : ∀ {Γ s Γ′ s′ t₀ t₁ t₂} → LC t₀
      → (e : Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁) (st : Γ ∣ s ⊢ t₀ ⟶ˢ′ t₂) (c : Γ ∣ s ↣′ Γ′ ∣ s′)
      → Join₁ e st c
join₁ {t₀ = t₀} lc e st c = commute (suc (tsize t₀)) (s≤s ≤-refl) lc e st c

Lem-1′ : ∀ {Γ s Γ′ s′ t₀ t₁ t₂} → LC t₀
       → Γ ∣ s ⊢ t₀ ⟶ᵉ′ t₁ → Γ ∣ s ⊢ t₀ ⟶ˢ′ t₂ → Γ ∣ s ↣′ Γ′ ∣ s′
       → ∃[ t₃ ] ((Γ ∣ s ⊢ t₂ ⟶ᵉ′ t₃) × (Γ′ ∣ s′ ⊢ t₁ ⟶ˢ′ t₃))
Lem-1′ {Γ = Γ} lc e st c with join₁ lc e st c
... | t₃ , f₁ , f₂ = t₃ , subst (λ Γ₁ → Γ₁ ∣ _ ⊢ _ ⟶ᵉ′ t₃) (∖-[] Γ) (f₁ [] (λ _ ()) (λ ()) (λ ())) , f₂
```

## What this establishes

`Lem-1′`: **strong commutation of the variant's subtyping and equivalence reductions**, with a
context reduction on the subtyping side, on locally closed subjects. Nothing is assumed: the
diamond it spends is `MPSS/VariantDiamond`'s, and the three cases `MPSS/Commutation` left open
are proved by induction on the size of the subject.
