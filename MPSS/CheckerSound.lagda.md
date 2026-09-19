# MPSS: the checker is sound

`MPSS/CheckerFns` decides nothing; it searches, with fuel, along the one route the source typing
suggests. Here: whatever it accepts is derivable.

    wf-sound   wf? n m Γ t ≡ true                    gives  Γ ⊢ t wf
    dom-sound  dom? n m Γ k w ≡ just d               gives  Γ ⊢ w ≤wf λx≤d.⊤  and  Γ ⊢ λx≤d.⊤ wf
    sub-sound  sub? n m Γ k v t ≡ true               gives  Γ ⊢ v₀ ≤*wf t

for a prevalid `Γ`. In `sub-sound`, `v₀` is the term the search started from and `v` the term it
has reached by head steps and head promotions, all inside one `Ws-Sub` layer; the layer built so
far is carried as a function from layers at `v` to layers at `v₀`. A head step leaves a term that
is not known to be well-formed (that is Lemma 6), so the flag `k` records whether `v` is, and
`Ws-Lf2`'s two well-formedness premises are checked where they are not known.

Under a binder the checker works at one fresh name; the derivations are closed up by
`wrap-wf` (`MPSS/Prop17Chain`) and `chain-fun` (`MPSS/CoFun`).

Nothing existing is modified.

```agda
{-# OPTIONS --safe #-}

module MPSS.CheckerSound where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import MPSS.WellFormed
open import MPSS.StackPush
open import MPSS.Narrow using (wf-fv)
open import MPSS.Scope using (⟶ᵉ-lc)
open import MPSS.Strip using (_∣_⊢_⟶ᵉ*_; ε; _◅_; ⟶ᵉ*-lc) renaming (_++_ to _++ᵉ_)
open import MPSS.Prop17Chain using (wrap-wf)
open import MPSS.CoFun using (chain-fun)
open import MPSS.WfRename using (wf-rename-head)
open import MPSS.CoPair using (_≟Tm_)
open import MPSS.CheckerFns
open import MPSS.NormalizeSound
open import PSS.Syntax
open import PSS.Close using (close-open)
```

## Booleans

```agda
∧-l : ∀ a {b} → a ∧ b ≡ true → a ≡ true
∧-l true  _ = refl
∧-l false ()

∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
∧-r true  e = e
∧-r false ()

if-maybe : ∀ {A : Set} c {r : Maybe A} {y} → (if c then r else nothing) ≡ just y
         → (c ≡ true) × (r ≡ just y)
if-maybe true  e = refl , e
if-maybe false ()

data Ite (c x y : Bool) : Set where
  then-branch : c ≡ true  → x ≡ true → Ite c x y
  else-branch : c ≡ false → y ≡ true → Ite c x y

ite : ∀ c {x y} → (if c then x else y) ≡ true → Ite c x y
ite true  e = then-branch refl e
ite false e = else-branch refl e
```

## The small functions

```agda
lamView-sound : ∀ w {a b} → lamView w ≡ just (a , b) → w ≡ lam a b
lamView-sound (lam a b) refl = refl
lamView-sound (bvar _)  ()
lamView-sound (fvar _)  ()
lamView-sound Top       ()
lamView-sound (app _ _) ()

isTop-sound : ∀ w → isTop w ≡ true → w ≡ Top
isTop-sound Top       _ = refl
isTop-sound (bvar _)  ()
isTop-sound (fvar _)  ()
isTop-sound (lam _ _) ()
isTop-sound (app _ _) ()

bound?-sound : ∀ Γ {x} → bound? Γ x ≡ true → ∃[ a ] ∃[ t ] ((x , a , t) ∈ Γ)
bound?-sound [] ()
bound?-sound ((y , a , t) ∷ Γ) {x} e with x ≟ y
... | yes refl = a , t , here refl
... | no  _    with bound?-sound Γ e
...   | a′ , t′ , m = a′ , t′ , there m

lookupˢ-sound : ∀ Γ {x t} → lookupˢ Γ x ≡ just t → x ≤ t ∈ Γ
lookupˢ-sound [] ()
lookupˢ-sound ((y , sub , u) ∷ Γ) {x} e with x ≟ y
lookupˢ-sound ((y , sub , u) ∷ Γ) {x} refl | yes refl = here refl
... | no _ = there (lookupˢ-sound Γ e)
lookupˢ-sound ((y , eqv , u) ∷ Γ) {x} e with x ≟ y
lookupˢ-sound ((y , eqv , u) ∷ Γ) {x} () | yes _
... | no _ = there (lookupˢ-sound Γ e)

-- the head promotion is a promotion, at any stack
phead-sound : ∀ {Γ s} t {p} → Γ ∣ s prevalid → LC t → Scoped Γ t
            → phead Γ t ≡ just p → Γ ∣ s ⊢ t ⟶ˢ p
phead-sound {Γ} (fvar x) pv lt ft e = Ms-Pro pv (lookupˢ-sound Γ e)
phead-sound {Γ} (app f v) pv (lc-app lf lv) ft e with phead Γ f in eq
phead-sound {Γ} (app f v) pv (lc-app lf lv) ft refl | just r =
  Ms-App (phead-sound f (Pv-Sta pv lv (fv-app-arg {f} {v} ft)) lf (fv-app-op {f} {v} ft) eq)
phead-sound {Γ} (app f v) pv (lc-app lf lv) ft () | nothing
phead-sound (bvar _)  pv lt ft ()
phead-sound Top       pv lt ft ()
phead-sound (lam _ _) pv lt ft ()
```

## Layers

```agda
lf1* : ∀ {Γ v v′ t m} → Γ ∣ [] ⊢ v ⟶ᵉ* v′ → Γ ⊢ v′ ⊑wf[ m ] t → Γ ⊢ v ⊑wf[ m ] t
lf1* (ε _)   d = d
lf1* (e ◅ p) d = Ws-Lf1 e (lf1* p d)

rgh* : ∀ {Γ v t t′ m} → Γ ⊢ v ⊑wf[ m ] t′ → Γ ∣ [] ⊢ t ⟶ᵉ* t′ → Γ ⊢ v ⊑wf[ m ] t
rgh* d (ε _)   = d
rgh* d (e ◅ p) = Ws-Rgh (rgh* d p) e

join-layer : ∀ {Γ v t} → Γ prevalid → Joins Γ v t → Γ ⊢ v ⊑wf[ sub-m ] t
join-layer pv (c , p , q) = lf1* p (rgh* (Ws-Rfl pv) q)

-- the body of a well-formed abstraction, at any name the context does not bind
wf-body : ∀ {Γ a b} x → x ∉ dom Γ → Γ ⊢ lam a b wf → ((x , sub , a) ∷ Γ) ⊢ (b ^ fvar x) wf
wf-body {Γ} {a} {b} x x∉ (Wf-Fun L Fm wa) =
  subst (λ q → ((x , sub , a) ∷ Γ) ⊢ q wf) (sym (subst-intro {b} lc-fvar z z∉b))
        (wf-rename-head x∉z (Fm z∉L))
  where
    A   = L ++ fv b ++ (x ∷ dom Γ)
    z   = fresh A
    z∉L = ∉-++ˡ (fresh-∉ A)
    z∉b = ∉-++ˡ (∉-++ʳ L (fresh-∉ A))
    z∉x : z ∉ (x ∷ dom Γ)
    z∉x = ∉-++ʳ (fv b) (∉-++ʳ L (fresh-∉ A))
    x∉z : x ∉ (z ∷ dom Γ)
    x∉z (here p)  = z∉x (here (sym p))
    x∉z (there m) = x∉ m

wf-ann : ∀ {Γ a b} → Γ ⊢ lam a b wf → Γ ⊢ a wf
wf-ann (Wf-Fun _ _ wa) = wa

-- known, or checked
known : ∀ {P : Set} k {c} → (k ≡ true → P) → (c ≡ true → P) → k ∨ c ≡ true → P
known true  f g _ = f refl
known false f g e = g e
```

## Soundness

```agda
wf-sound  : ∀ n m {Γ t} → Γ prevalid → wf? n m Γ t ≡ true → Γ ⊢ t wf

dom-sound : ∀ n m {Γ k w d} → Γ prevalid → LC w → Scoped Γ w → (k ≡ true → Γ ⊢ w wf)
          → dom? n m Γ k w ≡ just d
          → (Γ ⊢ w ⊑wf[ sub-m ] lam d Top) × (Γ ⊢ lam d Top wf)

sub-sound : ∀ n m {Γ k v t v₀} → Γ prevalid → LC v → Scoped Γ v → (k ≡ true → Γ ⊢ v wf)
          → Γ ⊢ t wf → Γ ⊢ v₀ wf
          → (∀ {u} → Γ ⊢ v ⊑wf[ sub-m ] u → Γ ⊢ v₀ ⊑wf[ sub-m ] u)
          → sub? n m Γ k v t ≡ true → Γ ⊢ v₀ ⊑*wf[ sub-m ] t

domV-sound : ∀ n m {Γ k w d} mv → lamView w ≡ mv
           → Γ prevalid → LC w → Scoped Γ w → (k ≡ true → Γ ⊢ w wf)
           → domV n m Γ k w mv ≡ just d
           → (Γ ⊢ w ⊑wf[ sub-m ] lam d Top) × (Γ ⊢ lam d Top wf)

domStep-sound : ∀ n m {Γ k w d} mp mh → phead Γ w ≡ mp → hred w ≡ mh
              → Γ prevalid → LC w → Scoped Γ w → (k ≡ true → Γ ⊢ w wf)
              → domStep n m Γ k w mp mh ≡ just d
              → (Γ ⊢ w ⊑wf[ sub-m ] lam d Top) × (Γ ⊢ lam d Top wf)

subV-sound : ∀ n m {Γ k v t v₀} mv mt → lamView v ≡ mv → lamView (whnf m t) ≡ mt
           → Γ prevalid → LC v → Scoped Γ v → (k ≡ true → Γ ⊢ v wf)
           → Γ ⊢ t wf → Γ ⊢ v₀ wf
           → (∀ {u} → Γ ⊢ v ⊑wf[ sub-m ] u → Γ ⊢ v₀ ⊑wf[ sub-m ] u)
           → subV n m Γ k v t (whnf m t) mv mt ≡ true → Γ ⊢ v₀ ⊑*wf[ sub-m ] t

subGen-sound : ∀ n m {Γ k v t v₀} tw
             → Γ prevalid → LC v → Scoped Γ v → (k ≡ true → Γ ⊢ v wf)
             → Γ ⊢ t wf → Γ ⊢ v₀ wf
             → (∀ {u} → Γ ⊢ v ⊑wf[ sub-m ] u → Γ ⊢ v₀ ⊑wf[ sub-m ] u)
             → subGen n m Γ k v t tw ≡ true → Γ ⊢ v₀ ⊑*wf[ sub-m ] t

subStep-sound : ∀ n m {Γ k v t v₀} mp mh → phead Γ v ≡ mp → hred v ≡ mh
              → Γ prevalid → LC v → Scoped Γ v → (k ≡ true → Γ ⊢ v wf)
              → Γ ⊢ t wf → Γ ⊢ v₀ wf
              → (∀ {u} → Γ ⊢ v ⊑wf[ sub-m ] u → Γ ⊢ v₀ ⊑wf[ sub-m ] u)
              → subStep n m Γ k v t mp mh ≡ true → Γ ⊢ v₀ ⊑*wf[ sub-m ] t

subLam-sound : ∀ n m {Γ k a b a′ b′ t v₀} → whnf m t ≡ lam a′ b′
             → Γ prevalid → (k ≡ true → Γ ⊢ lam a b wf)
             → Γ ⊢ t wf → Γ ⊢ v₀ wf
             → (∀ {u} → Γ ⊢ lam a b ⊑wf[ sub-m ] u → Γ ⊢ v₀ ⊑wf[ sub-m ] u)
             → subLam n m Γ k a b a′ b′ ≡ true → Γ ⊢ v₀ ⊑*wf[ sub-m ] t
```

### Well-formedness

```agda
wf-sound zero    m pv ()
wf-sound (suc n) m {Γ} {bvar i} pv ()
wf-sound (suc n) m {Γ} {fvar x} pv e with bound?-sound Γ e
... | sub , t , mem = Wf-PrS pv mem
... | eqv , t , mem = Wf-PrE pv mem
wf-sound (suc n) m {Γ} {Top} pv e = Wf-Top pv
wf-sound (suc n) m {Γ} {lam a b} pv e =
  subst (λ q → Γ ⊢ lam a q wf) (close-open 0 x b x∉b) (wrap-wf x x∉Γ (wf⇒lc wx) wx wa)
  where
    A   = dom Γ ++ fv b
    x   = fresh A
    x∉Γ = ∉-++ˡ (fresh-∉ A)
    x∉b = ∉-++ʳ (dom Γ) (fresh-∉ A)
    wa  = wf-sound n m pv (∧-l (wf? n m Γ a) e)
    wx  = wf-sound n m (Pv-Ctx pv x∉Γ (wf⇒lc wa) (wf-fv wa)) (∧-r (wf? n m Γ a) e)
wf-sound (suc n) m {Γ} {app f v} pv e with dom? n m Γ true f in eq
wf-sound (suc n) m {Γ} {app f v} pv e | nothing
  with ∧-r (wf? n m Γ v) (∧-r (wf? n m Γ f) e)
... | ()
wf-sound (suc n) m {Γ} {app f v} pv e | just d =
  Wf-App (Ws-Sub wf-f (proj₁ ds) (proj₂ ds))
         (sub-sound n m pv (wf⇒lc wf-v) (wf-fv wf-v) (λ _ → wf-v) (wf-ann (proj₂ ds)) wf-v
                    (λ l → l) (∧-r (wf? n m Γ v) (∧-r (wf? n m Γ f) e)))
  where
    wf-f = wf-sound n m pv (∧-l (wf? n m Γ f) e)
    wf-v = wf-sound n m pv (∧-l (wf? n m Γ v) (∧-r (wf? n m Γ f) e))
    ds   = dom-sound n m pv (wf⇒lc wf-f) (wf-fv wf-f) (λ _ → wf-f) eq
```

### The domain of an operator

```agda
dom-sound zero    m pv lw fw kw ()
dom-sound (suc n) m {w = w} pv lw fw kw e = domV-sound n m (lamView w) refl pv lw fw kw e

domV-sound n m {Γ} {k} {w} (just (d′ , b)) ev pv lw fw kw e with lamView-sound w ev
domV-sound n m {Γ} {k} (just (d′ , b)) ev pv lw fw kw e | refl
  with if-maybe ((k ∨ wf? n m Γ (lam d′ b)) ∧ wf? n m Γ (lam d′ Top)) e
... | c , refl =
  Ws-Lf2 ww pro wt (Ws-Rfl pv) , wt
  where
    ww : Γ ⊢ lam d′ b wf
    ww = known k kw (wf-sound n m pv) (∧-l (k ∨ wf? n m Γ (lam d′ b)) c)
    wt : Γ ⊢ lam d′ Top wf
    wt = wf-sound n m pv (∧-r (k ∨ wf? n m Γ (lam d′ b)) c)
    wd = wf-ann wt
    pro : Γ ∣ [] ⊢ lam d′ b ⟶ˢ lam d′ Top
    pro = Ms-Fun {u' = Top} (dom Γ)
            (λ {z} z∉ → Ms-Top (Pv-Nil (Pv-Ctx pv z∉ (wf⇒lc wd) (wf-fv wd))))
domV-sound n m {w = w} nothing ev pv lw fw kw e =
  domStep-sound n m (phead _ w) (hred w) refl refl pv lw fw kw e

domStep-sound n m {Γ} {k} {w} (just p) mh ep eh pv lw fw kw e
  with if-maybe ((k ∨ wf? n m Γ w) ∧ wf? n m Γ p) e
... | c , e′ =
  Ws-Lf2 ww (phead-sound w (Pv-Nil pv) lw fw ep) wp (proj₁ rec) , proj₂ rec
  where
    ww : Γ ⊢ w wf
    ww = known k kw (wf-sound n m pv) (∧-l (k ∨ wf? n m Γ w) c)
    wp : Γ ⊢ p wf
    wp = wf-sound n m pv (∧-r (k ∨ wf? n m Γ w) c)
    rec = dom-sound n m pv (wf⇒lc wp) (wf-fv wp) (λ _ → wp) e′
domStep-sound n m {Γ} {k} {w} nothing (just w′) ep eh pv lw fw kw e =
  lf1* ch (proj₁ rec) , proj₂ rec
  where
    ch  = hred-sound w (Pv-Nil pv) lw fw eh
    rec = dom-sound n m {k = false} pv (⟶ᵉ*-lc lw ch) (⟶ᵉ*-fv fw ch) (λ ()) e
domStep-sound n m nothing nothing ep eh pv lw fw kw ()
```

### One operand against a bound

```agda
sub-sound zero    m pv lv fv′ kv wt w₀ K ()
sub-sound (suc n) m {Γ} {k} {v} {t} pv lv fv′ kv wt w₀ K e
  with ite (isTop (whnf m t)) e
... | then-branch c₁ c₂ =
  Ws-Sub w₀ (K (Ws-Lf2 wv (Ms-Top (Pv-Nil pv)) (Wf-Top pv) (rgh* (Ws-Rfl pv) tt′))) wt
  where
    wv : Γ ⊢ v wf
    wv = known k kv (wf-sound n m pv) c₂
    tt′ : Γ ∣ [] ⊢ t ⟶ᵉ* Top
    tt′ = subst (λ q → Γ ∣ [] ⊢ t ⟶ᵉ* q) (isTop-sound (whnf m t) c₁)
                (whnf-sound m (Pv-Nil pv) (wf⇒lc wt) (wf-fv wt))
... | else-branch c₁ c₂ with v ≟Tm t
...   | yes refl = Ws-Sub w₀ (K (Ws-Rfl pv)) wt
...   | no  _    = subV-sound n m (lamView v) (lamView (whnf m t)) refl refl pv lv fv′ kv wt w₀ K c₂

subV-sound n m {v = v} (just (a , b)) (just (a′ , b′)) ev et pv lv fv′ kv wt w₀ K e
  with lamView-sound v ev
... | refl = subLam-sound n m (lamView-sound _ et) pv kv wt w₀ K e
subV-sound n m {t = t} (just (a , b)) nothing ev et pv lv fv′ kv wt w₀ K e =
  subGen-sound n m (whnf m t) pv lv fv′ kv wt w₀ K e
subV-sound n m {t = t} nothing (just _) ev et pv lv fv′ kv wt w₀ K e =
  subGen-sound n m (whnf m t) pv lv fv′ kv wt w₀ K e
subV-sound n m {t = t} nothing nothing ev et pv lv fv′ kv wt w₀ K e =
  subGen-sound n m (whnf m t) pv lv fv′ kv wt w₀ K e

subGen-sound n m {Γ} {k} {v} {t} tw pv lv fv′ kv wt w₀ K e
  with ite (guard v tw ∧ conv m (dom Γ) v t) e
... | then-branch c _ =
  Ws-Sub w₀ (K (join-layer pv (conv-sound m pv lv fv′ (wf⇒lc wt) (wf-fv wt) (∧-r (guard v tw) c)))) wt
... | else-branch _ c =
  subStep-sound n m (phead Γ v) (hred v) refl refl pv lv fv′ kv wt w₀ K c

subStep-sound n m {Γ} {k} {v} {t} (just p) mh ep eh pv lv fv′ kv wt w₀ K e =
  sub-sound n m pv (wf⇒lc wp) (wf-fv wp) (λ _ → wp) wt w₀
            (λ l → K (Ws-Lf2 wv (phead-sound v (Pv-Nil pv) lv fv′ ep) wp l))
            (∧-r (wf? n m Γ p) (∧-r (k ∨ wf? n m Γ v) e))
  where
    wv : Γ ⊢ v wf
    wv = known k kv (wf-sound n m pv) (∧-l (k ∨ wf? n m Γ v) e)
    wp : Γ ⊢ p wf
    wp = wf-sound n m pv (∧-l (wf? n m Γ p) (∧-r (k ∨ wf? n m Γ v) e))
subStep-sound n m {Γ} {k} {v} {t} nothing (just v′) ep eh pv lv fv′ kv wt w₀ K e =
  sub-sound n m {k = false} pv (⟶ᵉ*-lc lv ch) (⟶ᵉ*-fv fv′ ch) (λ ()) wt w₀
            (λ l → K (lf1* ch l)) e
  where ch = hred-sound v (Pv-Nil pv) lv fv′ eh
subStep-sound n m nothing nothing ep eh pv lv fv′ kv wt w₀ K ()
```

### Two abstractions

`λx≤a.b` against a `t` that reduces to `λx≤a′.b′`, with `a` and `a′` convertible: first the
bodies under `x ≤ a` (`chain-fun`), which gives `λx≤a.b ≤*wf λx≤a.b′`; then one more layer,
in which both annotations reduce to their common reduct.

```agda
subLam-sound n m {Γ} {k} {a} {b} {a′} {b′} {t} {v₀} et pv kv wt w₀ K e =
  Ws-Trs (Ws-Sub w₀ (K (Ws-Rfl pv)) wv) wv
         (Ws-Trs bodies wmid (Ws-Sub wmid last wt))
  where
    A   = dom Γ ++ fv b ++ fv b′
    x   = fresh A
    Γx  = (x , sub , a) ∷ Γ
    c₁  = k ∨ wf? n m Γ (lam a b)
    c₂  = conv m (dom Γ) a a′
    c₃  = wf? n m Γx (b′ ^ fvar x)
    e₁  = ∧-l c₁ e
    e₂  = ∧-l c₂ (∧-r c₁ e)
    e₃  = ∧-l c₃ (∧-r c₂ (∧-r c₁ e))
    e₄  = ∧-r c₃ (∧-r c₂ (∧-r c₁ e))
    x∉Γ = ∉-++ˡ (fresh-∉ A)
    x∉b = ∉-++ˡ (∉-++ʳ (dom Γ) (fresh-∉ A))
    x∉b′ = ∉-++ʳ (fv b) (∉-++ʳ (dom Γ) (fresh-∉ A))

    wv : Γ ⊢ lam a b wf
    wv = known k kv (wf-sound n m pv) e₁
    wa = wf-ann wv
    pvx : ((x , sub , a) ∷ Γ) prevalid
    pvx = Pv-Ctx pv x∉Γ (wf⇒lc wa) (wf-fv wa)
    wbx  = wf-body x x∉Γ wv
    wb′x = wf-sound n m pvx e₃

    bodies : Γ ⊢ lam a b ⊑*wf[ sub-m ] lam a b′
    bodies =
      subst₂ (λ p q → Γ ⊢ lam a p ⊑*wf[ sub-m ] lam a q)
             (close-open 0 x b x∉b) (close-open 0 x b′ x∉b′)
             (chain-fun x x∉Γ wa
                (sub-sound n m pvx (wf⇒lc wbx) (wf-fv wbx) (λ _ → wbx) wb′x wbx (λ l → l) e₄))

    wmid : Γ ⊢ lam a b′ wf
    wmid = subst (λ q → Γ ⊢ lam a q wf) (close-open 0 x b′ x∉b′)
                 (wrap-wf x x∉Γ (wf⇒lc wb′x) wb′x wa)

    -- t ⟶ᵉ* λx≤a′.b′
    tw : Γ ∣ [] ⊢ t ⟶ᵉ* lam a′ b′
    tw = subst (λ q → Γ ∣ [] ⊢ t ⟶ᵉ* q) et (whnf-sound m (Pv-Nil pv) (wf⇒lc wt) (wf-fv wt))
    ll′ : LC (lam a′ b′)
    ll′ = ⟶ᵉ*-lc (wf⇒lc wt) tw
    fl′ : Scoped Γ (lam a′ b′)
    fl′ = ⟶ᵉ*-fv (wf-fv wt) tw
    la′ : LC a′
    la′ with ll′
    ... | lc-lam _ l _ = l

    js = conv-sound m pv (wf⇒lc wa) (wf-fv wa) la′ (fv-lam-ann {a′} {b′} fl′) e₂

    last : Γ ⊢ lam a b′ ⊑wf[ sub-m ] t
    last = lf1* (lam-ann* (wf⇒lc wmid) (wf-fv wmid) (proj₁ (proj₂ js)))
                (rgh* (Ws-Rfl pv) (tw ++ᵉ lam-ann* ll′ fl′ (proj₂ (proj₂ js))))
```

## What this establishes

`wf-sound`, `dom-sound`, `sub-sound`: for a prevalid context, a `true` from the checker is a
derivation. With `MPSS/CheckerFns` this is a proof-producing, fuel-bounded search for
well-formedness in MPSS; it is sound and makes no claim to completeness.
