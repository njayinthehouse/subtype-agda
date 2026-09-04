# Audit of the refutations

For each refuted claim: the paper's statement verbatim, the Agda statement refuted, a check that
the second faithfully represents the first, the paper's proof verbatim, and the step that fails.

---

## Proposition 18 (Reflexivity)

### The paper's statement

> **Proposition 18 (Reflexivity.).** Let `Γ;s` be an extended context, and `u` be a term, we have
> `Γ;s ⊢ u ⟶≤ u`, and `Γ;s ⊢ u ⟶≡ u`.

### What was refuted

`MPSS/ReflFails`, four statements:

- `Prop-18ᵉ = ∀ {Γ s u} → Γ ∣ s ⊢ u ⟶ᵉ u`
- `Prop-18ᵉ-lc = ∀ {Γ s u} → Γ ∣ s prevalid → LC u → Γ ∣ s ⊢ u ⟶ᵉ u`
- the same two for `⟶ˢ`

### Faithfulness

`Prop-18ᵉ` is the paper's statement transcribed with no additions: it quantifies over every
context, stack and term, as the paper does. The `-lc` variants **add** hypotheses the paper does
not have — that the extended context is prevalid and the term locally closed — so refuting them
refutes the paper's claim a fortiori. Together they cover both readings of "extended context" and
"term": the literal one, and the charitable one where those words carry the implicit hygiene
conditions a named presentation assumes.

The one reading not covered would be "term" implicitly meaning *scoped in `dom Γ`*. That
condition is nowhere stated in the paper, and it is precisely the repair — it is what
`⟶ᵉ-refl` in `MPSS/StackPush` carries.

### The paper's proof

> By straightforward induction on the derivation trees of `Γ;s ⊢ u ⟶≡ u`, noting that the only
> applicable rules at the leaves are `Me-Top` and `Me-Var`, and that at the rest of the nodes only
> rules `Me-App`, `Me-Fun`, and `Me-FOp` occur. To now prove `Γ;s ⊢ u ⟶≤ u`, we use rule `Ms-Equ`.

### Where it breaks

At the `Me-App` node. The rule is

> `Γ; v::s ⊢ u ⟶≡ u′    Γ; nil ⊢ v ⟶≡ v′  /  Γ; s ⊢ u v ⟶≡ u′ v′`

so its operator premise is taken at the **pushed** stack `v::s`. Every leaf of that sub-derivation
— `Me-Var`, `Me-Top`, `Me-Pro`, `Me-TAp` — carries the premise `Γ; v::s prevalid`, and `Pv-Sta`
grants that only when `fv(v) ⊆ dom(Γ)`. The proof observes that `Me-App` is the rule that "occurs"
at an application node without checking that its premise's extended context is prevalid at all.

Concretely: `u = y y` with `Γ = ε`. Then `fv(y) = {y} ⊄ ∅`, so `ε; y::nil` is not prevalid, so
the operator premise has no derivation, so `y y` does not reduce — to itself or to anything.

There is also a slip in the phrasing: the proof says it inducts "on the derivation trees of
`Γ;s ⊢ u ⟶≡ u`", which is the object being constructed. The induction can only be on `u`.

---

## Proposition 17 (From reduction semantics to equivalence reduction)

### The paper's statement

> **Proposition 17 (From reduction semantics to equivalence reduction.).** Let `u` and `v` be
> terms. If `u ↦ v` then `Γ;s ⊢ u ⟶≡ v` for all extended context `Γ;s`.

### What was refuted

`MPSS/BetaScope`:

- `Prop-17 = ∀ {Γ u v} → Γ ∣ [] prevalid → LC u → fv u ⊑ dom Γ → u ↦ v → Γ ∣ [] ⊢ u ⟶ᵉ v`

and `MPSS/BetaScopeWf`, the same failure on a **well-formed** subject.

### Faithfulness

`Prop-17` adds three hypotheses the paper does not have — prevalidity of the extended context,
local closure of the subject, and scoping of the subject in `dom Γ` — and fixes the stack to be
empty. All four make the statement *weaker* than the paper's, which quantifies over every
extended context with no conditions. Refuting the weaker statement refutes the paper's.

`MPSS/BetaScopeWf` closes the remaining gap in the audit. Proposition 17 is used only in Lemma 6
and Theorem 5, both of which apply it to well-formed terms, so it mattered whether the failure is
visible there. It is: with `T = λz≤Top.Top` and `y ≤ λq≤T.Top`, the redex `(λx≤T. y x) T` is
well-formed (`R-wf`), steps operationally to `y T` (`R↦`), and has no equivalence step to `y T`
(`no-step`).

### The paper's proof

> By induction on the derivation tree of `u ↦ v`. The base case is when the last rule used is
> `Os-Bet`, and the result holds by rule `Me-Bet` and reflexivity of `⟶≡` (Proposition 18). The
> induction cases is when the last rule used is `Os-Con`, and the result holds by induction and
> rules `Me-Fun`, `Me-FOp` and `Me-App`.

### Where it breaks

In the base case, and in two ways.

**First**, it invokes Proposition 18, which is false. That alone sinks the step.

**Second**, and independently of 18's status, the instance of `Me-Bet` the proof needs cannot be
built. The rule is

> `Γ;s ⊢ u ⟶≡ u′    Γ;nil ⊢ v ⟶≡ v′  /  Γ;s ⊢ (λx≤t.u) v ⟶≡ u′[x\v′]`

To match the `Os-Bet` contractum `u[x\v]` the proof must instantiate `u′ := u` and `v′ := v`, so
it needs `Γ;s ⊢ u ⟶≡ u` where `u` is the **body, with `x` free and `Γ` not binding it**. That is
not merely an instance of reflexivity; it is an instance of reflexivity *at a term the context
does not scope*, which is exactly the false case. When the body places `x` in operand position —
`u = y x` — the `Me-App` node inside needs `Γ; x::s` prevalid, and `Pv-Sta` refuses.

So the two defects are one defect seen twice: `Me-Bet` reduces its body in a context that does not
bind the parameter, while `Me-App` and `Pv-Sta` together demand that everything pushed be scoped.

### Consequence

Lemma 6 cites Proposition 17 in its `Os-Con` cases and Theorem 5 cites it for the `Ws-Rgh` step;
both are on well-formed terms, and `MPSS/BetaScopeWf` shows the failure reaches them. The repair
is to bind the parameter in `Me-Bet`'s body premise, as `Me-Fun` and `Me-FOp` already do. That
changes `⟶ᵉ`, so Lemma 1 and Lemma 2 would need rechecking against the repaired relation.

---

## Further defects, found while discharging the obligations

These are not refutations — each statement below is true and is proved in this development. What
is wrong is the paper's own justification for it.

### Proposition 27: the wrong rule is cited

> **Proposition 27 (Reduction preserves subtyping derivation).** Let `Γ;s` be an extended context.
> Let `u`, `u′` and `v` be terms such that `Γ ⊢ u ≤*wf v` and `u ↦ u′`, and `Γ ⊢ u′ wf`. Then
> `Γ ⊢ u′ ≤*wf v`.

The proof reads:

> By 17, we have `Γ;nil ⊢ u ⟶≡ u′`. By rule `Ws-Rfl` and `Ws-Lf1`, we have `Γ ⊢ u′ ≤wf u`. […]

`Ws-Lf1` moves the **left**-hand side:

> `Γ;nil ⊢ v ⟶≡ v′    Γ ⊢ v′ ≤wf t  /  Γ ⊢ v ≤wf t`

so from `u ⟶≡ u′` and `Ws-Rfl : u′ ≤wf u′` it yields `Γ ⊢ u ≤wf u′` — the opposite of what is
claimed. The rule that gives the stated conclusion is `Ws-Rgh`, which moves the right-hand side,
and which the paper's own proof of Theorem 5 cites for this very step. The conclusion stands;
`MPSS/Preservation` derives it with `Ws-Rgh`.

### Theorem 5: an uncited dependency on Proposition 17

The proof of Theorem 5 says "hence `Γ ⊢ t′ ≤*wf t` by rule `Ws-Rgh`", having just obtained
`Γ ⊢ t′ ≤*wf t′`. `Ws-Rgh` needs an equivalence step `Γ;nil ⊢ t ⟶≡ t′`, and all that is in hand
is the operational step `t ↦ t′`. Bridging them is exactly Proposition 17, which is not cited
here. So Theorem 5 depends on the refuted proposition in its own right, not only through Lemma 6.

### Lemma 23: the `Wf-App` case, and a correction

> To do so, we do the same reasoning as in Lemma 7 by using instead Lemmas 24 and 25.

**An earlier entry here claimed this deferral does not reach the case. That claim was wrong and
is withdrawn.** It was based on a reconstruction in which narrowing a `≤wf` chain forces the
conclusion to be starred at the first `Ws-Lf2`, after which every other rule must be reassembled
through `Ws-Sub` — which demands well-formedness at the `Ws-Lf1` and `Ws-Rgh` intermediates,
where the rules do not provide it.

Lemma 7's actual reasoning does not work that way, and does not need those intermediates to be
well-formed. Its sub-induction produces, for each single step `a ≤wf b`, an existential diagram —
terms `a′`, `b′`, `c` with `a[x\α] ⟶≡↠ a′[x\α]`, `b[x\α] ⟶≡↠ c[x\α]`,
`b′[x\α] ⟶≡↠ c[x\α]`, and `a′[x\α] ≤*wf b′[x\α]` — so the equivalence steps are accumulated as
*reduction sequences* rather than as `⊑wf` steps needing to be starred. Reassembly then uses
well-formedness only at the chain's endpoints, which `Ws-Sub` supplies, and at the `Ws-Lf2` nodes,
which carry it as premises. The same shape transfers to narrowing with Lemmas 24 and 25 in place
of Lemma 31.

So the deferral is legitimate in outline. What remains true is narrower: neither Lemma 7 nor
Lemma 23 is written out for its hardest case, and the technique they share is stated only once,
inside another lemma's proof.

**What `MPSS/EqvWf` does and does not show.** It refutes "`⟶≡` preserves well-formedness", which
is the *naive* route to Lemma 23 — the one that narrows a chain step by step and needs each
intermediate to be well-formed. The paper never claims that statement, and its diagram technique
avoids needing it. The refutation stands on its own as a fact about MPSS: well-formedness is not
stable under the reduction its subtyping is built from, because contexts carry a scoping condition
where they would need a typing one. It is not evidence against Lemma 23.

---

## Lemma 2: the induction is not well-founded as written

This is an analysis of the proof, not a refutation of the statement. No counterexample to the
diamond property is claimed.

### What the proof says

> We now proceed by induction on the derivation tree of `Γ₀;s₀ ⊢ t₀ ⟶≡ t₁`.

and then, in the case where the two edges end in `Me-Pro` and `Me-Var`:

> By Lemma 36, `Γ₀;s₀ ↣ Γ₂;s₂` implies `Γ₀;nil ↣ Γ₂;nil`. Because `Γ₀` is of the form
> `Γ₀′, x ≡ α₀, Γ₀″`, we have `Γ₂ = Γ₂′, x ≡ α₂, Γ₂″`. By multiple use of the rule `Ct-Ann`, we
> have `Γ₀′;nil ⊢ α₀ ⟶≡ α₂`. By weakening (Lemma 19), we have `Γ₀;s₀ ⊢ α₀ ⟶≡ α₂`. By induction
> hypothesis on `Γ₀;s₀ ⊢ α₀ ⟶≡ α₁` […]

### The step that fails

The induction hypothesis is applied to the pair `(α₀ ⟶≡ α₁, α₀ ⟶≡ α₂)`. The first component is a
subderivation of the `Me-Pro` edge. **The second is not a subderivation of anything.** It is
constructed, by `Ct-Ann` and weakening, out of the context reduction `Γ₀;s₀ ↣ Γ₂;s₂` — a
hypothesis of the lemma, not part of either derivation being inducted on, and of unrelated size.

The two edges are also not consistently oriented. Induction "on the derivation of `t₀ ⟶≡ t₁`"
would make `t₁` the horizontal edge, but in this case the IH is applied to a subderivation of the
edge ending in `Me-Pro`, which the case names as the *other* one. In the mirror orientation the
roles swap, so no single edge carries the induction.

### Why the obvious repairs do not work

Writing `|d|` for derivation size and `S` for the fixed context reductions:

- **Sum or multiset of `|d₁|, |d₂|`.** In `Me-Var`/`Me-Pro` the pair `(1, 1+k)` becomes `(m, k)`
  where `m` is the size of the piece extracted from `S`. Nothing bounds `m` by `k`.
- **Lexicographic `(|d₂|, |d₁|)`.** Works in this orientation and fails in the mirror one, where
  it is `|d₁|` that shrinks and `|d₂|` that is replaced by a piece of `S`. Symmetry does not
  rescue it: the order is not symmetric, and making it so (`max`, `min`, multiset) reintroduces
  the unbounded `m`.
- **A term measure with the context unfolded.** Assign each variable a weight one greater than
  its annotation's, which is well defined because prevalidity forces an annotation to be scoped
  strictly earlier in the context. `Me-Pro` then strictly decreases it. But `Me-FOp` moves the
  stack head into the context as an equivalence annotation, so the body is measured with the
  bound variable weighted by the *stack head* rather than by the abstraction's own annotation,
  and the measure increases whenever the head is heavier. Repairing that by charging the stack
  additively with a coefficient at least the number of bound occurrences breaks `Me-App`, which
  pushes the operand and needs the coefficient to be at most one. Charging it multiplicatively
  fixes `Me-FOp` and breaks `Me-App` the same way.
- **Lexicographic `(configuration depth, term depth, derivation size)`,** with configuration
  depth `max(ρ u, maxᵢ (1 + ρ sᵢ))`. `Me-Pro` decreases the second component and `Me-App` the
  third, but `Me-FOp` increases the second while leaving the first equal, since the bound
  variable's weight `1 + ρ α` is exactly the stack entry's contribution.

The obstruction is stable across these: `Me-Pro` needs a variable lookup to cost strictly more
than its annotation, and `Me-FOp` needs a stack entry to cost at least as much as the variable it
becomes. Those two are in direct conflict, and it is `Me-FOp` — the rule that lets an abstraction
under an operand bind its parameter to that operand — that creates it.

None of this shows the diamond is false, and none of it rules out a measure of some other shape.
What it shows is that the proof as printed does not carry one, and that the missing ingredient is
specifically an accounting for the `Me-Pro`/`Me-FOp` interaction.

---

## Lemma 24: the well-formedness conclusion is not established

> **Lemma 24 (Narrowing of context in subtyping reductions).** […] Then there exists a term `v′`
> such that `Γ, x≤t′, Γ′; nil ⊢ u ⟶≤ v′`, and `Γ, x≤t′, Γ′; nil ⊢ v ⟶≤ v′`, and
> **`Γ, x≤t′, Γ′ ⊢ v′ wf`**.

The third conclusion is what Lemma 23 needs and cannot do without: its `Ws-Lf2` case has a
promotion whose target moves under narrowing, and `Ws-Lf2` will not accept the new target without
its well-formedness. `MPSS/Narrowing24` proves the first two conclusions — with the join
strengthened from `⟶≤` to `⟶≡` — and not the third.

The paper's argument for the third is:

> We now need to show that `v′` is well-formed in context `Γ, x≤t′, Γ′` **by induction on the
> structure of `v′`**.

and it fails in three separate ways.

**It proves too much.** Three of the four cases use no hypothesis relating `v′` to `u` at all:

> Case `v′ = x`: A variable is well-formed by rule `Wf-PrS` or `Wf-PrE`.
> Case `v′ = Top`: We have `Γ, x≤t′, Γ′ ⊢ Top wf` by rule `Wf-Top`.

An induction that establishes well-formedness from the shape of a term alone would establish it
for every term, and `Top Top` is not well-formed — `Wf-App` would put `Top` below an abstraction,
which Theorem 11 forbids. Well-formedness is not a structural property, precisely because
`Wf-App` carries subtyping premises.

**The abstraction case asserts its conclusion.**

> Case `v′ = λy≤t″.w`: We have `Γ, x≤t′, Γ′ ⊢ λy≤t″.w wf` by rule `Wf-Fun` with premise
> `Γ, x≤t′, Γ′, y≤t″ ⊢ w wf`. By the induction hypothesis, we have `Γ, x≤t′, Γ′, y≤t″ ⊢ w wf`.

The goal is stated as though established, and the premise it reduces to is then said to follow by
an induction hypothesis — but the induction is on the structure of `v′`, and the statement being
proved is about the one `v′` the lemma produces, not about arbitrary terms, so there is no such
hypothesis for the body. `Wf-Fun`'s second premise, `Γ, x≤t′, Γ′ ⊢ t″ wf`, is not mentioned.

**The application case pushes a promotion the wrong way.** Here `u = Co[x]` and `v′ = Co[t′]`, so
with `v′ = a b` the corresponding part of `u` is `a′ b`, where `a′` is `a` with `x` where `a` has
`t′`. From `u` well-formed the proof has `Γ, x≤t′, Γ′ ⊢ a′ ≤*wf λy≤w.Top`, and it needs the same
for `a`. It writes:

> Because `a′` is `a` but with a promotion of `x` to `t` in head position, we have
> `Γ, x≤t′, Γ′ ⊢ a ≤wf a′` from rule `Ws-Lf2`.

In the narrowed context `x` promotes to `t′`, not to `t`, so the step available is `a′ ⟶≤ a`, and
`Ws-Lf2` gives `Γ, x≤t′, Γ′ ⊢ a′ ≤wf a` — the opposite of what is written. Nor does the
correctly-oriented fact help: from `a′ ≤*wf λy≤w.Top` and `a′ ≤wf a` one cannot conclude
`a ≤*wf λy≤w.Top`, any more than `x ≤ Int` and `x ≤ String` give `Int ≤ String`. Recovering the
conclusion would need `⟶≤` to be confluent, which is not among the paper's results — it proves
the diamond for `⟶≡` and commutation of the two, not confluence of `⟶≤`.

**Status: the statement is true, and is now proved here by a different route.** `MPSS/CoNarrow`
inducts on the covariant context, carrying `Co′[t] ≤*wf λy≤w.Top` across the step
`Co′[t] ⟶≡ Co′[t′]` with `push≡*wf`, and proves that congruence simultaneously; the depth of the
context is the measure, since opening preserves it. The promotion itself is rebuilt in
`MPSS/CoPromote` from the covariant context rather than from the old derivation — which is what
keeps `Ms-Fun`'s cofinite family uniform, the difficulty that a derivation-directed argument runs
into. `MPSS/Lemma23` then proves Lemma 23 outright.

So the defect is in the argument, not the claim.
