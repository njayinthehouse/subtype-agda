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

In the base case, and in two ways. The independent one comes first, because it is the one that
survives every repair to Proposition 18.

**First**, the instance of `Me-Bet` the proof needs cannot be built at all. The rule is

> `Γ;s ⊢ u ⟶≡ u′    Γ;nil ⊢ v ⟶≡ v′  /  Γ;s ⊢ (λx≤t.u) v ⟶≡ u′[x\v′]`

To match the `Os-Bet` contractum `u[x\v]` the proof must instantiate `u′ := u` and `v′ := v`, so
it needs `Γ;s ⊢ u ⟶≡ u` where `u` is the **body, with `x` free and `Γ` not binding it**. That is
not merely an instance of reflexivity; it is an instance of reflexivity *at a term the context
does not scope*, which is exactly the false case. When the body places `x` in operand position —
`u = y x` — the `Me-App` node inside needs `Γ; x::s` prevalid, and `Pv-Sta` refuses.

**Second**, it invokes Proposition 18, which is false as printed. This is the weaker of the two
observations and is recorded only for completeness: the repaired Proposition 18 — reflexivity with
the scoping premise, proved here as `⟶ᵉ-refl` — does not rescue the step either, because its
hypothesis `fv u ⊆ dom Γ` fails at exactly the body `Me-Bet` hands it.

So the two propositions share a root cause and not a repair. Proposition 18's repair is to the
*statement*: add the scoping hypothesis and it becomes true. Proposition 17's repair is to the
*system*: `Me-Bet` must bind the parameter in its body premise, as `Me-Fun` and `Me-FOp` do. No
correction to 18 makes 17 true, because 17 is false outright.

Neither refutation is derived from the other. Both are counterexamples — exhaustive case analyses
showing that *no* derivation exists — and `MPSS/BetaScope` and `MPSS/BetaScopeWf` import nothing
about reflexivity, or about Proposition 18, at all. A proof that a derivation does not exist
cannot be parasitic on another statement being false.

Nor is either postulated. Postulating a refuted statement would make the assumption set
inconsistent with the system and let anything be derived from it, including the very propositions
under audit; `MPSS/Assumed` therefore carries `Prop-17ʳ`, the repaired form, and carries no
entry for Proposition 18 at all, its repair being proved rather than assumed.

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

## Equivalence reduction does not preserve well-formedness

`MPSS/EqvWf`. **Not a paper claim** — the paper never states it, and its Lemma 7 technique avoids
needing it. There is therefore no reasoning to diagnose and nothing to assume. It is recorded here
because it is a fact about MPSS worth knowing, and because it rules out the naive route to
Lemma 23.

`Γ₀ = x ≡ (Top Top)` is a legal context: prevalidity asks an annotation only to be locally closed
and scoped, never well-formed. `Wf-PrE` then calls `x` well-formed on the strength of the
annotation existing, `Me-Pro` unfolds it, and `Top Top` is not well-formed, since `Wf-App` would
place `Top` below an abstraction. So well-formedness is not stable under the reduction its own
subtyping relation is built from, and the cause is that contexts carry a scoping condition where
they would need a typing one.

Conditional on Lemmas 1 and 2, through Theorem 11.

---

## Negative results that are not refutations of the paper

Three further machine-checked negations sit in their own modules. None contradicts anything the
paper asserts, so none carries a diagnosis of a proof or an assumed repair; they are recorded here
so that the audit's coverage is complete.

**Promotion is not stack-monotone** (`MPSS/Diff`, `push-is-false`). Equivalence reduction is —
that is `pushᵉ` in `MPSS/StackPush`, and `MPSS/CoNarrow` uses it. Promotion is not, and the reason
is structural rather than incidental: pushing onto a non-empty stack turns `Ms-Fun` into `Ms-FOp`,
which binds the parameter with an *equivalence* annotation instead of a subtype one, and `Ms-Pro`
reads subtype annotations. A body that promotes its own parameter therefore has no counterpart.
This is why `MPSS/CoPromote` builds a covariant promotion at an arbitrary stack from the start
rather than building it at `nil` and pushing.

**Recording a typing obligation on the stack does not suffice** (`MPSS/StackObligation`). This
tests a *repair* of my own devising, not the paper: `Pv-Sta` demands only scoping of a stack
entry, so one might add the obligation that it lies below the annotation it will meet. Replaying a
body derivation under `x ≡ α` given `α ≤ t` fails in one step and succeeds in many, and that gap
is the answer — the obligation alone is not enough.

**The `Reach` obligation is false at arbitrary stacks** (`MPSS/ReachFails`). `Reach` is mine, not
the paper's: `MPSS/Push` reduces Conjecture 8's structural content to it. The refutation shows the
reduction is too strong as stated. It leaves the restricted form standing — the witness's applied
term is not well-formed — and so establishes that well-formedness is load-bearing in the
obligation rather than a convenience.

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

## Lemma 24: the well-formedness conclusion, whose printed proof does not establish it

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

### A further measure candidate, and why the generality is forced

The most promising measure not covered above unrolls the stack into the binders, so that the two
rules in tension are reconciled by construction:

> `D Γ s (app a b) = max (D Γ (b::s) a) (1 + D Γ [] b)`
> `D Γ (α::s) (λw.b) = max (D Γ [] w) (D (Γ, z ≡ α) s (b ^ z))`
> `D Γ [] (λw.b) = max (D Γ [] w) (D (Γ, z ≤ w) [] (b ^ z))`
> `D Γ s x = 1 + D Γ s α` for `x ≡ α ∈ Γ`, and `0` for a subtype-annotated or unbound `x`

Giving a subtype-annotated variable weight zero is sound and is what makes this candidate go
further than the others: `Me-Pro` reads *equivalence* annotations only, so a variable bound by
`Me-Fun` can never be promoted, and only `Me-FOp` — which binds the parameter to the stack head —
introduces a variable that can. `Me-App` is then non-increasing because `(a b) · s = a · (b::s)`,
`Me-FOp` because the stack head's weight is already charged to the binder it becomes, and
`Me-Pro` strictly decreasing by construction.

It fails at the definition rather than at a case. `D Γ s x = 1 + D Γ s α` recurses on the
annotation at the *same stack*, and while an annotation's free variables are scoped strictly
earlier in the context, the stack's are not, so no lexicographic combination of context position
with term and stack size is decreasing. Bounding the variable's weight instead — computing it once
at the empty stack — breaks `Me-Pro`, since a variable's weight must then dominate its
annotation's weight *at whatever stack is current*, and the stack is unbounded relative to the
context.

That is the obstruction in its sharpest form, and it is the same one throughout: `Me-Pro` and
`Me-FOp` pull in opposite directions on how a stack entry and the variable it becomes should be
weighed.

### The generality of Lemma 2's statement is forced

Lemma 2 concludes at arbitrary `Γ₁;s₁` and `Γ₂;s₂` with `Γ₀;s₀ ↣ Γᵢ;sᵢ`, which invites the
question of whether a fixed-context version would do — it would make the `Me-Pro`/`Me-Var` case
trivial, since `t₃ = α₁` works there with reflexivity and no induction hypothesis at all.

It would not. `Me-App` takes its operator premise at the *pushed* stack `v::s`, and joining two
`Me-App` steps requires the operator's join at `v₁::s`, where `v₁` is the reduced operand. The
induction hypothesis supplies it at `v::s`. Only a formulation that lets the stack reduce —
which is exactly what `Ct-Stk` provides — closes that gap. So the extra generality is not
incidental, and `Theorem 3`, which uses the lemma only at `Ct-Refl`, still cannot be proved from
a fixed-context version.

### Where the β-rule defect shows up again

The `Me-App`/`Me-Bet` case of the diamond has to join the abstraction body's two reducts. `Me-FOp`
takes that premise at `Γ, x ≡ v; s`; `Me-Bet` takes it at `Γ; s`, with the parameter unbound. The
two are in different contexts, so the induction hypothesis does not apply to them as they stand.
Under the repair — binding the parameter in `Me-Bet`'s body premise — both sit in the same
extended context and the case goes through. That is independent evidence for the repair that
`MPSS/Assumed` justifies on other grounds.

### The measure, made precise — and refuted at one rule

`MPSS/Height` carries the candidate out. It defines the unfolding height, machine-checks that
`Me-Pro` strictly decreases it, machine-checks that three of the four structural rules leave it
alone, and then **refutes the fourth by counterexample**. So the obstruction is no longer
something noticed while searching; it is a theorem.

The measure. `hvar Γ x` is `0` for a subtype-annotated or unbound variable and `1 + htm Γ' α` for
`x ≐ α`, read at the context `Γ'` that scopes `α`; `htm` takes the maximum over a term's free
variables. It is well defined because prevalidity scopes an annotation strictly earlier, so the
recursion descends a finite chain. Giving a subtype annotation weight zero is what makes going
under `Me-Fun` free — `Me-Pro` reads equivalence annotations only, so a variable it binds can never
be unfolded.

| | |
| --- | --- |
| `ht-unfold` | `suc (htm Γ α) ≤ hvar Γ x` — `Me-Pro` strictly decreases it |
| `ht-fun` | `Me-Fun` does not increase it |
| `ht-fop` | `Me-FOp` does not increase it |
| `ht-bet` | `Me-Bet` does not increase it |
| `ht-app-false` | **`Me-App` increases it** |

The counterexample is the smallest configuration there is: at the empty context and empty stack,
`M [] (⊤ :: nil) ⊤` is `1` and `M [] nil (⊤ ⊤)` is `0`.

The two demands are exactly opposed, and each is forced. `Me-FOp` binds a stack entry to a
variable worth one more than the entry, so a stack entry must carry that `suc` — without it the
body outgrows the abstraction it came from. `Me-App` moves an operand onto the stack unchanged, so
that same `suc` appears from nowhere. Charging the operand in the term instead does not help:
`htm (app a b) = htm a ⊔ suc (htm b)` makes the charge compound with nesting depth, and the opening
lemma then fails in its own application case — which is how the version above was arrived at.

This refutes measures of this shape, not all measures. What it rules out is any assignment that
weighs a stack entry uniformly, one more than the variable it becomes; the diamond may still hold,
and may still be provable by an argument that is not a size measure at all — a complete-development
translation in Takahashi's style needs none.

### Takahashi's method relocates the obstruction, it does not remove it

The complete development is the standard remedy when a parallel-reduction diamond stops closing by
direct case analysis, and it is the natural thing to reach for here — the paper is already in that
tradition, calling `⟶≡` a "simultaneous" reduction and citing Hutchins for it, though it never uses
the vocabulary and does the diamond by pairwise cases instead.

It also fits the paper's statement exactly. With the triangle in the form

> `Γ;s ⊢ t ⟶≡ u  →  Γ;s ↣ Γ';s'  →  Γ';s' ⊢ u ⟶≡ t*`

two instantiations give Lemma 2 with `t₃ := t*`, and the reduced configuration is not a
complication but the thing the `Me-App` case needs — joining there wants the operator's target at
the *reduced* operand's stack, which is what `Ct-Stk` supplies.

What it costs is that `t*` must exist. `MPSS/Develop` writes the development out, one clause per
rule, and Agda rejects it, naming two calls. One is the locally nameless tax: `b ^ z` is the same
size as `b`, a subterm of `lam w b`, so any size-based recursion sees through it where the
structural checker cannot. **The other is `star Γ (b :: s) a` — `Me-App` pushing the operand.** It
is forced: every step out of `app a b` is `Me-App` with its operator premise at `b :: s`, so the
development has to be computed there.

That is the same push `ht-app-false` refutes. So the obstruction moves from the diamond's induction
to the existence of `t*` and keeps its shape: `Me-FOp` binds a stack entry to a variable worth one
more than the entry, so a stack entry must carry that charge; `Me-App` puts an operand on the stack
without it. Whichever way it is charged, one of the two is unpaid.

**Where this leaves Lemma 2.** Neither proved nor refuted, and now four approaches deep: the
paper's own induction, three families of measure, the height of `MPSS/Height` with its
counterexample, and the complete development. Each fails at the same pair of rules. That is
evidence about the shape a proof must have, not evidence that the diamond is false — no
counterexample has been found, and its counterpart in v1 is proved, differing exactly by the
context and stack that create this tension.

### The obstruction, from both sides

`MPSS/Height` now states what a measure has to do — `Measure`, three constraints — and gives two
candidates that each satisfy part of it, with the gap closed by counterexample rather than left as
a failed attempt.

| | `dec-pro` | `mono-app` | `mono-fop` |
| --- | --- | --- | --- |
| `M`, charging the stack | `ht-unfold` | **`ht-app-false`** | `ht-fop` |
| `M₂`, charging the operand | same argument | `ht₂-app`, an *equality* | **`ht₂-fop-false`** |

Charging the operand buys `Me-App` outright — moving an operand to the stack becomes the same `⊔`
reassociated, so the measure is not merely non-increasing but unchanged. It loses `Me-FOp`, because
the charge then compounds with nesting: with body `⊤ x`, bound `⊤` and `⊤` on the stack, the opened
body costs 2 while the abstraction and the stack entry cost 1 each. Raising the stack charge only
moves the failure to a body one application deeper, and the abstraction cannot absorb it — the
depth is a property of the body, the charge is on the stack.

`dec-pro` is not incidental, and it is worth saying why the diamond needs it at all. At the
`Me-Var`/`Me-Pro` case the join has to be built from a derivation the *context reduction* supplies,
which is a subderivation of neither input; no induction on derivation size reaches it, and only a
measure that `Me-Pro` strictly decreases does. That is the precise sense in which the printed proof
has no induction principle.

**What is not established.** That no measure exists. The three constraints close no cycle: every
use of `mono-fop` extends the context, so chaining them builds an ever-larger context rather than
returning to a configuration already seen, and nothing contradictory follows. A measure reading the
context's own unfolding depth — which neither candidate does — is not ruled out.

**Position on Lemma 2.** Neither proved nor refuted, and no counterexample found; its v1 counterpart
is proved, differing exactly by the stack and context that create this tension. Five approaches have
failed at the same pair of rules, and the failure is now characterised rather than merely repeated.

### Erasing the configuration instead of measuring it

The one approach left that never weighs a stack entry against a variable: don't measure the
configuration, erase it. `MPSS/Unfold` translates `Γ;s ⊢ t` to a plain term by substituting away
every equivalence annotation, so that the diamond could be inherited from v1's `⟶≡`, which has no
context and no stack and whose diamond `PSS/Diamond` proves.

`U` is **definable outright**, by plain structural recursion on the context — each step discharges
one entry and substitutes it away, and an entry's annotation is scoped in exactly the tail being
recursed on. It is the only construction in this investigation that needs no measure, no fuel and
no well-founded machinery: the acyclicity that made every height argument delicate is already
carried by the shape of the context. It is a homomorphism for every term former, and it does
simulate the rules that look a variable up — `Me-Pro` becomes an ordinary reduction of the
annotation, `Me-Var` becomes reflexivity, which is the part v1 gets for free.

`sim-false` refutes the simulation, and only `Me-FOp` breaks it. The counterexample is minimal:
with `⊤` on the stack, `λ⊤. x` steps to `λ⊤. ⊤`, because the body unfolds the parameter the rule
has just bound to `⊤`. Under the unfolding both sides stay put, so the simulation would need
`λ⊤. x ⟶≡ λ⊤. ⊤`, and the context-free reduction has no step from a variable to `⊤` — it has no
rule that looks anything up.

**The obstruction, named.** Three changes of clothes have now produced the same fact, and it can
be stated without reference to measures at all: *the equivalence binding `Me-FOp` introduces is not
eliminable by substitution*, because the rule keeps the abstraction whose parameter it has just
defined. Measures fail because that binding must be paid for twice, once on the stack and once in
the term; the complete development fails because the operand push that creates the binding is
forced; and the unfolding fails because substituting the binding away discards the abstraction
that survives it.

This is exactly what v1 lacks. `Srs-FunOp` records `x ≤ α`, which `Me-Pro` cannot cash in, so no
v1 variable ever unfolds and the whole difficulty is absent. That is why v1's diamond proof does
not transfer, and it locates the cost of v2's central design change precisely.

### Searching for a counterexample, exhaustively

`MPSS/diamond-search.py` enumerates every prevalid configuration and locally closed term within
given bounds, computes the full set of one-step `⟶≡` reducts, and checks that every pair of reducts
joins at every pair of `↣`-reduced configurations. All eight `⟶≡` rules and all three `↣` rules are
implemented as printed — including `Me-Bet`'s unbound body premise, so the search is against the
paper's system rather than a repaired one.

| bound | instances | failures |
| --- | --- | --- |
| term ≤ 2, ctx ≤ 1, stack ≤ 1 | 2,020,902 | 0 |
| term ≤ 2, ctx ≤ 1, stack ≤ 2 | 630,378,265 | 0 |

Nothing here is a proof, and the bounds are small. But the shapes the characterisation points at —
`Me-FOp` against `Me-FOp` with the stack head reduced differently on the two sides, and `Me-Bet`
against `Me-App`+`Me-FOp` — are all inside these bounds, and every one of them joins. **The diamond
is very likely true**, and the difficulty is the induction, not the statement.

### The diamond cannot be weakened to confluence

The obvious thing to ask for instead is that the two sides meet after several steps rather than one
— ordinary confluence, the weaker and more usual statement. `MPSS/WeakDiamond` shows it will not do.

What survives is the easy half: `As-Right` absorbs a chain on the right and `As-Left-2` absorbs one
on the left, both by plain induction (`right*`, `left2*`). What fails is `push≡`, the diamond's only
consumer. With chains instead of steps its `As-Left-2` case has to push a chain through the
subtyping derivation, which means iterating `push≡` — and Agda rejects that, naming
`push≡* c (push≡ e d)`, where the chain shrinks but the derivation `d` being descended is replaced
by `push≡ e d`. The rejection is caused by the weakening: the single-step `push≡` in
`MPSS/Transitivity` compiles.

The reason is structural. `push≡` does not preserve the size of the derivation it transforms — at
`As-Refl` it returns `As-Right (As-Refl pv) e`, and at `As-Left-2` it prefixes one node per step of
the joining chain, so the count of left-steps, which the other three cases leave alone, grows by the
chain's length. And Newman's lemma cannot recover the difference: it turns weak confluence into
confluence for a *terminating* relation, and `⟶≡` is reflexive — `Me-Var` and `Me-Top` are steps —
so it terminates nowhere.

So Lemma 2's one-step form is not a convenience of presentation; the metatheory needs it as stated.
That also explains the paper's arrangement: a diamond for a reflexive simultaneous reduction, rather
than confluence for a small-step one, is the standard Tait–Martin-Löf setup, and the strength of the
statement is doing real work downstream.

### The equivalence reduction is not finitely branching

Chasing a `RecursionError` in the counterexample search turned up something better than the search
was looking for. `MPSS/InfiniteBranching` proves it: with `ω = λ⊤. x x` and `Ω = ω ω`, at the empty
context and the empty stack,

> `Ω ⟶≡ Ω`,  `Ω ⟶≡ (λ⊤. Ω) ω`,  `Ω ⟶≡ (λ⊤. (λ⊤. Ω) ω) ω`,  …

all in **one** step. `Ω-branching` gives both halves: `Ω-step`, that every member of the family is a
one-step reduct, and `Ω-inj`, that the family is injective. So a single term has infinitely many
one-step reducts, of unbounded size.

The mechanism is the same three rules that defeated every attempt on Lemma 2, this time caught
doing something visible. `Me-App` pushes the operand; `Me-FOp` pops it and records the fresh
parameter as *equivalent* to it; `Me-Pro` unfolds that parameter back to `ω`, whose body is again a
self-application. Each turn extends the context, so no configuration repeats. The invariant that
survives is `Unfolds`: a parameter is not annotated by `ω` but reaches it in finitely many hops,
because `Me-FOp` binds each parameter to the *previous* one, not to `ω`.

**This settles the complete development.** `MPSS/Develop` recorded that Agda rejects `star` on
termination and that the `Me-App` push causing it is forced — an obstruction. It is now a
refutation: `t*` must be a single term every reduct reduces to, and for `Ω` the reducts are
infinite and unbounded in size. `star` does not merely resist definition; for `Ω` there is no such
object. Takahashi's method is not available here, and that is a fact about the system rather than
about the formalisation.

**It also bounds the search.** Enumerating one-step reducts is not effective in general, so no
exhaustive search can run at bounds admitting self-application — `Ω` has size 11, comfortably
outside every bound reported above, so those results stand, but the method cannot be pushed much
further and its failure mode is non-termination, not a wrong answer. This is why the term-size-3
run stalled: the configurations it wedged on were the ones whose reduct sets were beginning to
blow up.

It does **not** refute Lemma 2. Infinite branching is compatible with the diamond. It removes one
standard route to proving it, and explains the shape of the reduct sets that stopped the search.

### The diamond holds at Ω, and the case analysis says where the difficulty is

`MPSS/InfiniteBranching` identifies `Ω = (λ⊤. x x)(λ⊤. x x)` as the pathological term — the one the
bounded searches could never reach, since it has size 11. Checking the diamond there directly: 68
reducts found, **all 4,624 pairs join**. The diamond survives exactly where a counterexample would
have been most likely.

So the difficulty is the induction, and `MPSS/DiamondCases` pins down what kind. Taking the diamond
as a hypothesis, each case is discharged against explicitly named sub-instances:

| case | closes against |
| --- | --- |
| `case-top`, `case-var-var` | nothing |
| `case-pro-pro`, `case-var-pro` | the annotation, at the same configuration |
| `case-app-app` | the operator at the pushed stack, the operand at the empty stack |

Two things came out of writing it.

**The context reductions are manufactured by the induction, not supplied to it.** In
`case-app-app` the operator's join must live at the stack carrying the *reduced* operand, and the
reduction that gets it there is `Ct-Stk c p`, built from the rule's own operand premise; the
abstraction cases do the same with `Ct-Ann` and the annotation premise. Drop the two context
reductions from Lemma 2's statement and the application case cannot even state its induction
hypothesis. **That is a point in the paper's favour** — the general form is forced, not decorative.

**`Me-Var` against `Me-Pro` is the case with no induction principle, now explicitly.** The joining
derivation is read off the context reduction by `↣-eqv` (added to `MPSS/CtxReduce`, and identical
to `↣-sub` since neither proof inspects the annotation kind), so it is a subderivation of neither
input and nothing in the case bounds it. Every other case recurses on premises of the rules being
analysed; this one does not. That is precisely why a measure is needed and why it must be one
`Me-Pro` strictly decreases — `ht-unfold` is that measure on the subject, and `MPSS/Height` shows
what stops it from extending to the whole configuration.
