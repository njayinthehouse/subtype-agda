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
