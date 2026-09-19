# MPSS: obligation status

Every entry below is machine-checked under `--safe`, with no postulates, no holes, and no
`TERMINATING` pragmas. Assumptions appear only as declared statement types in `MPSS/Assumed`,
taken as explicit arguments, so each result carries its dependencies in its own type.

## Proved

| # | statement | module | needs |
| --- | --- | --- | --- |
| 3 | transitivity elimination | `Transitivity` | 1, 2 |
| 4 | progress | `Progress` | 1, 2 |
| 5 | preservation | `Preservation17` (`Thm-5ʷ`); earlier `Preservation`, from the refuted 17ʳ | Conj 8 |
| 6 | evaluation preserves well-formedness | `Preservation17` (`Lem-6ʷ`); earlier `Evaluation`, from the refuted 17ʳ | Conj 8 |
| 7 | substitution preserves well-formedness | `Lemma7` | Conj 8 |
| 9 | promotion under substitution, statically | `Lemma9` | Conj 8 |
| 10 | inversion | `Inversion` | 1, 2 |
| 11 | no supertype of `Top` | `TopLemma` | — (single-step); 3 (as printed) |
| 12 | well-formedness extraction | `Static` | — |
| 13 | from well-subtyping to subtyping | `Static`, `Inversion` | — |
| 14 | from well-equivalence to equivalence | `Static` | — |
| 15, 16 | symmetry, and equivalence to subtyping | `Static` | — |
| 18ʳ | reflexivity, with the scoping premise | `StackPush` | — |
| 19–22 | weakening | `Weakening` | — |
| 24 | narrowing a promotion (first two conclusions) | `Narrowing24` | — |
| 23 | narrowing preserves well-formedness | `Lemma23` | — |
| 24 | third conclusion | `CoNarrow`, `CoPromote` | — |
| 25 | narrowing in equivalence reduction | `Narrowing` | — |
| 26 | narrowing prevalidity | `Narrowing` | — |
| 17ʷ | **repaired**: on well-formed terms an evaluation step is a chain of equivalence steps through well-formed terms | `Prop17Chain` | — |
| 27 | reduction preserves subtyping | `Preservation17` (`Prop-27ʷ`); earlier `Preservation`, from the refuted 17ʳ | — |
| — | renaming for the three well-formedness judgements | `WfRename` | — |
| — | abstraction congruence of `≤*wf` from a cofinite family (`FunCongr`) | `CoFun` | — |
| — | Conjecture 8 from `StepLift`, one promotion lifted under one application (`conj8`) | `Conj8Reduction` | `StepLift` |
| — | Conjecture 8 from the two binding rules (`conj8-from-lifts`) | `Conj8Push` | `FunLift`, `FOpLift` |
| 28 | substitution preserves prevalidity | `Subst28` | — |
| 29, 30 | promotion under substitution | `Lemma2930` | — |
| 31, 32 | reduction under substitution | `Subst`, `Open` | — |
| 33, 34, 35 | congruence | `Congruence` | — |
| 36 | commutativity — context weakening | `Narrowing` | — |
| 32 | reduction under substitution, in the printed `≡`-bound form | `SubstEqv` | — |
| — | `↣-Prevalid`: a reduced extended context is prevalid (the hypothesis of `Commutation`) | `CtxPrevalid` | — |
| 2, every case | the diamond's case analysis, complete, against the induction hypothesis, under the corrected invariant | `DiamondStep` | Lemma 2 itself, as `ih` |
| 2, for the variant | the one-step diamond for `⟶ᵉ′`, on locally closed subjects, with two arbitrary context reductions | `VariantDiamond` | — |
| 2, mixed | **the mixed diamond**: an original step against a variant step, at two reduced configurations, joined by one *original* step each (`Lem-2ᵐ`) | `MixedDiamond` (measure: `MixedMeasure`; sizes: `Sized`, `Uniform`) | — |
| 2, strip | the strip property of `⟶ᵉ`: two one-step reducts are joined by one original step from one and a chain from the other; confluence of `⟶ᵉ*` at a fixed configuration | `Strip` | — |

## Refuted

| # | statement | module |
| --- | --- | --- |
| 17 | `u ↦ v` implies `Γ;s ⊢ u ⟶≡ v` | `BetaScope`, `BetaScopeWf` |
| 17ʳ | the repaired statement `Assumed` carried: the same with a scoping premise on the redex | `Prop17Refuted` |
| 18 | reflexivity, as printed | `ReflFails` |
| — | `⟶≡` preserves well-formedness | `EqvWf` |
| — | promotion is stack-monotone | `Diff` |
| — | a stack typing obligation suffices for the `Ms-Fun`/`Ms-FOp` replay | `StackObligation` |
| — | the `Reach` obligation, at arbitrary stacks | `ReachFails` |
| 2, second conjunct | "no promotion of `x` on one edge ⇒ none on the other side's join" | `Moreover` |
| — | the `Me-App`/`Me-Bet` step "no promotion of `x`, so the derivation holds without `x`" | `Strengthen` |
| — | any configuration measure meeting `Height`'s three constraints | `NoMeasure` |
| — | "distinct consumption": no input promotion node triggers two pulls on one path of the diamond's recursion (`DEAD-ENDS` row 32) | `frame-visit-probe.py`, `cycle-sweep.py` (empirical: 4 violations in 533,894 runs) |
| — | "per-frame single visit": within one copy of an input tree no position is visited twice on a path (`DEAD-ENDS` row 33) | `frame-visit-probe.py`, `cycle-sweep.py` (126 violations) |

The first two rows and the row for Lemma 2's second conjunct are claims of the paper's; the
`Strengthen` row is a step of the paper's proof of Lemma 2. The others are facts about MPSS, about
a proposed repair, about this development's own reduction of Conjecture 8, and about the diamond's
induction; `AUDIT.md` says which is which, since only a refuted *paper* claim calls for a diagnosis
and an assumed repair.

**A faithfulness note on Lemmas 31 and 32.** `Subst` proves reduction under substitution for a
name the context does not bind, which is what the β-rule's unbound body premise needs; the printed
Lemma 31 binds the name by `≤` and the printed Lemma 32 by `≡`. The row "31, 32" above records the
unbound form. `SubstEqv` now proves 32 as printed; 31 as printed is not needed by the diamond and
is not proved.

## Assumed

| # | why |
| --- | --- |
| 8 | the paper's own conjecture — the only assumption under type safety (`Preservation17`); reduced in Agda to the two binding rules, `FunLift` and `FOpLift` (`Conj8Push`, 2026-09-13; `CONJ8.md` §7) |

No longer assumed by anything on the path to the paper's theorems: Lemmas 1 and 2 (the variant
route, below) and `Prop-17ʳ`, which `Assumed` still declares for `Evaluation`, `Preservation`
and `Unconditional` — modules kept in place, superseded by `Preservation17` — and which
`Prop17Refuted` shows is uninhabited (2026-09-13).

## Defects recorded in `AUDIT.md`

Refutations of Propositions 17 and 18, with the faithfulness check and the failing step in each
printed proof. Beyond those, six places where a proof does not establish what it claims:

- Lemma 24's third conclusion, whose argument would prove every term well-formed;
- Theorem 5's uncited dependence on Proposition 17;
- Proposition 27 citing `Ws-Lf1` where `Ws-Rgh` is meant;
- Lemma 9 citing a rule `Ws-Lft` that does not exist;
- Lemma 33 swapping which relation each side of `≤` reduces by;
- Lemma 7 citing Lemma 28 for a substituend more general than Lemma 28 covers;
- Lemma 2's induction hypothesis applied to a derivation that is not a subderivation.

One earlier entry, criticising Lemma 23's deferral to Lemma 7, was withdrawn: the technique it
defers to does cover the case.

## What remains

**Lemmas 1 and 2**, and nothing else in the appendix. (Lemma 2 now has its *mixed* form proved, `MixedDiamond`; see below.) For Lemma 2 the case analysis is now
complete (`DiamondStep`): every pair of rules is joined against the diamond taken as a hypothesis,
under the invariant the proof needs in place of the printed second conjunct. What is missing is
the induction principle alone. Every other numbered result the two type
safety theorems depend on is proved above, and Conjecture 8 is the paper's own. They are the paper's main theorem. `AUDIT.md` records why the printed induction
carries no well-founded measure and why four families of candidate measures fail, with the
obstruction isolated: `Me-Pro` needs a variable lookup to cost strictly more than its annotation,
while `Me-FOp` needs a stack entry to cost at least as much as the variable it becomes.
`DEAD-ENDS.md` rows 19–29 record the attempts since then, on the derivations rather than the
configuration: the recursion the proof describes terminates on every input tried and never revisits
a pair of input positions along a path (row 29), so an induction on pairs of positions is possible
in principle; no uniform order on them has been found (rows 23–28). `../PLAN.md`, "What the
positions say", isolates the difficulty to `Me-Pro`'s premise being at the current stack.

The active line (2026-09-08) is the variant `⟶ᵉ′` with that premise at the empty stack.
`EmptyStackPro`, `Peel`, `VariantSub` and `VariantMachine` prove that on locally closed terms the
machine relation `⊲` is the same whether built over the original reductions or the variant, so the
variant's transitivity elimination is Theorem 3.

**The variant's diamond is proved** (`VariantDiamond`, 2026-09-08): `Lem-2′`, unconditional, by
strong induction on `Φ` — the size of the configuration counting only the part of the context
reachable from the free names of the term and the stack (`VariantMeasure`). Every recursive call
of `DiamondStep`'s case analysis, transcribed, is at a strictly smaller `Φ`; the pull is where the
variant pays off, since its premise lands at the empty stack. `NoMeasure` shows no such measure
exists for the original.

What is left on this line is Lemma 1 for the variant — `Commutation` transcribed, with its three
open cases `Bet-App′`, `Fun-Fun′`, `FOp-FOp′` proved rather than assumed — then `Transitivity`
transcribed and the transfer through `VariantMachine`. `../PLAN.md`, "Step 4 done", says how.

## The mixed diamond — 2026-09-12

The recursion the diamond's case analysis describes has an induction principle as soon as **one
of the two edges is a variant step**. `MixedDiamond` proves `Lem-2ᵐ`: for `Γ₀;s₀ ⊢ t₀ ⟶ᵉ′ t₁`
(variant) and `Γ₀;s₀ ⊢ t₀ ⟶ᵉ t₂` (original), with `Γ₀;s₀ ↣′ Γ₁;s₁` and `Γ₀;s₀ ↣ Γ₂;s₂`, there is
`t₃` with `Γ₁;s₁ ⊢ t₁ ⟶ᵉ t₃` and `Γ₂;s₂ ⊢ t₂ ⟶ᵉ t₃` — both **original one-step** reductions. The
measure (`MixedMeasure`) is on the original side alone: the size of its derivation plus the sizes
of the live pieces of its context reduction. A variant promotion against an original variable —
the one case where a symmetric statement pulls a piece and pushes it under the stack — recurses
at the empty stack on the annotation with that piece as the new original derivation, and the
stack pieces and the unreachable pieces are discarded. Derivation sizes are made well defined on
cofinite families by `Sized` (a uniform-size relation, preserved by weakening, reflexivity and
renaming) and `Uniform` (every derivation has a uniformly sized copy). `Strip` draws the
consequences for `⟶ᵉ` alone.

For the original `Lem-2` this narrows the open question to one sentence: the mixed statement is
`Lem-2` with one edge's promotion premises at the empty stack, and everything else is identical.

## Handoff note — 2026-09-11

The active line is unchanged: **finish Step 5 (the variant)** to make `Lem-1`/`Lem-2` leave
`Assumed`. `../PLAN.md`, section "Session 2026-09-11", records the plan in detail: build
`VariantCommutation` (Lemma 1 for the variant, by well-founded recursion on `tsize t₀`; `Bet-App′`
case analysis worked out — case B reduces to the proven `Lem-2′`, case C mirrors `app-bet′`), then
`VariantTransitivity`, then the transfer. That section also records Phase-6 research for the
*original* diamond (decreasing diagrams / Hindley–Rosen; Z-property and complete developments
rejected because `InfiniteBranching` kills them), with the caveat that those give confluence, not
the one-step diamond the downstream proofs consume. Nothing new was mechanized on 2026-09-11.

## Step 5 of the variant line, done — 2026-09-12

`VariantDrop`, `VariantCommutation` (`Lem-1′`, unconditional, by induction on the subject's
size; `Bet-App′`, `Fun-Fun′`, `FOp-FOp′` proved), `VariantTransitivity` (`push≡′`, `⊲′-trans`,
`Thm-3′`), `VariantTransfer` (`Thm-3ᴸ`: transitivity elimination for `⊲` on chains with local
closure recorded, nothing assumed), `Unconditional` (`Thm-3wf` on well-formed chains; Theorem
11, Lemma 10, Theorem 4 with nothing assumed; Lemma 6, Theorem 5 and type safety from exactly
Conjecture 8 and the repaired Proposition 17). **Lemmas 1 and 2 of `Assumed` are no longer on the
path to any of the paper's theorems.** The one-step diamond `Lem-2` for the original relation
remains open as a statement about `⟶ᵉ` (see the mixed diamond above); the paper's metatheory no
longer depends on it.

## Proposition 17 repaired — 2026-09-13

The assumed repair `Prop-17ʳ` was found to be refutable: its instance at the empty stack is the
statement `BetaScope` refutes, so everything proved from it (Lemma 6, Theorem 5, Proposition 27,
type safety in `Unconditional`) was proved from a false hypothesis (`Prop17Refuted`). The repair
that holds is the chain form with well-formedness carried along, **`Prop-17ʷ`** (`Prop17Chain`):
if `u` and `v` are well-formed and `u ↦ v`, then `Γ;nil ⊢ u ⟶ᵉ* v` through well-formed terms.
The β case takes two steps — `Me-App` over `Me-FOp` binds the parameter to the operand and
unfolds it (`unfold`), then `Me-Bet` contracts the closed body — and the intermediate
`(λx≤t. u[x\v]) v` is well-formed because its body is the contractum. The congruence cases lift
the chain: annotations by Lemma 23 step by step, applications by `push≡*wf` and `pushᵉ`, bodies
by closing the chain at one fresh name and renaming, which needed renaming for the
well-formedness judgements (`WfRename`, new). `Preservation17` re-derives Proposition 27, Lemma 6
and Theorem 5 from it, and **type safety from Conjecture 8 alone**. Nothing existing was
modified; the superseded modules stay.

## Conjecture 8, the night of 2026-09-18 — not settled; what it reduces to

Full account in `CONJ8.md` §8–10. In short:

- **The nesting-depth measure of `CONJ8.md` §4 is dead** (`conj8-depth-probe.py`). A round of the
  recursion can raise the depth of the well-formedness derivations (`f = λx≤y. x (y x)`,
  `v = y (y y)` under `y ≡ λ⊤.0`: 3 to 4), because substitution copies the operand under the
  body's applications; Lemma 7 is bounded by the sum of its inputs' depths, not the maximum.
  Chains, the layer walk and Lemma 9 are depth-neutral.
- **The recursion is the machine's, not substitution's** (`conj8-lift-probe.py`). Under an operand
  the body of `λx≤t.u` is reduced under `x ≡ v`; narrowing the body's derivation and replacing a
  promotion of `x` by `x ⟶ᵉ v` and the lifted chain `v ≤*wf t` gives a valid well-subtyping chain
  on all 4.7 million instances tried, and **each round's bound is the domain of the previous
  round's** (31,178 of 31,178 nested rounds) — the order of hereditary substitution. The
  substitution route (Lemmas 7 and 9 with the context induction) does not descend in it.
- **Mechanized** (`--safe`, nothing existing touched): `Conj8Pair` (Lemmas 7 and 9 from the
  conjecture at the one pair `(α, t)`), `FunLift0` (`FunLift` under one operand from the conjecture
  at `(v, t)`), `PushWf` (**`⇛-push`**: the push theorem for well-subtyping chains at a stack,
  side condition a parameter, narrowing at an abstraction that meets an operand, one chain at the
  stack in force at each narrowed leaf), `DomainOrder` (the order, `domain-step`, and `Conj-8ʳ`
  declared, not proved).
- **What is owed for the conditional theorem** (finite domain rank ⇒ Conjecture 8): the rank
  lemmas, and the side condition at the points of a lifted chain, which has to be proved together
  with the lifting, in stack form, by induction on (rank of the bound, size of the wrapper, length
  of the chain). `FunLift`/`FOpLift` as `Conj8Push` states them — over spines at the empty stack —
  are the wrong interface for that: a chain of whole applied terms cannot be taken apart again
  into steps at a stack.
- **What an unconditional answer needs.** A proof needs the domain order well-founded on
  well-formed bounds — a normalization statement about MPSS's type level, which its rules do not
  obviously give. A refutation needs an instance with infinite domain descent, that is a
  well-formed type-level looping combinator, and then an argument that *no* chain exists; nothing
  small can be one (`CONJ8.md` §10).
- **With one recursive function type the conjecture is false** (`CONJ8.md` §11,
  `conj8-rectype-probe.py`): in MPSS + `R ≡ λx≤R.R`, `f δ ≤*wf f′ δ` fails for `f = λx≤R. x δ`,
  `f′ = λx≤R. R δ`, `δ = λx≤R. x x`, with every hypothesis of Conjecture 8 satisfied, and
  `(λx≤R. (x δ) δ) δ ↦ (δ δ) δ` leaves well-formedness. Not MPSS — prevalidity forbids the entry —
  but it ties the conjecture to the absence of bounds of infinite domain rank, which a type-level
  looping combinator (the paper's §6) would supply.
- **Correction, the morning of 2026-09-18 (`CONJ8.md` §13).** The narrowing route is wrong for
  bounds that depend on a parameter an earlier operand instantiates: its intermediate point is
  ill-formed, and `Conj8FromLeaves.Obligation` is false, though the conjecture holds at the
  instance by contracting the redexes first. `PushWf`, `Annotate`, `Conj8FromLeaves` and
  `Wrapper` typecheck and lead nowhere. The route that survives every instance, dependent bounds
  included, is the paper's own — β first, then Lemmas 7 and 9 (`conj8-subst-probe.py`,
  `conj8-dep-gen.py`; `FunLift0`, `Conj8Pair`, `BelowWf`, `RankedWalk`). Its measure is open.

## Conjecture 8 refuted as stated — 2026-09-18

**`MPSS/Conj8Refuted`: `¬ Conj-8`, `¬ Lem-6`, `¬ Lem-7₀`, `¬ Preservation`**, under `--safe`.
Contexts need only be prevalid, so `Γ₀ = R ≡ ω ω` (`ω = λs≤⊤. λx≤(s s). (s s)`) is a legal context
in which `R` is well-formed and `R ≡ λx≤R.R`. With `δ = λx≤R. x x`: `δ ≤*wf λx≤R. R x`, both
plugs under `□ δ` are well-formed, and `δ δ ≤*wf (λx≤R. R x) δ` fails — Theorem 3, confluence, and
the class `Bd` of `MPSS/AppClass` (closed under both reductions, no abstraction in it). And
`(λx≤R. (x δ) δ) δ ↦ (δ δ) δ` leaves well-formedness. `type-safety` in `Preservation17` is proved
from `Conj-8`, a false hypothesis.

**Open:** the same statements once `Pv-Ctx`/`Pv-EqA` ask the annotation to be well-formed.
`CONJ8.md` §8–14 record what a proof there cannot be (depth measure, narrowing, rank induction —
the domain order cycles at the type of the polymorphic identity) and what a counterexample there
needs (a well-formed term behaving as `R`).

## 2026-09-19 — type safety over `WfCtx` from `Conj-8ʷᶜ`; the reducibility argument closes

- `MPSS/WfCtxSafety`: Lemmas 7 and 6 and Theorem 5 over contexts with well-formed annotations,
  from `Conj-8ʷᶜ` alone. Type safety over `WfCtx` now rests on exactly that statement.
- `MPSS/ReducibleMore`, `Morphism`, `GoodAt`, `GoodSubst`, `Fundamental`, `Conj8Ranked`: the
  fundamental lemma of the reducibility argument, and from it `Conj-8ʷᶜ`, `Lem-6ʷᶜ`,
  `Preservationʷᶜ` — under the module parameter that every well-formed term is ranked.
- That parameter is false in full MPSS, and `Ranked` as defined is too strong: `λx≤⊤.x` is not
  ranked, because the order ranges over every operand (`id ▷ id (T T) ▷ T ▷ T T ▷ T`; checked by
  `conj8-id-unranked.py`, not mechanized). `Conj-8ʷᶜ` is still open.
- Owed for a theorem about a calculus: kinded judgements, `Good` by recursion on the kind, the
  six modules carried over (`CONJ8.md` §18). Which stratification is the user's choice.
- Measure search for the substitution route: head-step and size measures all fail
  (`conj8-measure-probe.py`, `CONJ8.md` §19). Next: the route on Hurkens' paradox (`CONJ8.md` §20).

## 2026-09-19, later — Hurkens' paradox is well-formed; candidate counterexample to `Conj-8ʷᶜ`

- `conj8-hurkens-probe.py`: Hurkens' term `[L₀ R₀]` (2039 nodes, transcription checked against
  his printed lengths), encoded as in `CONJ8.md` §20, is found well-formed in the empty context by
  a goal-directed checker, validated against the enumerating oracle on 6,625 small terms.
  `L₀ ≤*wf ¬φ₀`, `(¬φ₀) R₀ wf`, `(¬φ₀) R₀ ⟶ᵉ* ⊥`. The head of `[L₀ R₀]` is a redex after every
  head step (Hurkens, Section 7), so its only supertypes are its own reducts and `⊤`, and the
  instance `u = L₀`, `t = ¬φ₀`, context `□ R₀` of `Conj-8ʷᶜ` fails. **Checked by the probe and
  argued on paper; not mechanized.**
- `MPSS/Conj8NoAbstraction`, `refutes`: the term-independent part, mechanized — `¬ Conj-8ʷᶜ` from
  five hypotheses about `f`, `q`, `A`, `B`, which for Hurkens' term are what the probe checks.
- Lemma 6 and Theorem 5 over `WfCtx` are not refuted by this: the first 13 head reducts of the
  paradox are found well-formed. Still open. `CONJ8.md` §21.
- `MPSS/PromotionNoWhnf`: for a closed term, "no `⟶ᵉ*`-reduct is an abstraction" is preserved by
  promotion (a promotion in a context without `≤` entries is an equivalence step, or goes to `⊤`,
  or its source reduces to an abstraction). `refutes-NR`: `¬ Conj-8ʷᶜ` from the four static
  hypotheses and that one. Left for Hurkens' term: the four static facts and `NR [L₀ R₀]`.
