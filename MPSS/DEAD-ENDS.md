# Dead ends on Lemma 2, the diamond

Every attempt to prove v2's Lemma 2 — the one-step diamond for `⟶≡` with two reduced
configurations — in one place, each with the file that preserves it, the lemma or counterexample
that kills it, and what it gave way to. Read this before trying anything on the diamond.

The statement, from `MPSS/Assumed`:

> `Lem-2 = ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂} → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₁ → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂`
> `→ Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂ → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ t₁ ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ t₂ ⟶ᵉ t₃))`

**Status.** Neither proved nor refuted. **Its mixed form is proved** (row 35, `MixedDiamond`,
2026-09-12): with either edge's promotion premises at the empty stack, the diamond holds with
original one-step joins on both sides, by a measure on the original side alone. Rows 29 and 32,
the catalogue's previous frontier, are refuted (rows 32–33). No counterexample in 630 million checked joins at small
bounds, none at `Ω`, none in the capped self-application search (row 20). The recursion the
printed proof describes terminates on every input tried, and never revisits a pair of input
positions along a path (row 29). Every failure below is a failure of an *induction*, and every one of them
fails at the same pair of rules: `Me-Pro`, which needs a variable to cost strictly more than its
annotation, and `Me-FOp`, which binds a stack entry to a variable and so needs the entry to cost at
least as much as the variable it becomes. `MPSS/Height`'s `Measure` record states the three
constraints any measure must meet; `MPSS/DiamondCases` states, per case, which sub-instance the
induction has to be justified against.

The longer narratives are in `AUDIT.md` (from "Lemma 2: the induction is not well-founded as
written" onward) and `../PLAN.md` (the sections dated 2026-09-03). This file is the index.

## The table

| # | attempt | preserved as | killed by | superseded by |
| --- | --- | --- | --- | --- |
| 1 | the paper's own induction, on the derivation of `t₀ ⟶≡ t₁` | `DiamondCases` | the `Me-Var`/`Me-Pro` call is on a derivation drawn from the context reduction, a subderivation of nothing | 2 |
| 2 | derivation sizes: sum, multiset, lexicographic either way | `DerivationSize` | `sum-false`, `max-false`, `lex-pro-var-false` | 3, 4 |
| 3 | context position × derivation size, lexicographic | prose, `../PLAN.md` "The measure for Lemma 2" | `(position, size)` fails at binders, `(size, position)` at promotion | 4 |
| 4 | `Φ`, an unfolding weight with the stack carried inside | `Measure` | the opening lemma cannot be stated — `../PLAN.md` "Correcting the measure" | 5 |
| 5 | `Ψ`, the stack taken out of `Φ` and charged with a multiplier `K` | `Multiplier` | `fop-false`, for every `K` | 7 |
| 6 | a positional measure on fixed trees (the "retraction") | prose, `../PLAN.md`, **withdrawn** | the walk returns to a subtree it is inside — the trace in `Unroll` | 9 |
| 7 | `M`, the unfolding height, stack entries charged one more | `Height` | `ht-app-false` | 8 |
| 8 | `M₂`, the same with the operand charged instead | `Height` | `ht₂-fop-false` | 9 |
| 9 | `D`, the stack unrolled into the binders | `Unroll` | `D-Ω`: the recursion diverges at `Ω` | 10 |
| 10 | `D′`, the same with annotations charged at the empty stack | `Unroll` | `D′-dec-pro-false` | — |
| 11 | lexicographic (configuration depth, term depth, derivation size) | `LexDepth` | `lex-fop-false` | — |
| 12 | Takahashi's complete development `t*` | `Develop`, `InfiniteBranching` | `star` rejected on the forced `Me-App` push; `Ω-branching`: `t*` does not exist at `Ω` | — |
| 13 | erase the configuration by substituting annotations away, inherit v1's diamond | `Unfold` | `sim-false` at `Me-FOp` | — |
| 14 | weaken the statement to confluence | `WeakDiamond` | `push≡*` rejected; Newman's lemma needs termination and `⟶≡` is reflexive | — |
| 15 | weaken the statement to a fixed configuration | `DiamondCases` (`case-app-app`), `../PLAN.md` "Why the diamond cannot be stated at a fixed context" | `Me-App` needs the operator's join at the *reduced* operand's stack, which only `Ct-Stk` supplies | — |
| 16 | search for a counterexample | `diamond-search.py` | none found; the search cannot reach self-application because `⟶≡` is not finitely branching | 20 |
| 17 | the paper's second conjunct, "no promotion of `x` on one edge ⇒ none on the other side's join" | `Moreover` | `moreover-false`: the context reduction forces the promotion | the clause with the context reduction's pieces also constrained |
| 18 | any measure on configurations meeting `Height`'s `Measure` | `NoMeasure` | `no-measure`: the walk from `Ω` cycles through the three transitions with the strict one every round | a measure on the derivations |
| 19 | `Me-Pro` nodes weighted by (`hvar`, annotation size), multiset order | prose, `../PLAN.md` "The diamond, resumed" | internal parameters `z₂ ≡ z z` outweigh the variable whose piece binds them | — |
| 20 | search with a cap on `Me-Pro` nesting, reaching self-application | `diamond-search-capped.py` | none found: 29 family configurations at edge caps 1 and 2, joins sought up to cap 5, zero unjoined pairs (a random pass was stopped as uninformative) | — |
| 21 | run the recursion itself on explicit derivation trees | `diamond-recursion.py` | not a dead end: terminates on every input tried (family caps 1 and 2, random), in at most 65 calls | — |
| 22 | the printed invariant ("no promotion of `x`") as the thing to carry through the induction | `Moreover`, `Strengthen` | false, and insufficient — the strengthening also needs `x` off every stack and binder annotation | the derivation at `Γ₁ ∖ B`, `DiamondStep` |
| 23 | `Me-Pro` nodes weighted by (root original variable, size of the unfolding), multiset order, then size | `measure-probe.py` | survives 9.6 million calls, then fails at a stack entry `(λ⊤.(λ⊤.0)(0 0)) x` whose piece binds a parameter to `x x`: the copied piece's internal promotions outweigh the promotion consumed | — |
| 24 | any weight on `Me-Pro` nodes that is a function of the variable and the context | prose, `../PLAN.md` "What the copies need" | the piece copied at a pull has promotions on parameters it binds itself, whose pieces are subtrees of the *other* side's current derivation — no static weight sees that | a measure on the pair, or the trigger-forest argument |
| 25 | pair-aware weights: a promotion weighted by the size or promotion count of the piece the other side would copy for it, by binding position, and their combinations | `measure-probe.py` | all fail, at pulls and at structural steps; worse than the static weights | — |
| 26 | an ordinal potential ranking each promotion by the piece it pulls paired with the partner's subtree | prose, `../PLAN.md` "What the copies need" | circular: computing the rank walks the pair exactly as the recursion does, so the potential is well-defined only if the recursion terminates | the trigger-forest argument, as a bound on chains rather than a state potential |
| 27 | history-aware orders on the pair: each side carries the binding position of the variable whose pull created its material (its anchor) and the size of that material; lexicographic and multiset orders on (anchor, size), with promotion counts and sums as tie-breakers | `anchor-probe.py`, logs `.search-logs/anchor_k*_*.log` | two survive every call on the family configurations with context pieces capped at promotion depth 1 (7.6 million non-leaf calls), then fail at depth 2 on `y ≡ λ⊤.(0 0), v ≡ y ((⊤ ⊤)(⊤ ⊤))`, subject `v`: after both sides have pulled (anchors 0 and 1), a promotion of the parameter the pushed piece binds to the stack entry makes the puller fetch the operand premise it pushed before its own pull — anchored above both, and larger than what either side holds. The scenario predicted in `../PLAN.md` "Anchors" is realised; leaf calls (no induction hypothesis needed) are excluded from the count | the trigger-forest bound, or a decomposition of the diamond that never pulls a stack piece |
| 28 | a lexicographic order on pairs of *input positions*, built from tree rank, depth, subtree size and promotion count of the two materials (18,279 keys of up to three components) | `order-search.py` | none survives one configuration at promotion depth 2 | the order on position pairs exists (row 29) but is not a function of these features |
| 29 | the recursion revisiting a pair of input positions along a path | `position-probe.py`, `frame-probe.py`, `revisit-probe.py`, logs `.search-logs/pos_*.log` | **not a dead end**: in 264,000 runs at promotion depths 1–4 no pair of positions recurs along a path, and the union call graph of all runs of a configuration is acyclic. A well-founded order on pairs of positions exists for fixed inputs; a uniform definition of it, or a direct proof that no pair recurs, is the open item | the frames argument, `../PLAN.md` "What the positions say" |
| 30 | the frames argument: frames (copies of input trees), segments (entry at root or at a premise, descent to a leaf), the segments lemma, the reduction of an infinite path to an ascending chain of parameters pulled infinitely often on one side | prose, `../PLAN.md` "The frames argument, attempted"; `frame-probe.py`, `trigger-probe.py`, `jointlex-probe.py`, `pullseq-probe.py` | not refuted, not closed: everything up to the chain is provable; refuting the chain — a binder position visited infinitely often, each visit binding a fresh parameter to the stack top of the moment — is the open step. Pre-order within a frame is *not* the traversal order (returns to a premise pushed later than the one left from), so the creation-ordered frame list is not a potential | the descent lemma, row 31 |
| 31 | pulls between two binder steps descend in binding order | `runs-probe.py`, `../PLAN.md` "A lemma that holds" | **not a dead end**: holds on 56,000 within-run pull pairs, and follows from prevalidity (annotations mention only earlier bindings). So runs are bounded by the context length and an infinite path needs infinitely many binder steps; the circle to break is binder steps ← λ nodes of copies ← pulls ← the partner's promotion nodes ← the partner's copies | the order on binder steps by whether the popped stack entry predates the copy |
| 32 | an input promotion node consumed by two pulls along one path | `distinct-probe.py`, `../PLAN.md` "Two more structural facts" | **refuted 2026-09-12** (`frame-visit-probe.py`, `cycle-sweep.py`, `cycle-summary-2026-09-12.md`): at `Γ = u ≡ λ⊤.(w 0), w ≡ λ⊤.0`, subject `u u`, with `d₁` of promotion depth 3 (`u → z → u` in the operand of the body) and a context piece for `u` whose body promotes `w` and, inside, the parameter bound to the stack, that promotion node is consumed twice on one path: the second consumption follows a re-pull of the piece for `u`, which follows the other side promoting `u` at a deeper node. 4 violations in 533,894 runs of the sweep. Row 29's no-repeat property fails on the same configuration (pairs of origin positions recur, at deeper contexts) | the *asymmetric* statement, row 35 |
| 33 | per-frame single visit: within one copy of an input tree (a frame, created by a pull of an original piece and re-entered by fetching a stored premise), no position is visited twice on a path — which would bound the recursion by a finite tree of frames | `frame-visit-probe.py`, `cycle-sweep.py` | **refuted**: at `Ω`-shaped inputs `(λ⊤.(0 0)) (λ⊤.(0 0))` with one side of promotion depth 3 (`z → z′ → z`), the same stored premise (the root's operand) is fetched twice on one path — the parameter bound to it is promoted, unfolds to a stack entry that is a parameter bound later, and returns to the subject. 126 violations in the sweep | row 35 |
| 34 | exact-state cycle detection on the recursion: hashing the full state (both derivations, both context reductions, contexts and stacks) up to renaming along every path | `cycle-sweep.py`, `cycle-summarize.py`, `cycle-summary-2026-09-12.md` | **not a dead end**: no exact state repeats in 533,894 runs, 11.3 million calls, a million pulls, no budget hit. The recursion terminates on every input tried; as with row 21, this is evidence for the diamond, not a proof | — |
| 35 | **the mixed diamond** — measure the original side alone, by the size of its derivation plus the sizes of the live pieces of its context reduction, when the *other* edge is a variant step | `MixedDiamond`, `MixedMeasure`, `Sized`, `Uniform`, `Strip`; probe `mixed-measure-probe.py` | **not a dead end — proved.** `Lem-2ᵐ`: an original step against a variant step, at two reduced configurations, is joined by one original step each. The measure decreases at every call: an original promotion consumes a node; a variant promotion against an original variable recurses at the empty stack on the annotation, with its piece as the new original derivation, and the stack pieces and unreachable pieces are discarded. The probe confirmed the decrease on 496,209 calls before the proof was written. Consequences for `⟶ᵉ` alone (`Strip`): the strip property and confluence. What it does not give: `Lem-2` itself, whose second edge promotes at the current stack — the case where the pulled piece is pushed under the stack, which is exactly what the measure cannot pay for (rows 18, 32, 33) | the one-step diamond for two original steps stays open; a reassembly of the strip's chain into one step is what it would take |
| 36 | compression of the strip: peel one original step into variant links, join them one by one against the other original step with the mixed diamond's own join construction, and ask whether the chain of original steps this leaves on the other side is a single original step | `compression-probe.py`, `onestep-check.py`, `compression-2026-09-12.log` | **not a dead end**: 7,943 strips over the families, 4,313 needing compression, every one a single original step — 4,311 by capped enumeration at promotion depth ≤ 2, the remaining two (and all 23 that depth 1 missed on the compounding family) by a goal-directed decision procedure at depth 4. So the residuals of a peeled original step after an original step always reassembled into one step, and the reassembly (row 35's remaining content) is not refuted by the canonical join | a proof of reassembly, i.e. Lemma 2 |

## The entries

### 1. The paper's induction

The appendix proof says "by induction on the derivation tree of `Γ₀;s₀ ⊢ t₀ ⟶≡ t₁`" and, at
`Me-Pro` against `Me-Var`, applies the hypothesis to `α₀ ⟶≡ α₂`, which it has just built from the
context reduction by `Ct-Ann` and weakening. That derivation is a subderivation of neither input.
`MPSS/DiamondCases` writes the case out: `case-var-pro` obtains it by `↣-eqv` and the call `ih` is
on it. Every other case in that module recurses on premises of the rules being analysed; this one
does not. The two edges are also not consistently oriented — in the mirror case it is the other
edge that carries the premise — so no single edge carries the induction.

### 2. Derivation sizes

`MPSS/DerivationSize` defines `size` on `⟶ᵉ` derivations and states four orders as "the recursive
call is smaller than the inputs" in the `Me-Var`/`Me-Pro` case. One instance refutes three of them:
`x ≡ ⊤ ⊤`, the `Me-Pro` premise `⊤ ⊤ ⟶≡ ⊤` (one node), and a context reduction rewriting the
annotation by `⊤ ⊤ ⟶≡ ⊤ ⊤` (three nodes). The inputs measure 2 and 1; the recursive call measures
1 and 3. The fourth order, lexicographic with the `Me-Var` edge first, survives this case and fails
its mirror, which is the same instance with the roles swapped. The extracted derivation can be made
any size; the inputs cannot.

### 3. Context position against derivation size

Promotion moves the promoted variable strictly earlier in the context, because prevalidity scopes
an annotation in the entries before it; the binder rules add an entry the body may promote. So
`(position, size)` fails at binders and `(size, position)` at promotion. This is a measure on the
*call*, not on a configuration, which is why it is recorded in prose only; its two components'
failures are the ones `DerivationSize` and `LexDepth` mechanize.

### 4. `Φ`, with the stack inside

`MPSS/Measure` defines `Φ Γ t w ns`: every free variable charged for its annotation, bound indices
weighed by an assignment that binders shift, the stack carried as a list of weights. Agda accepts
its termination and the module proves the context-extension lemma. It stops there because the
opening lemma cannot be stated: the variable clause charges the annotation at the current stack, so
the weight of an opened name depends on where in the term it sits, and there is no single number to
put in the weight assignment. Charging at the empty stack instead breaks the promotion decrease.

### 5. `Ψ`, the multiplier

Take the stack out of `Φ` and charge it in `Ψ` as `K · Σ Φ α`, with `K` a bound on the number of
occurrences of any bound variable. Then `Me-Pro`, `Me-App`, `Me-Fun` and `Me-Bet` all decrease.
`MPSS/Multiplier` refutes `Me-FOp` for every `K`: with the body `λx. x` — the outer parameter used as
the inner annotation — and a stack entry of weight `6K + 4`, the opened body weighs `6K² + 12K + 7`
against the abstraction's `6K² + 9K + 5`. The parameter's weight feeds the inner binder's weight
assignment and is paid again there. That is `../PLAN.md`'s `bump b ≤ K` obstruction as a
configuration.

### 6. The positional measure

`../PLAN.md` briefly claimed that the recursion terminates because each subject is a position in
one of finitely many fixed trees and a jump from a bound occurrence to its binder's annotation lands
in a disjoint subtree it can never return to. **Withdrawn.** `Me-FOp` binds the parameter to the
stack head, not to the binder's annotation, and the trace in `MPSS/Unroll` shows the walk from `Ω`
re-entering the root of the subtree it is inside after two unfoldings. The argument was never
mechanized; the walk it describes is `D` below, which diverges.

### 7, 8. The unfolding height, both ways of charging

`MPSS/Height`. `M` charges a stack entry one more than its own height, so `Me-FOp` is covered and
`Me-App` invents a level: `ht-app-false`, at `⊤ ⊤` with the empty context. `M₂` charges the operand
where it sits, so `Me-App` is an equality and `Me-FOp` compounds with nesting: `ht₂-fop-false`, at
`λ⊤. ⊤ x` with `⊤` on the stack. The module's `Measure` record is the target any measure must hit.

### 9, 10. Unrolling the stack into the binders

`MPSS/Unroll`. `D` reconciles the two rules by construction — the abstraction case reads the stack
head and binds it, the variable case charges the annotation at the same stack — and its recursion
is infinite: `D-Ω` shows no fuel returns a value at `Ω`, by the same `Unfolds` invariant as
`InfiniteBranching`. `D′` charges the annotation at the empty stack instead, does return a value,
and returns the wrong one: `D′-dec-pro-false`, the variable worth 2 and its annotation worth 3 at
the stack `ω :: nil`.

### 11. Depth, then depth, then size

`MPSS/LexDepth`. Configuration depth is `M`, term depth is `htm`; at `Me-FOp` on `λ⊤. x` with `⊤`
on the stack the first ties at 1 and the second goes from 0 to 1. `lex-fop-false`. The third
component cannot help a pair that has gone up.

### 12. The complete development

`MPSS/Develop` writes `t*` one clause per rule and Agda rejects it, naming `star Γ (b ∷ s) a` — the
operand push, which is forced. `MPSS/InfiniteBranching` then shows the object does not exist:
`Ω-branching` gives an injective family of one-step reducts of `Ω`, so there is no single `t*`
every reduct reduces to. Takahashi's method is unavailable as a fact about the system.

### 13. Erasure

`MPSS/Unfold`. `U` substitutes every equivalence annotation away, is definable by plain structural
recursion on the context, and is a homomorphism. `sim-false`: with `⊤` on the stack, `λ⊤. x` steps
to `λ⊤. ⊤`, both erase to themselves, and v1's context-free `⟶≡` has no step between them. The
binding `Me-FOp` introduces is not eliminable by substitution, because the rule keeps the
abstraction whose parameter it has just defined.

### 14. Confluence instead of the diamond

`MPSS/WeakDiamond`. The easy halves go through (`right*`, `left2*`). The consumer `push≡` does not:
its `As-Left-2` case has to iterate itself along a chain, Agda rejects `push≡* c (push≡ e d)`, and
the rejection is caused by the weakening — the single-step version compiles. Newman's lemma does
not apply because `⟶≡` is reflexive and terminates nowhere.

### 15. A fixed configuration

Joining two `Me-App` steps needs the operator's join at `v₁ :: s` with `v₁` the *reduced* operand;
the induction hypothesis supplies it at `v :: s`. `case-app-app` in `MPSS/DiamondCases` builds the
gap as `Ct-Stk c p` from the rule's own operand premise. Without the two context reductions in the
statement, the application case cannot state its own hypothesis. The paper's general form is
forced.

### 16. Search

`diamond-search.py` enumerates prevalid configurations and locally closed terms within bounds,
computes all one-step reducts, and checks every pair joins at every pair of reduced configurations.

| bound | instances | failures |
| --- | --- | --- |
| term ≤ 2, ctx ≤ 1, stack ≤ 1 | 2,020,902 | 0 |
| term ≤ 2, ctx ≤ 1, stack ≤ 2 | 630,378,265 | 0 |
| `Ω` directly | 68 reducts, 4,624 pairs | 0 |

The search cannot be pushed to bounds admitting self-application, because enumerating one-step
reducts is not effective there (`InfiniteBranching`).

## What survives

- The obstruction, characterised: `Me-FOp` binds a stack entry to a variable that `Me-Pro` will
  unfold, and the entry has to be paid for twice — once on the stack, once in the term. Every
  compositional measure pays it once. `Height`'s `Measure` record is the exact target.
- The case analysis: `DiamondCases`. The only case with no induction principle is `Me-Var` against
  `Me-Pro`; a measure that `Me-Pro` strictly decreases is the missing ingredient, and `ht-unfold`
  is that measure on the subject alone.
- The general form of the statement is forced (15), and the one-step form is forced (14).
- Ruled out since (row 18): *any* measure on configurations — `NoMeasure`. The walk from `Ω`
  closes the cycle that the earlier remark said nothing did: `mono-fop` extends the context, and
  the round repeats one binding deeper with `dec-pro` strict every time.
- Not ruled out: an induction on the derivations together with the context reductions, in which
  the copied piece at `Me-Var`/`Me-Pro` is paid for by the other side's descent. Row 19 is the
  first attempt at one; row 21 is the evidence that such an induction exists.
- The case analysis is complete: `DiamondStep` joins every pair of rules against the diamond as a
  hypothesis, with the invariant that actually survives the recursion (row 22). The induction
  principle is now the only open item.
- The second conjunct of the lemma is false as printed (row 17); the diamond itself is unaffected
  by that instance, but the `Me-App`/`Me-Bet` case of the printed proof needs the corrected clause.
