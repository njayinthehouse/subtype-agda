# Dead ends on Lemma 2, the diamond

Every attempt to prove v2's Lemma 2 — the one-step diamond for `⟶≡` with two reduced
configurations — in one place, each with the file that preserves it, the lemma or counterexample
that kills it, and what it gave way to. Read this before trying anything on the diamond.

The statement, from `MPSS/Assumed`:

> `Lem-2 = ∀ {Γ₀ s₀ Γ₁ s₁ Γ₂ s₂ t₀ t₁ t₂} → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₁ → Γ₀ ∣ s₀ ⊢ t₀ ⟶ᵉ t₂`
> `→ Γ₀ ∣ s₀ ↣ Γ₁ ∣ s₁ → Γ₀ ∣ s₀ ↣ Γ₂ ∣ s₂ → ∃[ t₃ ] ((Γ₁ ∣ s₁ ⊢ t₁ ⟶ᵉ t₃) × (Γ₂ ∣ s₂ ⊢ t₂ ⟶ᵉ t₃))`

**Status.** Neither proved nor refuted. No counterexample in 630 million checked joins at small
bounds, none at `Ω`. Every failure below is a failure of an *induction*, and every one of them
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
| 20 | search with a cap on `Me-Pro` nesting, reaching self-application | `diamond-search-capped.py` | none found at cap 1 (29 configurations); further passes running | — |
| 21 | run the recursion itself on explicit derivation trees | `diamond-recursion.py` | not a dead end: terminates on every input tried (family caps 1 and 2, random), in at most 65 calls | — |
| 22 | the printed invariant ("no promotion of `x`") as the thing to carry through the induction | `Moreover`, `Strengthen` | false, and insufficient — the strengthening also needs `x` off every stack and binder annotation | the derivation at `Γ₁ ∖ B`, `DiamondStep` |
| 23 | `Me-Pro` nodes weighted by (root original variable, size of the unfolding), multiset order, then size | `measure-probe.py` | survives 9.6 million calls, then fails at a stack entry `(λ⊤.(λ⊤.0)(0 0)) x` whose piece binds a parameter to `x x`: the copied piece's internal promotions outweigh the promotion consumed | — |
| 24 | any weight on `Me-Pro` nodes that is a function of the variable and the context | prose, `../PLAN.md` "What the copies need" | the piece copied at a pull has promotions on parameters it binds itself, whose pieces are subtrees of the *other* side's current derivation — no static weight sees that | a measure on the pair, or the trigger-forest argument |

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
