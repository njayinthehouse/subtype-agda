# Conjecture 8: search, structure, and the measure — 2026-09-12

Conjecture 8 (v2): if `Γ ⊢ u ≤*wf t` and `Co[u]`, `Co[t]` are well-formed in `Γ`, then
`Γ ⊢ Co[u] ≤*wf Co[t]`, for covariant contexts `Co ::= □ | λx≤t.Co | Co t`. It is the paper's
own open problem, and (with the repaired Proposition 17) the only assumption left under type
safety (`MPSS/Unconditional`).

## 1. Search (no counterexample)

`conj8-search.py`: contexts of one or two entries over six annotation shapes, both annotation
kinds; all locally closed terms up to a size bound over the context's names; pairs `u ≤*wf t`
checked **with** the well-formedness side conditions (every promotion between well-formed terms,
both ends of every layer well-formed — an earlier version omitted the left-end condition of
`Ws-Sub`, accepted non-well-formed operators, and produced 5,745 spurious candidates); covariant
contexts `□ v`, `λx≤a.□`, `(□ v) w`, `λx≤a.(□ v)` with both plugs well-formed; conclusion tested
through the machine relation `Co[u] ⟶ˢ* c ⟵ᵉ* Co[t]` with caps on promotion depth, chain length
and term size.

Term size 3: **561,145 instances, 3 failures at chain depth 4, all three joining at depth 6**
(`conj8-deep.py`), e.g. `Γ = y ≤ λ⊤.0, z ≤ y`, `u = λx≤z.x`, `t = λx≤z.y`, `Co = □ (z z)`: the
join is through the body, `x ↦ z z ↦ y z ↦ (λ⊤.0) z ↦ z ↦ y`, five steps. (The generator's term sizes are odd — a compound is one plus two smaller terms — so
the next level is size 5, run separately with single-layer contexts.) So on everything tried the conjecture holds, and the joins it needs are
exactly the "operand reaches the bound" chains the structural analysis below predicts.

Term size 5 (`conj8-size5-2026-09-12.log`, single-layer contexts, `CO2=0`): the run stopped
after **32 of 133 contexts, 11,698,280 instances, 0 failures** (one context, `y ≡ ⊤, z ≡ λ⊤.y`,
skipped on memory). The remaining 101 contexts have not been searched.

## 2. What a `⟶ˢ` step is

A promotion derivation is a path of `Ms-App` (pushing operands), `Ms-Fun` (entering a body
under `x ≤ t`) and `Ms-FOp` (entering a body under `x ≡ α`, `α` popped from the stack), ending
in `Ms-Pro` (one variable to its bound), `Ms-Top` (one subterm to `Top`) or `Ms-Equ` (an
equivalence step). So a `⟶ˢ` step at the empty stack is an equivalence step, or a single
promotion `Co′[y] ⟶ Co′[bound y]` / `Co′[a] ⟶ Co′[Top]` at one covariant position, where the
binders of `Co′` extend the context — by `≤` entries for `Ms-Fun`, and by `≡` entries bound to
operands pushed inside `Co′` for `Ms-FOp`.

## 3. Where the conjecture's content is

`MPSS/Conjecture8Star` reduces the conjecture to `AppCongr₁` (one `≤wf` layer between
well-formed `f`, `f'`, applied to `v`), and the only step that does not lift to the applied
terms is a promotion of the parameter of the *outermost* abstraction: `λx≤w.Co″[x] ⟶ˢ
λx≤w.Co″[w]`. At the stack `[v]` the parameter is bound `x ≡ v`; `x` unfolds to `v`, and what is
needed is `Co″[v] ⊲ Co″[w]` — Conjecture 8 again, for the pair `(v, w)` and the context `Co″`
(with `v` substituted for the other occurrences of `x`). Everything else is congruence,
`pushᵉ`, and bookkeeping. `MPSS/Push` states the residual as `Reach Γ v w` at every stack;
`MPSS/ReachFails` refutes it for arbitrary stacks, with a non-well-formed application.

Three facts fix what the recursive instance has and needs:

- **Its hypothesis `v ≤*wf w` is derivable**: `Co[t] = t v` well-formed gives `t ≤*wf λt₁.Top`
  and `v ≤*wf t₁`; the chain suffix gives `λx≤w.Co″[x] ≤*wf t`; transitivity and inversion
  (Lemma 10, now unconditional) give `w ≡wf t₁`; Lemma 16 turns that into `v ≤*wf w`.
- **Its next application is well-formed**: an application `x v′` inside `Co″` (the only place
  the recursion continues into) is well-formed under `x ≤ w`, so `w ≤*wf λt₂.Top` and
  `v′ ≤*wf t₂` come from the body's well-formedness derivation, which is a premise of the
  `Ws-Lf2` step in the hypothesis chain; with `v ≤*wf w` this gives `v v′` and `w v′`
  well-formed.
- **Its target may move**: the promotion `x ↦ w` need not be matched by `v ⟶ˢ* w` exactly (that
  is what `ReachFails` kills); it is enough that `v ⟶ˢ* c ⟵ᵉ* w` at the relevant stack, with
  the rest of the outer chain carried across `w ⟶ᵉ* c` by strong commutation, which the variant
  now supplies for the closures.

## 4. The measure

Write `D_e` for the well-formedness derivation of the body `Co″[x]` (a `Ws-Lf2` premise inside
the hypothesis `u ≤*wf t`) and `D_v` for the derivation of `v ≤*wf w` (built from `Co[t] wf`).
Round 1 is Conjecture 8 for `(v, w)` at `□ v′`. Its body derivation — the body of the
abstraction `v` promotes to — sits inside a `Ws-Lf2` premise of `D_v`, strictly; its operand
hypothesis `v′ ≤*wf t₂` sits inside `D_e`, strictly. Round 2's pieces sit inside those. So the
recursion descends, at every round, in **both** components of the pair of derivations, and the
right measure is not their size (the next round's derivations are assembled by transitivity,
inversion and weakening, which do not shrink size) but their **nesting depth**: the maximal
nesting of `Ws-Lf2`/`Ws-Sub` well-formedness premises, which the assembling operations leave
unchanged and which each round strictly lowers. This is the concrete form of
`Conjecture8Star`'s remark that the recursion is "plausibly well-founded on the pair of
well-formedness derivations".

A self-referential bound would break this: a bound `w` whose reduct's annotation is (equivalent
to) `w` itself would make the descent stall, and that is the shape of the classical
non-termination of F<: subtyping. Prevalidity forbids it here — annotations mention only
earlier entries, so no term is equivalent to a proper subterm of its own unfolding — which is
also why the search finds nothing.

## 5. What a mechanized proof needs, in order

1. A depth measure on `wf`/`⊑wf`/`⊑*wf` derivations that transitivity (`Ws-Trs`), weakening
   (Lemmas 19–22), inversion (`Lem-10`) and Lemma 16 do not increase. Inversion is the delicate
   one: `Inversion` currently goes through Theorem 3, whose output is a machine chain, not a
   well-subtyping derivation; the measure must be stated on what `Lem-10` actually returns.
2. Lifting of a `≤wf` layer to `[v]` (`AppCongr₁` to `FunStep`, the owed prose of
   `Conjecture8Star`): equivalence steps by `pushᵉ` and `Me-App`; promotions not at the
   outermost parameter by `Ms-App` over the pushed step; well-formedness of every promotion
   point `fᵢ v` from the chain suffix and `f' v wf`. **Obstacle found today:** target-side steps
   (`Ws-Rgh`) move `f'` to a non-well-formed `f''`, and `fᵢ v wf` then needs `fᵢ ≤*wf λt.Top`
   through `f''` — available in the machine relation by commutation, but `Wf-App` wants `≤*wf`
   with well-formed middles. Either a lemma "machine chain between well-formed ends is a
   well-subtyping chain" (choose the promotion points well-formed), or a formulation of the
   lifting that keeps target steps at the outer level and only lifts left steps.
3. `FunStep` from the recursive instance, with the target moved by commutation.
4. The mutual induction of `AppCongr₁`, `FunStep`, Lemma 9 and Lemma 7 on the measure.

Steps 1 and 2 are unconditional and mechanizable now; 3 and 4 are the conjecture.

## 6. Reflection: machine chains between well-formed ends (2026-09-12, later)

The obstacle in §5.2 disappears if a machine chain `u ⟶ˢ* a ⟵ᵉ* t` between well-formed `u` and
`t` can always be replaced by a well-subtyping chain, one whose promotions are between
well-formed terms. `reflect-search.py` tests this on the same contexts and terms as the
conjecture search: at term size 3, **all 8,271 machine-related well-formed pairs are
well-subtyping-related** (80 of them only at a deeper chain cap). If this reflection lemma
holds, the conjecture can be proved in the machine relation — where Theorem 3, strong
commutation and confluence are already available — with well-formedness added at the ends:
`u ⊲ t`, `Co[u] wf`, `Co[t] wf` ⇒ `Co[u] ⊲ Co[t]`, then reflect.

Size 5 (`reflect-size5-2026-09-12.log`): **569,295 machine-related well-formed pairs; all are
well-subtyping-related** — 562,442 at the base caps, 6,837 at a deeper chain cap, and the last
16 (all in the context `y ≡ λ⊤.λ⊤.1, z ≡ y ⊤`, pairs like `y (y y)` against `y (y z)`) at chain
depth 10 and term size 30 (`reflect-deep.py`). Instructive: the *shortest* machine chain for
`y (y y) ⊲ y (y z)` passes through `λ⊤.λ⊤.λ⊤.λ⊤.1`, which is not well-formed, and the
well-subtyping chain is a longer detour. So reflection is not "the same chain with side
conditions checked"; a proof would have to construct the detour, presumably by choosing the
promotion points after the equivalence steps (well-formedness is preserved by evaluation and
by promotion between well-formed ends, not by arbitrary equivalence steps).

## 7. Mechanized reduction to the two binding rules — 2026-09-13

Three new `--safe` modules take §5's steps 1–2 as far as they go without the conjecture's own
content:

- `MPSS/CoFun` — **`FunCongr`**, the abstraction congruence of `≤*wf` from a cofinite family of
  body chains, by closing one name's chain step by step and recovering each family by renaming
  (`MPSS/Wrap` for the steps, `MPSS/WfRename` for the well-formedness premises). Unconditional.
- `MPSS/Conj8Reduction` — the layer walk of §5.2, mechanized: a `≤wf` layer is split into its
  left chain (equivalence steps, and promotions with well-formedness at both ends) and its right
  chain (equivalence steps), every equivalence step lifts to the applied terms by `pushᵉ` and
  `Me-App`, every promotion point's application is well-formed because the point is below the
  target (`app-wf-mid`), and the promotions are lifted by one obligation, **`StepLift`**: a
  single promotion at the empty stack between well-formed terms, under one well-formed
  application. With `MPSS/Conjecture8Star`'s reduction over the transitive layer, and the context
  induction redone on the context's depth so that no `CoLC` premise is needed,
  **`conj8 : StepLift → Conj-8`** for `MPSS/Assumed`'s statement exactly.
- `MPSS/Conj8Push` — `StepLift` generalised over spines, `a ⋅ s₀ ⋅ s`: `Ms-Pro`, `Ms-Top` and
  `Ms-Equ` hold at every stack and lift as one layer; `Ms-App` is the statement one operand
  deeper; `Ms-Fun` and `Ms-FOp` with no extra stack are the step itself. What remains are the two
  rules that bind a parameter, with a non-empty extra stack: **`FunLift`** (`Ms-Fun` at the empty
  stack, whose parameter the first extra operand is about to be bound to) and **`FOpLift`**
  (`Ms-FOp`, whose parameter is already bound to an operand, replayed with more stack).
  **`conj8-from-lifts : FunLift → FOpLift → Conj-8`.**

So Conjecture 8, and with it type safety, rests on `FunLift` and `FOpLift`, and nothing else.

**What the two obligations need, and why the measure is the whole difficulty.** Take `FunLift`
at `s = []`: `(λx≤t.u) v ≤*wf (λx≤t.u′) v` from a body promotion `u ⟶≤ u′` under `x ≤ t`. Both
sides β-reduce by equivalence steps — two each, as in `MPSS/Prop17Chain` — to `u[x\v]` and
`u′[x\v]`, and the layer can absorb those as `Ws-Lf1`/`Ws-Rgh` without any well-formedness. What
is then needed is `u[x\v] ≤*wf u′[x\v]`, which is Lemma 9's statement (promotion under
substitution): off the covariant pattern it is Lemmas 29–30, on it — the promotion *is* of `x`,
`u = Co″[x]`, `u′ = Co″[t]` — it is Conjecture 8 for the pair `(v, t)` in the context
`Co″[x\v]`. And the first `Ws-Lf2` inside that instance needs `u[x\v]` well-formed, which is
Lemma 7, which needs Lemma 9, which needs the conjecture. The recursion is genuine; the paper's
own §5 remark that the four are proved by one mutual induction is right, and the measure is the
open point.

A measure by structural recursion on the *target's* well-formedness derivation was tried on
paper and fails at exactly this point: the recursive instance's well-formedness hypotheses are
those of the *substituted* terms `Co″[x\v][v]` and `Co″[x\v][t]`, which are outputs of Lemma 7,
not subderivations of anything given. A numeric nesting depth (§4) survives that objection only
if Lemma 7 and Conjecture 8 can be shown to return derivations no deeper than their inputs, and
the layer walk above adds one `Wf-App` per promotion point it passes; whether the additions are
bounded across rounds is what a proof would have to settle. That is the next thing to probe —
numerically, on the recursion the three modules now define, before any more Agda.

## 8. The nesting-depth measure, probed — 2026-09-18

`conj8-depth-probe.py` does what §7 left as the next step. The depth of a well-formedness
derivation is 0 at `Wf-PrS`, `Wf-PrE`, `Wf-Top`, the maximum over the premises at `Wf-Fun`, and one
more than its two chains at `Wf-App`; the depth of a `≤wf`/`≤*wf` chain is the maximum over the
well-formedness premises of `Ws-Lf2`, `Ws-Sub` and `Ws-Trs`. `Ws-Trs`, weakening and the
equivalence steps of a layer leave it unchanged, which is what §4 wanted of it. The probe computes,
level by level, the terms well-formed at depth ≤ d and the chains whose ends and promotion points
are, and so the *minimal* depth `md` of every term and chain it can resolve (chain length 4,
promotion cap 2, term size 18; 133 contexts, terms to size 5, three contexts skipped on memory).
Minimal depths are the right thing to test: if the minimal depth of an output exceeds the depths of
the inputs, no proof can return a derivation no deeper than what it was given.

**The measure fails, on the recursion itself.** With `y ≡ λ⊤.0`, take `f = λx≤y. x (y x)` and the
operand `v = y (y y)` (so `v ≡ y`, and `v ≤*wf y`). The promotion of the parameter in head
position gives `f′ = λx≤y. y (y x)`. The instance `(f v, f′ v)` has depth 3 — `f` and `v` have
depth 2 — and the recursive instance `(Co″σ[v], Co″σ[w]) = (v (y v), y (y v))` has depth 4, because
`y v = y (y (y y))` has depth 3 and sits in operand position. This is independent of the caps: an
application is one deeper than its operand (`Wf-App`'s second premise has the operand well-formed
under `Ws-Sub`), so `yⁿ ⊤` has depth n, and substitution copies the operand under the body's
applications. Counts at size 5:

| test | instances | result |
| --- | --- | --- |
| T6, a round of the recursion: `max md` of the recursive instance against the instance | 59,531 | lower 53,167 · equal 6,205 · **higher 60** · unresolved 99 |
| T4, a β-contractum against its redex | 150,941 | lower 131,580 · equal 19,117 · **higher 244** |
| T2, Lemma 7: `md(b[x\v]) ≤ max(md b, md(v ≤ w))` | 151,090 | holds 131,580 · **only ≤ the sum 19,361** · never over the sum · unresolved 149 |

So Lemma 7 cannot return a derivation no deeper than its inputs — the first of §7's two
conditions — and neither "each round strictly lowers the depth" (§4) nor even "no round raises
it" is true. The 149 unresolved substitutions are the caps: at chain length 8 the worst context
(`y≤λ⊤.0, z≤y`, 122 of them) leaves 6, all with head spines that need longer chains still, and the
other two contexts leave none.

**What does hold.** Everything *except* substitution is depth-neutral, on every resolved instance:

| test | instances | result |
| --- | --- | --- |
| T0, a chain needs no more depth than its ends and the context's annotations | 568,694 | 0 excess (5 at chain length 4, in `y≡λ⊤.λ⊤.1, z≤y ⊤`, all gone at chain length 6) |
| T1, Conjecture 8: `Co[u] ≤ Co[t]` at the depth of `Co[u]`, `Co[t]` (size 3, one-layer contexts) | 212,592 | 212,584 at that depth · 0 excess · 8 unresolved |
| T3, Lemma 9 on a single promotion | 365,408 | 365,010 at the bound · 0 excess · 395 unresolved |

The context's own depth has to be counted (a promotion `x ⟶ˢ bound x` lands on the annotation,
which `Ws-Lf2` wants well-formed): without it T0 and T1 show spurious excesses in every context
whose annotation is an application. T0 and T1 answer §7's second worry: the `Wf-App` the layer walk
adds at each promotion point never needs more depth than the two end applications have.

**Keeping the operand in the context** (T5: `x ≡ v` in place of `x ≤ w`, as `Ms-FOp` does, instead
of `b[x\v]`): 162,052 instances, 161,440 within `max(md b, md(v ≤ w))`, 330 over it, 282
unresolved. Every excess is by exactly one and has `x` at the head of an application with `v` deeper
than its bound `w` — where it is forced, since `x a` then needs `x ⟶ᵉ v ≤*wf λt.⊤` through
well-formed points as deep as `v`. An operand occurrence of `x` costs nothing (`Wf-PrE` has depth
0), which is where substitution pays `md v` per enclosing application.

**What this leaves.** A measure that is a function of the terms' minimal depth is dead; this
retires §4's proposal and the second half of §7. What the numbers still allow is a measure on the
two *given* derivations `(D_e, D_v)` in which Lemma 7's output is accounted as `D_e` with copies of
`D_v` plugged at the occurrences of `x` — the additive bound T2 never exceeds — or a formulation of
`FunLift`/`FOpLift` that never substitutes and keeps `x ≡ v` in the context, where the only growth
left is the head-position `+1`. Neither has been tried.

Logs: `.search-logs/depth5_*.log` (T0, T2, T3, T4), `depth5r_*.log` (T5, T6), `depth5esc_*.log`
(the escalations); size 3 runs in 80 seconds (`python3 conj8-depth-probe.py 3 0 1 012356`).

## 9. The two binding rules without substitution, run as an algorithm — 2026-09-18

`conj8-lift-probe.py` tries the second of §8's two leftovers, and it turns out to contain the
first. `FunLift` is read as the machine reads it. Under an operand `v` the machine does not
reduce the body of `λx≤t.u` under `x ≤ t` (`Ms-Fun`) but under `x ≡ v` (`Ms-FOp`); so the body's
derivation is *narrowed*, `x ≤ t` to `x ≡ v`, and pushed under the rest of the stack, by recursion
on the derivation:

| the step `F : p ⟶ˢ q` at stack `s₀`, extra stack `S` | `push(F, S)`: a zigzag of machine steps from `p` to `q` at `s₀ ++ S` |
| --- | --- |
| `Ms-Top`, `Ms-Equ`, `Ms-Pro y`, `y` not narrowed | the step itself |
| `Ms-App F′` | `push(F′, S)`, one operand deeper |
| `Ms-Fun F′`, `S = []` | `push(F′, [])` under `x ≤ t`, each step under `Ms-Fun` |
| `Ms-Fun F′`, `S = v ∷ s` | narrow `x` to `v`; `push(F′, s)` under `x ≡ v`, each step under `Ms-FOp` |
| `Ms-FOp F′` | `push(F′, S)` under `x ≡ α`, each step under `Ms-FOp` |
| `Ms-Pro x`, `x` narrowed to `v`, bound `t` | `x ⟶ᵉ v`, then `lift(D, s₀ ++ S)` for a chain `D : v ≤*wf t` |

and `lift(D, σ)` takes every equivalence step of `D` to the stack `σ` (`pushᵉ`) and every
promotion through `push`. Nothing is substituted; `lift → push → lift` is the conjecture. The probe
runs this on every instance it finds (a chain `u ≤*wf t`, a stack `S` with `spine u S` and
`spine t S` well-formed) and checks the result at the top level, in the original context at the
empty stack: every step a machine step, every promotion between well-formed terms, every turn from
backward to forward steps at a well-formed term. The nested chains `D` are the shortest the search
finds.

| run | instances | with a round | result |
| --- | --- | --- | --- |
| terms to size 3, stacks of one or two operands | 60,779 | 17,447 | all valid |
| terms to size 5 (7 of 8 shards, one lost to memory after 8 of 17 contexts; 4 contexts skipped) | 2,967,285 | 833,161 | all valid; 29 promotion points the oracle missed, all found at chain length 8 |
| subjects of size 7 that apply their own parameter, sampled (120 per context), stacks of up to three operands, targets read off the subject's forward closure (23 contexts skipped on memory, two shards cut short by their time limit) | 1,688,723 | 1,418,772 | no invalid step, no unresolved chain, no budget hit; 507 instances keep a promotion point the oracle cannot confirm — terms of about 20 nodes, over its size cap of 18 |

No instance failed, none ran out of budget, the pending stack reached four operands, and nesting
reached two rounds (31,172 instances).

**The order the recursion descends in.** Round `k` narrows a parameter of bound `t_k` to an
operand `v_k`. The next round happens inside `lift(v_k ≤*wf t_k, σ)`: an abstraction
`λx′≤t′.…` of that chain meets the first operand of `σ`. That abstraction is below `t_k`, and `t_k`
is applied to the same operand (`spine t_k σ` is well-formed), so `t_k ≤*wf λt″.⊤` and, by
inversion (Lemma 10), `t′ ≡wf t″`: **the bound of each round is the domain of the bound of the round
before.** The probe checks it on every nested round — 31,178 of 31,178. It is the order on which
hereditary substitution terminates for simple types, and it is the measure on the given
derivations that §8 asked for: not their depth, which grows (the pair (body depth, operand depth)
goes to at most (operand depth, body depth − 1 + operand depth)), but the rank of the bound, with
the second component of a lexicographic pair being the derivation `F` itself, on which `push` is
structural.

**The substitution route does not have this descent.** `Lem-9`/`Lem-7` reach the same place through
`b[x\v]` and a context induction (`conj8-n`), which re-enters an abstraction the body already
applies — `(λz≤A. x z) o` — under `z ≤ A` (`FunCongr`, then `AppCongr` with `o`), and a given
derivation of `z ≤*wf ⊤` that goes through `z ⟶ˢ A` then asks for the conjecture at the pair
`(o, A)`, whose rank is unrelated to anything before. The machine binds `z ≡ o` there and the
narrowing route never promotes `z`. So the mutual induction of the paper's §5 (Conjecture 8 with
Lemmas 7 and 9) is the wrong shape for the measure; the stack-aware one is the right one.

**What Conjecture 8 reduces to.** Whenever the recursion terminates the conjecture holds for that
instance: the well-formedness of every wrapped intermediate is the `app-wf-mid` argument, a point
below the target applied to the same operand. It terminates when the domain order — `T ▷ d` if
`T ≤*wf λd.⊤`, `T ▷ T v` if `T v` is well-formed — has no infinite descending chain from the bounds
involved. Prevalidity excludes a cycle through the context (§4); a cycle or an infinite descent
through *computation* needs a well-formed bound with no normal form of finite rank, the type-level
image of a looping combinator, which the paper (§6) says exists for PSS only as a mechanically
derived term of some forty pages. So:

- a counterexample to Conjecture 8 cannot be small: it needs an infinite domain descent, and even
  then the conjecture may hold by another chain (with a hypothetical `T ≡ λT.⊤` and
  `δ = λx≤T. x x` the instance `δ δ ≤ (λx≤T. T x) δ` holds, though the recursion loops on a
  perversely chosen derivation of `δ ≤*wf T`);
- an unconditional proof along this recursion needs the domain order well-founded on well-formed
  bounds, which is a normalization statement about the type level of MPSS and is not known.

What can be proved is the conditional theorem: *if the domain order is well-founded, Conjecture 8
holds* — by induction on the rank of the bound, then on the step derivation.

Logs: `.search-logs/lift5_*.log`, `lift5_recheck.log`, `lift7s_*.log`.

## 10. What is mechanized of §9, and the proof it is a part of — 2026-09-18, night

Six new `--safe` modules, nothing existing touched.

| module | content |
| --- | --- |
| `MPSS/Conj8Pair` | `Lem-9ᵖ`, `Lem-7ᵖ`: Lemmas 9 and 7 for the substitution `x := α` with `α ≤*wf t` need Conjecture 8 **at the pair `(α, t)` only**, in the contexts extending the one the pair lives in (`C8At Γ α t`). The proofs are those of `MPSS/Lemma9` and `MPSS/Lemma7` with the one call replaced |
| `MPSS/FunLift0` | `FunLift₀`: `(λx≤t.u) v ≤*wf (λx≤t.u′) v` from a body promotion under `x ≤ t`, **from `C8At Γ v t`** — §7's sketch: both sides β-reduce through well-formed terms (`Prop-17ʷ`), `v ≤*wf t` by inversion (`operand≤`: Lemmas 10, 15, 16), the middle is `Lem-9ᵖ`, the two ends are well-formed by `Lem-7ᵖ` |
| `MPSS/PushWf` | `⇛-push`: §9's `push`, for the chains the conjecture is about. A promotion derivation at `Γˢ ∣ s₀`, annotated at its leaves, replays at the narrowed `Γᵉ ∣ s₀ ++ s` as `Γᵉ ∣ s₀ ++ s ⊢[ P ] a ◁* a′` (`MPSS/Frame`), the side condition `P` a parameter that becomes `App P v` under an application and `Fun P t x` under a binder. An abstraction that meets an operand narrows its parameter and goes on (`q-fun-cons`); the datum at a narrowed variable is **one chain `α ◁* t` at the stack in force under the side condition in force** — not `MPSS/Push`'s reachability at every stack, which `MPSS/ReachFails` refutes |

| `MPSS/Annotate` | `push-from-leaves`: a *plain* promotion derivation, with the side condition at its two ends, lifts to `Γᵉ ∣ s₀ ++ s` — the annotation `⇛` is built by recursion on the derivation, the side condition carried down unchanged (`App P v u` is `P (app u v)`; `Fun P t x (u ^ x)` is `P (lam t u)` up to `close-open`). Asked from outside: a supplier of the chain `α ◁* t` at each rebound variable, and one (`NewLeaf`) at each abstraction that meets an operand — for a class `𝒫` of side conditions closed under the two wrappers |
| `MPSS/Conj8FromLeaves` | **`conj8-from-obligation : Obligation → Conj-8`.** With `𝒫` the class `𝒲` generated from "`z` applied to `v` is well-formed" by the wrappers, `StepLift` follows from `NewLeaf 𝒲`, and `conj8` of `MPSS/Conj8Reduction` does the rest. `FOpLift` is gone — an abstraction already entered under an operand is structural — and `FunLift` has become the one obligation, in stack form |

`Obligation`, unfolded: *for a generated side condition `P` at `Γᵉ ∣ α ∷ s′` that holds at
`λx≤t.u` and `λx≤t.u′`, and `x` fresh — for every extension `Γ′` of `x ≡ α, Γᵉ`, every stack `σ`
and every generated `P′` at `Γ′ ∣ σ` that holds at `t`: a chain `Γ′ ∣ σ ⊢[ P′ ] α ◁* t`.* That is
Conjecture 8 at the pair (operand, annotation), in the narrowed context, at a stack, with the
well-formedness of the wrapped points as the side condition — the form in which the recursion can
call itself, and the only thing not machine-checked.

`MPSS/DomainOrder` adds the order itself (`_▷ᵈ_`: a target steps down to its domain and to itself
applied, in any extension of its context), `domain-step` — an abstraction `λx≤w.u` below `T`, with
`T v` well-formed, has `w ≡wf` the domain of `T` and `v ≤*wf w` — and the conditional conjecture
`Conj-8ʳ` as a type, **declared and not proved**.

So the structural half of the recursion is checked: `lift → push` is `⇛-push`, and the only thing
it asks from outside is `push → lift`, the chain at a narrowed leaf.

**The rest of the proof, as it now stands on paper.** Not mechanized; every step below that is not
a citation is an obligation.

1. *Rank.* `rk Γ T` is 0 if no application `T o` is well-formed in (an extension of) `Γ`, and
   otherwise one more than the ranks of the domain `d` (`T ≤*wf λd.⊤`) and of every well-formed
   `T o`. By inversion (Lemma 10) the domain is unique up to `≡wf`, and two terms below a common
   abstraction have `≡wf` domains, so `rk` is invariant under `≡wf` and along `≤*wf` between
   applicable terms. *Hypothesis of the theorem:* `rk` is finite on the targets involved.
2. *Main statement*, by induction on `rk Γ t`, then on the size of the covariant context, then on
   the chain: Conjecture 8 at the target `t` — for every extension of `Γ`, every `a ≤*wf t` and
   every covariant context.
3. *Application frame.* `walk` of `MPSS/Conj8Reduction`, with each promotion `p ⟶ˢ p′` lifted
   under the operand by `⇛-push` from the annotation of its derivation (`s₀ = []`, `s = [v]`).
   A binder the derivation already enters under an operand (`Ms-FOp`, a redex the term had) is
   structural and costs nothing — this is where the substitution route loses the descent (§9).
   An abstraction `λx≤w.b` that meets the operand is narrowed, `w ≡wf` the domain of the frame's
   target, so `rk w < rk` of the target, and `v ≤*wf w` by `operand≤`.
4. *Narrowed leaf* `x ≡ α`, old bound `w`, stack `σ`: the chain `α ◁* w` at `σ` is the main
   statement at the target `w` for the spine `σ` in the narrowed context, by 2 at lower rank.
5. *Side condition.* `P z` is well-formedness of the whole term with `z` in the hole. For the
   points of a lifted chain it should follow from `z ≤*wf w` and well-formedness at `w`, frame by
   frame of the wrapper: `app-wf-mid` at an application frame, with `z v ≤*wf w v` from the lifted
   chain at the smaller wrapper; `Wf-Fun` at a binder, in the **un-narrowed** context, where the
   same lifting has to be available. **This is the least checked step.** It makes the induction
   (rank of the bound, size of the wrapper, length of the chain), with the lifting and the
   well-formedness of its points proved together; and the lifting must be kept in stack form
   (`◁*` at a stack, as `⇛-push` returns it) all the way, because a chain of whole applied terms
   cannot be taken apart again into steps at a stack, so `FunLift`/`FOpLift` as stated in
   `MPSS/Conj8Push` — over spines at the empty stack — are the wrong interface for the recursion.
   The probe checks the conclusion of this step (every wrapped point well-formed) on every
   instance, not the argument.
6. *The leaf's chain is ours to choose only below the first round.* The top chain is given; the
   chains at narrowed leaves come out of `Wf-App` premises (through `operand≤`), so they too are
   given. Step 4 needs nothing of them but the rank of their target.

**Why this is the end of what small cases can say.** The recursion terminates whenever `rk` is
finite, and then the conjecture holds. If a well-formed `T` with `T ≡wf λx≤T.⊤` existed, the
recursion would loop on a suitably given derivation (§9's `δ δ`), though the instance itself still
holds through a shorter chain; whether an instance can *fail* there is what a refutation would
have to show, on terms the size of a type-level looping combinator. Nothing in MPSS's
well-formedness rules out such a `T` — contexts need only be prevalid, and `Wf-Fun` does not bound
the annotation's rank — and nothing small builds one: self-application at a bound `P` needs
`P ≤*wf λd.⊤` and `P ≤*wf d`, which with invariant annotations is a recursive type.

**Status.** Conjecture 8 is neither proved nor refuted. There is a proof plan for every instance
whose targets have finite domain rank — the structural half mechanized (`⇛-push`), the recursion
validated by execution on 4.7 million instances, steps 1 and 5 above owed — and any
counterexample has infinite domain rank.

## 11. The other direction: with one recursive function type the conjecture is false — 2026-09-18

§9–10 say the conjecture holds where the domain order is well-founded. This section is the
converse in the simplest case, and it is what makes the domain order the right thing to look at.

**The extension.** MPSS plus one definition that prevalidity forbids, `R ≡ λx≤R.R` — a bound
whose domain and codomain are itself. Everything else is unchanged. This is *not* MPSS; it is what
MPSS would contain if a type-level fixed point were well-formed in it.

**The instance.** `δ = λx≤R. x x`, `f = λx≤R. x δ`, `f′ = λx≤R. R δ`, context `□ δ`.

- `x x` is well-formed under `x ≤ R`: `x ⟶ˢ R ⟶ᵉ λx≤R.R ⟶ˢ λx≤R.⊤`, and the operand `x ≤*wf R`.
  So `δ` is well-formed, and `δ ≤*wf R` (`δ ⟶ˢ λx≤R. R x ⟶ᵉ λx≤R.R ⟵ᵉ R`), so `δ δ` is too.
- `f ⟶ˢ f′` at the empty stack (`Ms-Fun`, `Ms-App`, `Ms-Pro`), between well-formed terms:
  `f ≤*wf f′`. And `f δ`, `f′ δ` are well-formed. The conjecture says `f δ ≤*wf f′ δ`.
- It does not hold. `f′ δ` reduces to `R δ`, to `R`, to `λx≤R.R`; none of its `⟶ᵉ` reducts contains
  `⊤`, and `⟶ᵉ` never deletes a `⊤` on the head path nor creates one. `f δ` reduces to `δ δ`, which
  reduces to itself. Under the operand every abstraction on the head path is entered by `Ms-FOp`,
  so its parameter is `≡`-bound and `Ms-Pro` never applies; the only promotion available anywhere
  on the head path is `Ms-Top`, whose `⊤` then stays in every later term of the chain, forward or
  backward. So a chain from `f δ` to `f′ δ` would consist of equivalence steps alone, and `δ δ` and
  `R` have no common reduct: one has no head normal form, the other is an abstraction.
- Lemma 6 fails with it: `g = λx≤R. (x δ) δ` is well-formed, so is `g δ`, and `g δ ↦ (δ δ) δ`,
  which is not — `δ δ` is below no abstraction. So in MPSS + `R` evaluation does not preserve
  well-formedness, and type safety as sketched fails.

The recursion of §9 shows why: narrowing `x ≡ δ` asks for `δ` to reach `R` *under the operand*,
which asks for the body `x′ x′` to reach `R`'s body under `x′ ≡ x`, which is the same question;
with codomain `⊤` in place of `R` the question is answered at once by `Ms-Top` (§9's `T ≡ λx≤T.⊤`),
with codomain `R` it never is.

**What this says about MPSS.** Conjecture 8 holds on the instances of finite domain rank (plan of
§10, structural half mechanized) and fails in the presence of a recursive function type with a
non-trivial codomain. So the conjecture is, in substance, the statement that well-formed MPSS has
no such type — not the exact fixed point used here, which would need a fixed-point combinator,
but the infinite domain descent a type-level *looping* combinator gives (`T_n ≡ λx≤T_{n+1}.T_{n+1}`
from `L_n F ⟶ F (L_{n+1} F)` with `F = λr≤⊤.λx≤r.r`). The paper's §6 takes such combinators to
exist in PSS through the encoding of System λ*. Whether the encoding survives MPSS's
well-formedness, and whether the descending family (no exact fixed point, so no `δ`) still yields
a failing instance, is what is left between this and a refutation. If it does, it refutes type
safety of the sketched system too, since the conjecture is what preservation rests on.

`conj8-rectype-probe.py` runs the instance in the extended system: the fourteen steps the
well-formedness of `δ`, `δ δ`, `f`, `f′`, `f δ`, `f′ δ` and `f ≤*wf f′` rest on are all machine
steps; within chains of length 6, the 5,772 terms reached from `f δ` by `⟶ˢ` and the 13,281
reached from `f′ δ` by `⟶ᵉ` have none in common, no reduct of `f′ δ` contains `⊤`, the only
`⊤`-free terms reached from `f δ` are `δ δ` and its expansions, and of 5,917 terms reached from
`δ δ` none is an abstraction. The non-existence of the chain is argued above, not mechanized —
the development's relations cannot hold the entry `R ≡ λx≤R.R`.

**A tension in the paper.** §6 of the paper argues for Turing-completeness from a *well-formed
looping combinator*, and §4 conjectures context independence on the way to type safety. A
looping combinator at the type level gives bounds of infinite domain rank, and with a term-level
one alongside it (`c_n = λz≤T_{n+1}. z c_{n+2}` at `T_n ≡ λx≤T_{n+1}.K`, `K` not `⊤`) the instance
above has an analogue: `c_n c_{n+1}` diverges, is expected below `K`, and can reach nothing but
`⊤`. If MPSS's well-formedness admits those combinators, Conjecture 8 and preservation of
well-formedness fail there; if Conjecture 8 holds, it does not admit them. Both are open; they
are not independent.

## 12. The proof of `Obligation`: work list — 2026-09-18, morning

`Obligation` (`MPSS/Conj8FromLeaves`) is what is left. Facts live in two kinds of context and the
proof has to keep them apart: **well-formedness and `≤*wf` facts live in the un-narrowed context
`Γˢ`** (they come out of `Wf-App` and `Wf-Fun` premises), **the steps of the chain being built
live in the narrowed context `Γᵉ`**, and `Γˢ ▶ᴸ Γᵉ` with its suppliers is the bridge — which is why
`NewLeaf` now receives it.

Done: `Wrapper` (a generated side condition is well-formedness of the closed-up term, both
directions), `BelowWf` (`below-wf`: from Conjecture 8 at a target `t`, every `m ≤*wf t` is
well-formed in every covariant context `t` is — the side condition at the points of a lifted
chain, from the induction hypothesis at the bound).

Owed, in dependency order:

1. `⊒` as a prefix, and `≤*wf` weakened along it.
2. The ranked layer walk: `walk`, `appcongr`, `conj8-n` of `MPSS/Conj8Reduction` with `StepLift`
   asked only for steps below a target of bounded rank (they take it for all steps now).
3. A generated wrapper read as a covariant context: `close ok z = plug C z′`, with the frame
   variables of `z` closed at the right indices; then `below-wf` gives the side condition.
4. The operand's chain when the abstraction was reached through an `Ms-FOp` frame,
   `((λt₀.λt.u) α₀) α`: there `α ≤*wf t` holds only with `y ≡ α₀`, and comes from
   `α ≤*wf d`, `(λt₀.λt.u′) α₀ ≤*wf λd.⊤` and an inversion of that chain through the β-step
   (`t[α₀]` and `d` have a common reduct; `⟶ᵉ-subst≡` for the annotation). Without an `Ms-FOp`
   frame in between it is `operand≤`.
5. The numeric rank `Rank≤ n`, its invariance under `≡wf` and along `≤*wf` between applicable
   terms, and the descent (`domain-step`, and its form under item 4).
6. The induction on the rank bound `n`: `NewLeaf` at `n + 1` from the conjecture at rank `n`
   (for `below-wf`) and `push-from-leaves` with `NewLeaf` at `n`.

## 13. The narrowing route is wrong for dependent bounds; `Obligation` is false — 2026-09-18, morning

`conj8-poly-instance.py`. Take `A = λ⊤.⊤` and

    p  = λy≤⊤. λo≤y. λx≤(λz≤y.⊤). x o        p ⟶ˢ p′ = λy≤⊤. λo≤y. λx≤(λz≤y.⊤). (λz≤y.⊤) o

under the context `((□ A) a) α` with `a = A` and `α = λz≤A.z`. Both plugs are well-formed and the
conjecture **holds**: both sides β-reduce, by equivalence steps, to `α a` and `(λz≤A.⊤) a`, and
`α ≤*wf λz≤A.⊤` lifts under `a`.

The narrowing algorithm of §9 does something else. It keeps the three abstractions in place, binds
`y ≡ A`, `o ≡ a`, `x ≡ α`, unfolds `x` to `α` and promotes — at the point

    (λy≤⊤. λo≤y. λx≤(λz≤y.⊤). α o) A a α

which is **not well-formed**: read as a term, its body has `α o` under the *abstract* `y`, where
`o` is below `y` only and `α`'s domain is `A`. The probe's oracle does not find it well-formed at
any chain length, and it is not. So:

- **§9's "valid on every instance" was a statement about the instances tried.** None had a bound
  that depends on a parameter instantiated by an earlier operand; the 542 "unconfirmed" points of
  the sampled runs have to be re-read in this light.
- **`Obligation` of `MPSS/Conj8FromLeaves` is false** at this instance: the chain `α ◁* t` it asks
  for must start at `α` under the side condition "the closed-up term is well-formed", which fails
  at `α`. `conj8-from-obligation` stays a theorem, with a hypothesis that does not hold.
- **§10's step 5 is wrong**, not merely unchecked: the closed-up points of a lifted chain need not
  be well-formed under the abstract binders.
- What the instance shows is that `≤*wf`'s freedom to take equivalence steps through ill-formed
  terms is essential: the chain that works β-reduces the consumed redexes **first**, so that
  promotions happen on instantiated terms. That is the substitution route (`FunLift₀`, Lemmas 7
  and 9), whose promotion points are reducts of well-formed terms.

So §9's comparison of the two routes is reversed on this shape. What survives: the descent in the
domain order (`domain-step`), `Conj8Pair`, `FunLift0`, `BelowWf`, `RankedWalk`, and §8, §11. What
has to be redone: the measure for the substitution route, where §9 found calls to the conjecture
at pairs `(o, A)` from redexes the body already contains — to be looked at again with the freedom
to contract those redexes first.

## 14. Conjecture 8 is false as stated — machine-checked, 2026-09-18

`MPSS/Conj8Refuted`: **`¬Conj-8 : ¬ Conj-8`**, under `--safe`, no postulates. With it
`¬Lem-6`, `¬Lem-7` and `¬Thm-5`: Lemma 6 (evaluation preserves well-formedness), Lemma 7
(substitution preserves it) and Theorem 5 (preservation) are false as stated too.

**The observation.** §11 refuted the conjecture in MPSS *extended* by a recursive type. No
extension is needed. A logical context only has to be **prevalid** — `Pv-EqA` asks that the
annotation's free variables be in the domain, nothing about well-formedness — and `Wf-PrE` makes
a variable well-formed as soon as it occurs in a prevalid context (`MPSS/EqvWf` had used this
already). So a context may define a name by a term with no normal form:

    ω = λs≤⊤. λx≤(s s). (s s)        W = ω ω        Γ₀ = R ≡ W

`W` is ill-formed (`s s` under `s ≤ ⊤`), closed and locally closed; `Γ₀` is prevalid. `W` reduces
to `λx≤W.W` — two steps, the first binding and unfolding the parameter as in `Prop17Chain` — and
so does the **well-formed** `λx≤R.R`, in one. So `R ≤*wf λx≤R.R`: in `Γ₀`, `R` is the recursive
function type of §11, with `λx≤R.R` as its well-formed representative.

**The instance.** `δ = λx≤R. x x`, `δ ⟶ˢ t′ = λx≤R. R x` at the empty stack, context `□ δ`.
Derived in Agda: `R`, `λx≤R.R`, `λx≤R.⊤` well-formed; `R ≤*wf λx≤R.⊤`; `x x` and `R x` well-formed
under `x ≤ R`; `δ`, `t′` well-formed; `δ ≤*wf t′`; `t′ ≤*wf R` (the body `R x` unfolds `R` under the
operand `x` and contracts to `W`); `δ ≤*wf R`; `δ δ` and `t′ δ` well-formed. Those are all the
hypotheses of `Conj-8`.

**The conclusion fails.** From `δ δ ≤*wf t′ δ`, Theorem 3 (`Thm-3wf`) gives a machine chain: a
list of promotions from `δ δ` and of equivalence steps from `t′ δ`, meeting. `t′ δ` reduces to the
abstraction `λx≤W.W` in seven steps. `no-chain`, by induction on the chain: the right side keeps
reaching an abstraction (`strip*`, confluence of `⟶ᵉ*` from `MPSS/Strip`, and a reduct of an
abstraction at the empty stack is one); the left side stays in the class `Bd` of `MPSS/AppClass`

    Cl ::= bound variable | free variable other than R | ⊤ | λx≤(anything). Bd | Cl Cl
    Bd ::= Cl Cl | ⊤

which both reductions preserve at a configuration with no subtype entry, `Cl` on the stack and
`Cl` for the `≡`-annotations other than `R`'s; when the two sides meet, a term of `Bd` reaches an
abstraction by equivalence steps, and `Bd` has none. The reason is the one of §11: under an
operand every abstraction on the head path is entered by `Ms-FOp`, so its parameter is `≡`-bound
and `Ms-Pro` never fires; `R` occurs only in annotations, which never come to a head position.

**Lemma 6, Lemma 7, Theorem 5.** `g = λx≤R. (x δ) δ` is well-formed (`x δ` promotes to `R δ`, which
reduces to `W`, as `R` does), so is `g δ`, and `g δ ↦ (δ δ) δ`, which is not: `Wf-App` would put
`δ δ` below an abstraction. Lemma 7 goes with Lemma 6 (`Lem-6ʷ`), and preservation with
`g δ ≤*wf g δ`. The development's `type-safety` in `MPSS/Preservation17` is proved *from*
`Conj-8`: from a false hypothesis, as the earlier `Prop-17ʳ` was.

**What this does and does not say.**

- The paper's Conjecture 8, Lemmas 6 and 7 and Theorem 5 are stated for "a logical context", and
  the paper's prevalidity (Figure 1) and `Wf-PrE` are as transcribed. As stated they are false.
- The repair that suggests itself is a well-formedness premise on the annotations in `Pv-Ctx` and
  `Pv-EqA`. **Under it everything is open again**: the counterexample needs an ill-formed
  annotation. §11 then says what a counterexample would need — a well-formed term behaving as `R`
  — and §8, §9, §13 say what a proof cannot be.
- A proof cannot be an induction on the domain rank of §9 either: the domain order is not
  well-founded on well-formed terms. With `T = λy≤⊤. λx≤y. y`, the type of the polymorphic
  identity, `T T` is well-formed and `T T ≤*wf λx≤T.⊤`: `T` steps to `T T`, whose domain is `T`
  (`MPSS.DomainOrder.Ranked` is uninhabited at `T`). A proof under the repaired prevalidity would
  have to be by reducibility, with the instantiations of a parameter bounded by `⊤` interpreted by
  candidates — and that is exactly what type-level computation without a normal form would break.

## 15. The repaired statements — 2026-09-18

`MPSS/WfCtx`: `WfCtx Γ` — every annotation well-formed in the entries before it — and
`Conj-8ʷᶜ`, `Lem-6ʷᶜ`, `Preservationʷᶜ`, the statements with `WfCtx Γ` as a hypothesis on the
logical context. The premise is on the statement's context, not inside the reductions: a
well-subtyping chain takes equivalence steps through ill-formed terms and `Me-FOp` binds a
parameter to whatever operand is there, so a well-formedness premise in `Pv-EqA` itself would
change `⟶ᵉ`, not just the statements. `¬WfCtx-Γ₀`: the context of §14 is excluded (`ω ω` is not
well-formed — its annotation `s s` would need a variable bounded by `⊤` below an abstraction). So
the three statements are **open**, and every theorem of the development holds over `WfCtx`
contexts as it is.

The probes' 133 contexts include 8 with an ill-formed annotation (`z ≤ y ⊤` or `z ≡ y ⊤` where `y`
is not below an abstraction); 125 are `WfCtx`. Over those, the substitution route run as an
algorithm (`conj8-subst-probe.py`): 3,190,343 instances at size 5 (7 of 8 shards done, one cut
short, 5 contexts skipped on memory), none invalid, none unresolved; sampled size 7 with stacks of
up to three operands, 1,567,796 instances (4 of 6 shards done, 24 contexts skipped), no invalid
step, none unresolved, 847 with a promotion point the oracle cannot confirm (terms over its size
cap). Over all contexts, every nested use of the conjecture (1,037) is at a bound of lower rank
than the use it sits in. The dependent-bound generator
(`conj8-dep-gen.py`) works in the empty context, which is `WfCtx`: 800 of 800 valid by the
substitution route.

## 16. Towards a provable variant: reducibility over ranked targets — 2026-09-18

The variant aimed at: Conjecture 8 over `WfCtx` contexts, for pairs whose targets are accessible
in the domain order (`Ranked`, `MPSS/DomainOrder`). It leaves out exactly what §14 shows cannot be
handled by rank — the type of the polymorphic identity is not `Ranked` — and what §11 shows would
be a counterexample.

Its proof cannot be a rank induction *on the conjecture*: the conjecture is used, on the way, at
pairs of unrelated rank (a redex the body already contains, §9; the contractum of a head redex,
§13). The standard way out is reducibility: define by recursion on the rank a predicate that can
then be *used* at any rank, and prove the fundamental lemma by induction on derivations, under
substitutions of good terms.

`MPSS/Reducible`, mechanized so far:

- `Good a m`, for `a : Ranked Γ T`: `m` well-formed, `m ≤*wf T`, and — in every extension of the
  context, for every `v` good at the domain of `T` — `m v ≤*wf T v` and `m v` good at `T v`.
  Conjecture 8 for spines, made hereditary. Defined by recursion on the accessibility proof.
- `good-irr`: it does not depend on that proof.
- `neutral-good`: a term that promotes to the target at every stack — a variable and its bound —
  is good at it. The base case.

- `good-expand`, `good-trans`, `good-reduct`, `good-join`: closed under equivalence expansion on
  the left; composes (the `Ws-Trs` case); a well-formed reduct of the target is good at it; and the
  chain form a layer needs — two well-formed terms that join by equivalence steps, through terms
  that need not be well-formed.

So every part of a well-subtyping derivation is covered except the promotion step itself. For a
step `p ⟶ˢ p′` between well-formed terms, `Good p′ p` goes by the derivation: `Ms-Top` is vacuous
(`⊤ v` is never well-formed), `Ms-Equ` is `good-join`, `Ms-Pro` is `neutral-good`, `Ms-App` is
the same statement at the stack one operand deeper — and `Ms-Fun` under a good operand `v` is
β-expansion to the body **with `v` substituted for the parameter**, where the induction hypothesis
has to be available. That forces the statement to be about derivations under a simultaneous
substitution of good terms (Tait's form), over the single-substitution lemmas the development has
(`⟶ᵉ-drop`, `⟶ˢ-drop′`, `Lem-28-ctx`). That is the next module.

Owed: the
fundamental lemma (a well-formed `b` under good substitution is well-formed, and `a ≤*wf c` under
good substitution is good), whose abstraction case is β-expansion with the body taken under the
substitution extended by the operand; and Conjecture 8 from it, by filling the hole with a
variable bounded by the target.

**A design question this does not answer.** `Ranked` is a semantic condition on targets. A
*language* in which every well-formed term is ranked — so that the variant is a theorem about a
system and not about instances — needs a syntactic stratification (no parameter bounded by `⊤`
used as an annotation, or universe levels on `⊤`), and which one is wanted is a choice about the
calculus, not about the proof.

## 17. Type safety over `WfCtx`, and the design of the fundamental lemma — 2026-09-19

**Done.** `MPSS/WfCtxSafety`: Lemmas 7 and 6 and Theorem 5 over contexts with well-formed
annotations, from `Conj-8ʷᶜ` alone. The `WfCtx` premise threads through Lemma 7's induction — the
`Wf-Fun` case extends the context by `z ≤ w[x := α]`, well-formed by the induction hypothesis on
the annotation — so no separate lemma that substitution preserves `WfCtx` was needed.

**The fundamental lemma, as it will be built.** Tait's form, with the development's
single-substitution lemmas reused rather than a parallel substitution redone.

- A substitution `θ` is a list of pairs `(x, α)` acting on terms one after the other. A relation
  `Γ ⊢ θ ⇒ Γ′` is generated by three kinds of step, each backed by a lemma the development has:
  substituting a `≤`-bound name in the middle of the context (`Lem-28-ctx`, `⟶ᵉ-drop`), substituting
  a `≡`-bound name by its definition (`prevalid-subst≡`, `⟶ᵉ-subst≡`), and weakening in the middle,
  which has no action on terms (`⟶ᵉ-weaken`). From these, by induction on the list: `θ` preserves
  prevalidity and `⟶ᵉ` at every stack. It lifts under a binder and extends by `z := v` at the head.
- `θ` is good for `Γ` into `Γ′` when every `x ≤ t ∈ Γ` has `xθ` good at `tθ` in `Γ′`. Stated about
  the result of the action, so no invariant on the list's entries is needed.
- A well-formedness derivation is folded into a datatype `SW` that records, for every application
  in the term, the goodness of the operand at the domain under every good `θ`, and for every
  abstraction the same for its body. It is a datatype so that the lemma for a promotion can
  invert it freely while recursing on the promotion alone.
- The promotion lemma, by induction on `Γᵉ ∣ s ⊢ p ⟶ˢ p′`: `(p s)θ` is good at `(p′ s)θ`. `Ms-Pro`
  is the goodness of `xθ` applied down the stack; `Ms-Equ` is `good-join`; `Ms-Top` is vacuous
  under an operand; `Ms-App` moves an operand to the stack; `Ms-FOp` extends `θ` by `z := αθ` and
  closes under the β-step; `Ms-Fun` lifts `θ` under the binder for the chain (`FunCongr`) and
  extends it by `z := v` for the operand. The reductions run in a context `Γᵉ` that has `≡` where
  the well-formedness context `Γˢ` has `≤`; `θ` acts the same on both.
- Conjecture 8 from it: `C[x] ⟶ˢ C[t]` is one promotion in `x ≤ t, Γ`, and `θ = [x := u]` is good
  because `u ≤*wf t` is, by the lemma at the empty substitution.

**The hypothesis that every target is ranked.** `Good` is indexed by an accessibility proof. The
first version takes `∀ Γ T. Γ ⊢ T wf → Ranked Γ T` as a module parameter. That is false in full
MPSS (§14: the type of the polymorphic identity), so a theorem under it says nothing until it is
relativized to a class closed under what the proof uses; the places the parameter is called are
the list of closure properties. A class that should satisfy them: terms whose erasure is simply
kinded (`⊤` at every kind, `x ≤ t` at the kind of `t`), which excludes `T T` and is preserved by
substitution and by both reductions.

## 18. The reducibility argument closes; `Ranked`, as defined, is too strong — 2026-09-19

**Mechanized.** `MPSS/ReducibleMore`, `MPSS/Morphism`, `MPSS/GoodAt`, `MPSS/GoodSubst`,
`MPSS/Fundamental`, `MPSS/Conj8Ranked`, all `--safe`, as designed in §17:

- `STEP` (the promotion lemma) and `FL-wf`/`FL-sub` (the fundamental lemma) typecheck, termination
  included. `img ∘ FL-wf` is Lemma 7 for good substitutions with no appeal to Conjecture 8.
- `conj-8ʷᶜ : Conj-8ʷᶜ`, and through `MPSS/WfCtxSafety`, `Lem-6ʷᶜ` and `Preservationʷᶜ` — under
  the module parameter `rk : ∀ Γ T. Γ ⊢ T wf → Ranked Γ T`.

So the part that was in doubt — whether a reducibility argument closes, given that the conjecture
is used on the way at pairs of unrelated rank — is settled: it does. `rk` is false in full MPSS,
so this is a statement about the argument and not yet a theorem about a calculus.

**`Ranked` is too strong, not only at `T`.** The order `▷ᵈ` lets a target step to itself applied
to *any* operand that makes the application well-formed. With `T = λy≤⊤.λx≤y.y` and
`id = λx≤⊤.x`: `id (T T)` is well-formed, `id (T T) ≤*wf λx≤T.⊤`, and `(id (T T)) T` is
well-formed (`MPSS/conj8-id-unranked.py`, by the probe's checker — not mechanized). So

    id  ▷  id (T T)  ▷  T  ▷  T T  ▷  T  ▷  …

and `id` is not `Ranked`. The same goes for every abstraction whose bound admits `T T`. The
variant of §16 ("targets accessible in the domain order") therefore covers very little of full
MPSS, and relativizing `rk` to a class of *targets* cannot work: the order itself has to range
over operands of the class only.

**What a theorem about a calculus needs.** A sub-calculus whose derivations mention only terms of
a stratified class — simply-kinded terms are the candidate: `⊤` at every kind, a name at the kind
the context assigns it, `λx≤t.u : κ₁ → κ₂` with `t : κ₁`. Two observations from the mechanized
argument shape it:

- With kinds, `Good` is defined by recursion on the **kind** (Tait's definition), not on an
  accessibility proof. The kind is only the measure: neither term needs to be kinded for the
  definition to make sense, `⊤` is a target at every kind, and `rk`, `good-irr` and the order
  disappear. The six modules carry over with a kind where they have an accessibility proof.
- Kinding of the *terms* of a statement is not enough: `Wf-App` quantifies existentially over the
  domain `d`, and a well-formed derivation of a kinded term can pass through an unkinded `d` that
  is equivalent to a kinded one (`d = (λy≤⊤.⊤)(T T)`). The fundamental lemma recurses on every
  derivation it meets, so the judgements themselves have to be the kinded ones (`wfᴷ`, `≤*wfᴷ`:
  every term mentioned is kinded), with subject reduction for kinding under `⟶ᵉ` and `⟶ˢ`. The
  theorem is then type safety of kinded MPSS.

Which stratification is wanted — simple kinds, or levels on `⊤` — is a choice about the calculus.

## 19. No head-step measure for the substitution route; the recursion is cut elimination — 2026-09-19

`conj8-measure-probe.py` records every lifting of one promotion `A ⟶ˢ B` under one operand `v`
with the lifting it is nested in, and tests candidate measures on each nested pair. Seven shards
of size-7 samples, about 13,000 nested pairs:

| measure | result |
| --- | --- |
| head steps from `B v` to a head normal form | fails |
| head steps from `A v` | fails (783 pairs) |
| the larger of the two | fails |
| size of `B v` | fails |

The failures have one shape. The operand is a variable `y` whose bound is an abstraction: the
parent `(λx≤t. x r) y` is one step from a head normal form, and the child lifts the *second*
promotion of the chain `y ⟶ˢ (λ…) ⟶ˢ t` under `r`, from a term with a redex of its own. The
points of the chain `v ≤*wf t` are unrelated, in head steps, to the term the chain is spliced into.

**What the recursion is.** `Wf-App` on `(λx≤t.u) v` is a cut between the body's derivation under
`x ≤ t` and the operand's derivation `v ≤*wf t`. Contracting it substitutes the second into the
first at each use of `x` at the head of a spine `x r`, and each such use is a new cut, of `r[v]`
against an abstraction of the chain, with formula the domain of `t`. That much descends — the
domain is a subterm of `t`. What does not is the other direction: after `t r` the formula is the
annotation of the head normal form of `body[r]`, and when the body's head is its parameter that
annotation comes from the operand `r` (`T T = λx≤T.T`). This is impredicative instantiation, and
the paper expects MPSS to encode System λ* (§6), where derivations do not normalize.

Pure type systems prove subject reduction for λ* without normalization because their application
rule is compositional: `N r` is typed from `N : Πy:S.B` as given. MPSS's well-subtyping is a chain
of machine steps between well-formed terms, so `α r ≤*wf t r` has to be produced step by step, and
producing it is normalizing the cut. If the canonical promotion line from `C[u]` does not reach
`C[t]` in finitely many steps, the instance is a counterexample; so over `WfCtx`, Conjecture 8 is
tied to whether a well-formed looping combinator exists, in both directions.

## 20. Plan: run the substitution route on a well-formed looping term — 2026-09-19

**Why.** §19: no measure is known that goes down along the nesting of the substitution route, and
the calculus does not normalize. The route has terminated on every instance tried (§15), none of
which contains a well-formed term without a normal form. Whether the nesting can go on forever
has to be tested where terms loop.

**Why this says something about the conjecture.** The way up from a term is nearly forced: reduce,
promote the head variable to its bound, or go to `⊤`. If the route from `C[u]` never reaches
`C[t]`, no other chain should — to be proved as in `MPSS/Conj8Refuted`: a class of terms that
contains `C[u]`, is closed under both reductions and omits `C[t]`, with confluence for the
backward equivalence steps.

**The term.** Hurkens' paradox ("A simplification of Girard's paradox", 1995): a term without a
normal form, typable in λU⁻ and so in λ*, about a page long. The looping combinator the paper
cites ([16]) is over 40 pages. `T T` is well-formed and normalizes; `ω ω` loops and is not
well-formed. Encoding: Hutchins' thesis p. 47 — `Πx:A.B ↦ λx≤A.B`, `* ↦ ⊤`, `M : A ↦ M ≤ A`. The
term is to be taken from Hurkens' paper, not from memory.

**Steps.**

1. Encode the paradox: a term `M` and a bound `A` with `M ≤ A`, `M` without a normal form.
2. Check `M wf`, `A wf`, `M ≤*wf A` in the empty context. The term has a few hundred nodes and
   the probe's checkers were built for size 7, so this is where it may stop.
3. Instances: `u = λx≤A. x r`, `t = λx≤A. A r`, both applied to `M` — the shape whose lifting
   splices the chain `M ≤*wf A` under `r` — and variations of `r` and of the body.
4. Run the substitution route (`conj8-subst-probe.py`) with a large budget and log the pairs.

**Expected outcomes, and what each would mean.**

| outcome | meaning | next |
| --- | --- | --- |
| step 2 fails: the encoding is not well-formed in MPSS | MPSS's well-formedness excludes the known looping terms — evidence for the conjecture, and a hint at the measure | find what the judgement rejects |
| step 2 fails: the checker cannot handle the size | nothing about the conjecture | a goal-directed checker, as in `conj8-illformed-ctx-probe.py` |
| the route terminates and the chain checks | strong evidence for the conjecture | read off what made the nesting stop |
| the nesting exceeds the budget | a candidate counterexample, not a refutation | find the repeating pattern of pairs; prove divergence as above; then `¬ Conj-8ʷᶜ` in Agda |

## 21. Hurkens' paradox is well-formed in MPSS, and it is a candidate counterexample to `Conj-8ʷᶜ` — 2026-09-19

**Superseded the same day by §22: the instance is machine-checked.** This section is kept as the
record of how it was found; its "not mechanized" list is what §22 discharges.

Not mechanized beyond `MPSS/Conj8NoAbstraction`. What is checked, by what, and what is argued
only on paper is stated item by item below.

**The term.** Transcribed from Hurkens, Section 3 (p. 269) and Section 7 (p. 277);
`refs/hurkens95tlca.pdf`. With the encoding of §20 (`Π ↦ λ`, `λ ↦ λ`, every sort `↦ ⊤`):

    ℘S = λ_≤S.⊤        ⊥ = λp≤⊤.p        ¬φ = λ_≤φ.⊥
    U  = λX≤⊤. λ_≤(λ_≤℘℘X. X). ℘℘X
    τt = λX≤⊤. λf≤(λ_≤℘℘X.X). λp≤℘X. t (λx≤U. p (f (x X f)))
    σs = s U (λt≤℘℘U. τt)
    Δ  = λy≤U. ¬(λp≤℘U. λ_≤(σy p). p (τσy))
    Ω  = the normal form of τ (λp≤℘U. λx≤U. λ_≤(σx p). p x)
    φ₀ = λp≤℘U. λ_≤(λx≤U. λ_≤(σx p). p x). p Ω
    R₀ = λp≤℘U. λ1≤(λx≤U. λ_≤(σx p). p x). 1 Ω (λx≤U. 1 (τσx))
    M₀ = λx≤U. λ2≤(σx Δ). λ3≤(λp≤℘U. λ_≤(σx p). p (τσx)). 3 Δ 2 (λp≤℘U. 3 (λy≤U. p (τσy)))
    L₀ = λ0≤φ₀. 0 Δ M₀ (λp≤℘U. 0 (λy≤U. p (τσy)))

The transcription is checked against the lengths Hurkens prints: `⊥`, `U`, `Δ`, `Ω` and the whole
term `[L₀ R₀]` have 3, 15, 241, 145 and 2039 nodes, as on p. 269; and `Ω` as he writes it out is
the β-normal form of the `τ`-term.

**The checker** (`conj8-hurkens-probe.py`). The enumerating oracles cannot take a term of this
size, so the probe has a goal-directed one that follows the source typing derivation: `Wf-App` by
promoting the head variable of the operator to its bound and contracting head redexes until an
abstraction `λx≤d.b` appears (then `Ms-Fun` over `Ms-Top`), and the operand against `d` by one
`Ws-Sub` layer — `⊤`, conversion, `Ms-Fun` under a binder with convertible annotations, or
promotion of the head variable — with every promotion between terms it has itself found
well-formed. Conversion is equality of β-normal forms (β anywhere is two `⟶ᵉ` steps,
`MPSS/Prop17Chain`), asked only of type-level terms. Mode `validate` compares it with the oracle
`wfd` of `conj8-depth-probe.py` on every locally closed term of size ≤ 5 in the 13 contexts with
`≤` entries only: 6,622 terms found well-formed by both, none by the oracle alone, and 3 by the
checker alone (`z z ⊤`, `z z y`, `z z z` in `y ≤ λ⊤.0, z ≤ y`), which the oracle also finds once
its chains may have length 9 (the default is 4). So no unsound answer among 6,625.

**Found (mode `check`), in the empty context.**

- `U`, `⊥`, `Δ`, `Ω`, `φ₀`, `R₀`, `M₀`, `L₀`, `¬φ₀`, `[L₀ R₀]` and `(¬φ₀) R₀` are well-formed.
  Outcome 1 of §20's table is excluded: MPSS's well-formedness does not reject the paradox.
- `Δ ≤ ℘U`, `Ω ≤ U`, `R₀ ≤ φ₀`, `L₀ ≤ ¬φ₀`, each by one layer.
- `(¬φ₀) R₀ ⟶ᵉ* ⊥`.
- Mode `head`: the head of `[L₀ R₀]` is an abstraction with one to three operands after each of
  40 head steps. This is Hurkens' Section 7: `[[Pₙ Mₙ] Rₙ] → [Lₙ Rₙ] → [[Qₙ Mₙ] Rₙ₊₁] → [[Pₙ₊₁ Mₙ₊₁] Rₙ₊₁]`,
  every term of the cycle an application of an abstraction.
- The first 13 head reducts of `[L₀ R₀]` are all found well-formed (by the probe; this is not
  in Agda). So this term is **not** a
  counterexample to Lemma 6 along head reduction; only to the conjecture.

**The instance.** `u = L₀`, `t = ¬φ₀ = λ0≤φ₀.⊥`, covariant context `□ R₀`, empty context. The
hypotheses of `Conj-8ʷᶜ` are the items above. Its conclusion is `[L₀ R₀] ≤*wf (¬φ₀) R₀`, that is,
the application rule of the source: the paradox is a subtype of `⊥`.

**Why the conclusion fails.** `(¬φ₀) R₀ ⟶ᵉ ⊥ = λp≤⊤.p`, an abstraction. From `[L₀ R₀]`, a
promotion at the empty configuration walks down the head: `Ms-App` pushes `R₀`, `Ms-FOp` enters
`L₀` with `0 ≡ R₀`, `Ms-App` pushes the three operands of the body, and the head is the variable
`0`, which is bound by `≡`. `Ms-Pro` reads `≤` entries only, so what is left is `Ms-Top` and
`Ms-Equ`: the term goes to `⊤` (or to `⊤` applied, which reduces to `⊤`), from where no abstraction
is reached (Theorem 11), or it takes an equivalence step. The same holds of every reduct, because
every binder on the head path of every reduct meets an operand (no weak head normal form), so
every head variable is `≡`-bound. A real promotion needs `Ms-Pro` at a `≤`-bound variable, that
is, `Ms-Fun`, that is, an abstraction on the head path with the stack empty — a weak head normal
form. So no chain of promotions from `[L₀ R₀]` ends in an abstraction. (It is not true that the term is
below its reducts and `⊤` only: `Ms-Top` under `Ms-App` and `Ms-FOp` gives
`[L₀ R₀] ⟶ˢ (λ0≤φ₀.⊤) R₀`, which is neither; it reduces to `⊤`.)

This is the phenomenon of §14 without the ill-formed annotation: there the term without a weak
head normal form was `δ δ`, made possible by `R ≡ ω ω`; here it is a well-formed closed term, made
possible by impredicativity with `⊤` in place of every sort.

**Mechanized.** `MPSS/Conj8NoAbstraction`, `refutes`: for any `f`, `q`, `A`, `B` in the empty
context, `f ≤*wf λx≤A.B`, `f q wf`, `(λx≤A.B) q wf`, `(λx≤A.B) q ⟶ᵉ*` an abstraction, and "no chain
of promotions from `f q` ends in an abstraction" together give `¬ Conj-8ʷᶜ` (Theorem 3, then
confluence from `MPSS/Strip`, as in `Conj8Refuted`). The five hypotheses are arguments; no term is
constructed in Agda.

**Mechanized later the same day.** `MPSS/PromotionNoWhnf`: part (a) of item 2 below, and with
it the contraction of the head path, so that standardization is not needed. In a context with no
`≤` entry a promotion is an equivalence step, or its result has `⊤` at the end of its head path
(and then reduces to `⊤`), or its source has an abstraction at the end of its head path with the
stack empty (and then reduces to an abstraction, by β along the path). So for a closed term,
"no `⟶ᵉ*`-reduct is an abstraction" (`NR`) is preserved by promotion and gives `NoAbs`.
`refutes-NR`: `¬ Conj-8ʷᶜ` from the four static hypotheses and `NR (f q)`. What is left of item 2
is `NR [L₀ R₀]`, a statement about equivalence reduction only.

**Not mechanized, and what each would take.**

1. The four well-formedness facts. The checker made 8,322 promotions and 118,783 well-formedness
   judgements for them; a derivation by hand is out of the question. It needs a checker written
   in Agda and proved sound (`check Γ t ≡ true → Γ ⊢ t wf`), run by the type checker on the term.
2. "No chain of promotions from `[L₀ R₀]` ends in an abstraction." Two parts: (a) a promotion
   from a closed term whose head path never empties the stack is `Ms-Top` or an equivalence
   step — an induction on the promotion, in a context with `≡` entries only, of the kind
   `MPSS/AppClass` does for its class; (b) no `⟶ᵉ*`-reduct of `[L₀ R₀]` is an abstraction, which
   is Hurkens' Section 7 together with standardization (a reduct that is an abstraction would be
   reached by head reduction). `AppClass`'s class `Bd` cannot be reused: it requires every
   abstraction body to be an application or `⊤`, and `M₀`, `R₀`, `Δ`, `Ω` have abstractions as
   bodies. A route that avoids formalizing the cycle: replace `⊥` by a variable `o ≤ ⊤` as Hurkens
   notes is possible; then (b) is subject reduction plus the fact that no abstraction has type
   `o` — but that is subject reduction for λ\*, which for MPSS is the open statement itself, so it
   would have to come from `Spartan/Preservation` through an embedding that reflects reduction.

**Why the substitution route was not run (§20, step 4).** Its first call at this instance is
`under(L₀ ⟶ˢ …, R₀)`: contract both heads and ask for a chain from `L₀`'s body at `R₀` to `⊥`, at
the root. That chain is what the argument above says does not exist, and the probe's chain search
enumerates reducts, which it cannot do at this size. The route does not get to nest.

**What this does and does not say about type safety.** `Conj-8ʷᶜ` is how the paper proves Lemma 7
(substitution preserves well-formedness) and through it Lemma 6 and Theorem 5. If the instance
stands, that proof route is closed over well-formed contexts as well. Lemma 6 and Theorem 5
themselves are not touched by it. As a heuristic only: a redex `(λx≤A.b) a` has few supertypes in MPSS to begin with
(its body is promoted under `x ≡ a`, where `x` cannot be promoted), so there is little for
preservation to lose, and the head reducts checked are well-formed. A proof of type safety would
have to go around Conjecture 8, not through it: Lemma 7 stated for the operand substituted, by a
direct argument on well-formedness derivations.

**Next.** (i) The sound checker in Agda, which discharges hypothesis group 1 and is reusable for
any large instance. (ii) Part (a) of 2, which is term-independent. (iii) Part (b). Or, in place of
(i)–(iii) for this term, a smaller well-formed closed term without a weak head normal form, if
one exists. `conj8-nowhnf-search.py` finds none: of the 1,246,341 closed terms of size ≤ 13, the
checker finds 225,125 well-formed, and every one of them reaches a weak head normal form within
400 head steps. None is known for λ\* below Hurkens' size.

## 22. Conjecture 8 is false over well-formed contexts — machine-checked, 2026-09-19

`MPSS/Conj8WfCtxRefuted`, `¬Conj-8ʷᶜ`, under `--safe`, nothing assumed. The instance is §21's, in
the empty context: `u = L₀`, `t = ¬φ₀`, covariant context `□ R₀`, with `[L₀ R₀]` Hurkens' paradox.
Everything §21 left to the probe or to paper is now in Agda.

| what | how | module |
| --- | --- | --- |
| the term | written with names and closed binder by binder, as in the probe | `HurkensTerm` |
| `L₀ ≤*wf ¬φ₀`, `[L₀ R₀] wf`, `(¬φ₀) R₀ wf` | the probe's checker as Agda functions (`wf?`, `dom?`, `sub?`, with `hred`, `whnf`, `nf`, `conv`), run by the type checker on the term (`refl`), and a proof that what it accepts is derivable | `CheckerFns`, `NormalizeSound`, `CheckerSound` |
| `(¬φ₀) R₀ ⟶ᵉ* λp≤⊤.p` | one head contraction, which is two `⟶ᵉ` steps (`β₁`, `β₂`) | `Conj8WfCtxRefuted` |
| no `⟶ᵉ*`-reduct of `[L₀ R₀]` is an abstraction | five kinds, preserved by `⟶ᵉ` at every configuration; the paradox has the kind `S`, which no abstraction has | `Kinding`, `HurkensTerm` |
| so no chain of promotions from it ends in an abstraction | a promotion in a context without `≤` entries is an equivalence step, or goes to `⊤`, or its source reduces to an abstraction | `PromotionNoWhnf` |
| so `[L₀ R₀] ≤*wf (¬φ₀) R₀` is not derivable | Theorem 3, confluence | `Conj8NoAbstraction` |

**The kinds.** Hurkens' Section 7 and standardization are not used. Hurkens remarks that `⊥` can
be replaced by a variable of type `*`; a closed term whose type is a variable has no weak head
normal form, by subject reduction — which MPSS does not have. But the argument needs only the
proof-level skeleton of the term, with every object and annotation left unexamined:

    O  anything     F = O → T     T = F → G     G = F → S     S  a finished proof

`R₀`, `M₀` and every `let p. …` have kind `F`, `L₀` has kind `G`, `[L₀ R₀]` has kind `S`. `F` occurs
in its own definition, so this is not a normalization argument. `sr`: the kinds are preserved by
`⟶ᵉ` at a configuration whose stack and `≡`-definitions are kinded as the subject's kind says
(`Me-FOp` binds the parameter to an operand of the binder's kind; `Me-Pro` unfolds a name to a
term of its kind). `S` is only ever the kind of an application.

**The checker.** Fuel-bounded, sound, not complete. `sub-sound` carries the `Ws-Sub` layer built
so far as a function, because a head step leaves a term not known to be well-formed (that is
Lemma 6, which is open), and `Ws-Lf2` wants both ends of a promotion well-formed; the checker
checks the ends it does not know. The first version of the probe did not check the source of a
promotion; it does now, and its results are unchanged. Under a binder the checker works at one
fresh name and the derivation is closed up by `wrap-wf` and `chain-fun`. The three runs on the
term take the type checker about half a minute together.

**What is and is not refuted.** Well-subtyping in MPSS is not closed under covariant contexts,
in any reading of the *logical* context the paper could intend: prevalid (§14) or with
well-formed annotations (here, and in the empty context). The covariant context used is `□ q`;
nothing is shown about the shapes `λx≤t.Co` alone, and nothing is needed. The conclusion that fails is the application rule
of the source calculus at a redex without a weak head normal form. `Lem-6ʷᶜ` and
`Preservationʷᶜ` are **not** refuted by this instance and are open; a proof of them cannot go
through Conjecture 8, and would have to establish Lemma 7 directly.

**Reusable.** `wf-sound` and `sub-sound` give derivations for any term the checker accepts, at
any size the type checker can evaluate; `Kinding.sr` applies to any term with a kinded skeleton.

**Routes considered for "no reduct is an abstraction" and not taken** (so that they are not
retried): `MPSS/AppClass`'s class `Bd` (it requires every abstraction body to be an application
or `⊤`; `M₀`, `R₀`, `Δ`, `Ω` have abstractions as bodies); Hurkens' Section 7 cycle with a
standardization theorem for `⟶ᵉ` (the cycle is only up to growing annotations, and `⟶ᵉ` unfolds
`≡`-bound parameters partially, so its steps are not β-steps); typing the term in `Spartan/` and
transferring subject reduction through an embedding that reflects reduction (it needs a second
verified type checker and a simulation for `Me-FOp`'s partial unfolding); a syntactic class
closed under parallel reduction written out shape by shape (it is the kind system of
`MPSS/Kinding`, less uniformly). One thing to know about the kinds: with `O` read as a base type
they look simply typed, which would make the skeleton normalizing; they are not, because `F`
occurs in `T = F → G` and `T` in `F = O → T`.

## 23. Lemma 6 and Theorem 5 are false over well-formed contexts — machine-checked, 2026-09-19

`MPSS/Lem6WfCtxRefuted`: `¬Lem-6ʷᶜ`, `¬Preservationʷᶜ`, nothing assumed, empty context. One more
application around the term of §22, with `H = [L₀ R₀]`:

    t₆ = (λx≤¬φ₀. x R₀ ⊤) L₀   ↦   L₀ R₀ ⊤ = H ⊤

`t₆` is well-formed (the checker of §22): under `x ≤ ¬φ₀`, `x R₀` is promoted to `(¬φ₀) R₀`, which
reduces to `⊥ = λp≤⊤.p`, so `x R₀` is below `λp≤⊤.⊤` and takes the operand `⊤`; and `L₀ ≤*wf ¬φ₀`.
This is *ex falso* in the source calculus. `H ⊤` is not well-formed: `Wf-App` wants a chain of
promotions from `H` to an abstraction, and §22 shows there is none.

So **type safety of MPSS in the paper's form is false**: progress holds (Theorem 4), preservation
of the judgements of Figure 4 does not, in any reading of the context. The reduct `H ⊤` is not
stuck — it diverges. What the counterexamples leave untouched is safety in the operational
sense: a well-formed term never evaluates to `⊤` applied to an operand. §24 is the plan for that.

## 24. Plan: operational safety by a step-indexed model — 2026-09-19

**Statement aimed at.** For `[] ⊢ t wf`: head evaluation of `t` (β at the head of the spine,
deterministic) never reaches `⊤ v₁ … vₙ` with `n ≥ 1`. The calculus and its judgements are
untouched; nothing is stratified.

**Why a model.** Every syntactic invariant tried is either not preserved (Figure 4's own
judgements, §23) or needs the statement itself (the class of reducts of well-formed terms). The
fact to be transferred across a β-step is "the operand is below the bound, and the bound is below
an abstraction, so the operand can be applied" — hereditarily, through applications. That is a
logical relation. It cannot be defined by recursion on the bound (bounds are terms, `⊤` stands
for every sort, and domains cycle: `T T` has domain `T`, §14), so it is indexed by a number that
goes down at each operand.

**The model** (closed terms; `π` a stack of closed terms; `⟶ᵉ*` at the empty configuration;
`→h` head β):

    Supp₀ t π,  Suppₖ t []                  hold
    Suppₖ₊₁ t (w ∷ π)   iff   t does not reduce to ⊤ or to ⊤ applied, and for every reduct
                              λx≤d.B of t:   w ∈ 𝒯ₖ d   and   Suppₖ (B[w]) π
    w ∈ 𝒯ₖ d            iff   for j ≤ k:  Suppⱼ d ⊆ Suppⱼ w,  and  Goodⱼ w
    Goodₖ w             iff   for j ≤ k and Suppⱼ w π:  w π is safe for j head steps

The supports of a bound quantify over *all* its `⟶ᵉ*`-reducts, so invariance under `⟶ᵉ` on either
side is confluence (`MPSS/Strip`), with no standardization. Safety is about the deterministic
`→h`, so one β-step is one index. A term with no abstraction and no `⊤` among its reducts
(Hurkens' paradox) supports every stack, which is what `H ⊤` needs.

**Fundamental lemma.** (1) `Γ ⊢ t wf` gives `Good` of `t` under a good environment. (2)
`Γ ⊢ u ≤*wf t` gives `Supp t ⊆ Supp u`; then `u ∈ 𝒯 t` follows from (1) and (2). (2) goes by
induction on machine derivations at configurations: `Ms-Pro` is goodness of the environment;
`Ms-Top` is vacuous (a `⊤` with operands supports nothing); `Ms-Equ`, `Ws-Lf1`, `Ws-Rgh` are
confluence; `Ms-App` and `Ms-FOp` are the definition, read at the spine. The environment is a
context of `≡` entries — the operand kept in the context as `Ms-FOp` keeps it (`relabelᵉ`,
`unfold`) — not a substitution, for which the development has no lemma at a `≤`-bound name
(Lemma 31 as printed is open).

**Expected obstacles.** The spine/stack bookkeeping of `Ms-App`/`Ms-FOp` against `Supp`; that
`Wf-Fun` gives the body at cofinitely many names under `x ≤ A` and the model needs it under
`x ≡ w`; `↦`/`→h` as `⟶ᵉ*` on terms that are not well-formed (`β₁`, `β₂` of
`MPSS/PromotionNoWhnf` do this).

### §24, first design pass — where the index goes wrong (2026-09-19, night)

Tested first: `conj8-safety-search.py` — of the 225,125 closed terms of size ≤ 13 the checker
finds well-formed, none reaches `⊤` in operator position within 60 leftmost-outermost β-steps.

The existing `MPSS/Morphism` (substitutions as lists, `m-e`, `up`, `inst`, `m-eqv`, `act-open…`)
and the shape of `MPSS/Fundamental`'s `STEP` (a `Link` between the machine's context with `≡`
entries and the well-formedness context with `≤` entries; `Ms-FOp` extends `θ` at the head,
`Ms-Fun` instantiates) carry over unchanged: only the goodness predicate is to be replaced, the
syntactic `G` (whose conclusion `m v ≤*wf T v` is false, §22) by the semantic `Supp`/`𝒯`.

Four placements of the index were worked through on paper; each loses one index somewhere on
the cycle `Ms-App → Ms-FOp/Ms-Fun → Ms-Pro`:

| placement | breaks at |
| --- | --- |
| `Suppₖ t (w∷π)` asks `𝒯ⱼ w d` and `Suppⱼ (B[w]) π` for `j < k` (the canonical "later") | `Supp (t c) π` and `Supp t (c∷π)` differ by one index, so `Ms-Pro` under `n` operands needs the variable good at `k+n`; a parameter instantiated from a stack at `k` is good only below `k` |
| index drops only inside `𝒯` (`𝒯ₖ₊₁ w d` = inclusion at `k`) | `Ms-Fun`: the instantiated operand has `𝒯ₖ`, `Ms-Pro` on it at `k` needs `𝒯ₖ₊₁` |
| drop at each operand, none in `𝒯` | circular (`Supp` is contravariant in `𝒯`) |
| supports by head reduction instead of all reducts | conversion invariance holds only up to one index, and both directions are needed (`Ws-Lf1`, `Ws-Rgh`) |

In the limit (`Supp∞ = ∀k. Suppₖ`) every case of `STEP` is exact; what does not pass to the
limit is `𝒯` itself, which asks inclusion *at each index* and is what `FL-sub` has to produce for
operands. Open design question: a definition of `𝒯` for which inclusion of the limits is enough,
or a bound on the loss by the size of the derivation with `𝒯` tolerant of it. Not yet resolved;
nothing of the model is in Agda.

## 25. Next steps: the least change that gives an MPSS-style calculus type safety — 2026-09-19

The user's instruction: try each repair until it ends in a proof or a refutation; the goal is
type safety (progress and preservation of the static judgement) for an MPSS-style calculus, and,
since the calculus as printed does not have it (§22, §23), the *minimum* change that does.
Stratification (kinds, levels) is excluded: it shrinks the calculus.

**Diagnosis to repair.** `Ms-FOp` binds the parameter of a consumed abstraction by `x ≡ a` and
forgets `x ≤ A`. So `(λx≤A.b) a` can be promoted only by reducing it, `a v ≤ A v` does not follow
from `a ≤ A` (Conjecture 8), and a β-step can replace a promotable `x v` by an unpromotable `a v`
(Lemma 6).

**Candidates, in order of how little they change.**

| | change | what has to be re-established | first test |
| --- | --- | --- | --- |
| A | `Ms-FOp` keeps the bound: the body is promoted under *both* `x ≡ a` and `x ≤ A`, and `Ms-Pro` may fire on such an `x`. One rule of `⟶ˢ` changes; `⟶ᵉ`, Figure 4 and `↦` do not. | the push theorem should become verbatim (the one failing case of `MPSS/Push` was `Ms-Pro` on the narrowed name), hence Conjecture 8, hence Lemmas 7, 6, Theorem 5 by `WfCtxSafety`'s argument; but Lemma 1 (commutation) meets `x ⟶ᵉ a` against `x ⟶ˢ A`, which needs `a ≤ A` — a coherence condition on configurations — and Theorem 3, Lemma 10, Theorem 11 rest on Lemma 1 | enumerate: Theorem 11 (`⊤ ≤ λ`?), Conjecture 8, Lemma 6 at small sizes, and the two Hurkens instances, under the changed rule |
| B | Conjecture 8 as a rule of well-subtyping (`Ws-Co`). `⟶ˢ`, `⟶ᵉ` unchanged; Figure 4 gains one rule. | Lemmas 7, 6, Theorem 5 by the paper's argument redone over the new judgement; Theorem 3 is lost (`H ≤ ⊥` has no machine chain), so Lemma 10 and Theorem 11, which progress needs, want a new — probably semantic — proof | enumerate Theorem 11 and Lemma 10 under the rule |
| C | v1's discipline: well-formedness that reads the operand stack (`PSS/` has type safety unconditionally) grafted onto MPSS's `≡`-contexts | what of MPSS's commutation survives | compare the two instances in `PSS/` |
| — | operational safety for the calculus unchanged (§24) | the step-indexed model | kept as the fallback statement if no change is wanted |

"Minimum" is to be argued at the end from what each candidate needed: a rule of the machine, a
rule of the static judgement, or the judgement's shape.

**Order of work.** A first (smallest, and it attacks the diagnosed cause); each candidate gets a
probe before any Agda, a new-file variant of the relation (nothing existing modified), and ends
in a module that proves type safety for it or one that refutes it.

### §25 — status: logged, not started (2026-09-19)

Nothing of candidates A, B or C has been written; no file was changed for them. To do, in order:

1. **Probe for A** (a new file beside `conj8-search.py`; nothing existing edited). A consumed
   parameter needs an entry that `⟶ᵉ` reads as `x ≡ a` and `⟶ˢ` also reads as `x ≤ A`. The probes'
   entries are triples used everywhere, so encode it as a third kind whose payload pairs the two
   terms, with `lookup_eqv` returning the operand and `lookup_sub` the bound. Tests: `⊤ ≤ λ`
   (Theorem 11), Conjecture 8, Lemma 6, transitivity elimination (Theorem 3), and the two Hurkens
   instances with the goal-directed checker taught to promote through a redex.
2. **What to expect of A**, from reading the rules, to be confirmed or refuted by the probe:
   `[L₀ R₀] ≤ ⊥` and `[L₀ R₀] ⊤ wf` become derivable, because `L₀` is an abstraction whose body is
   headed by its own parameter; the failing case of `MPSS/Push` (`Ms-Pro` on the narrowed name)
   becomes verbatim, so Conjecture 8 should be provable syntactically. The risk is Lemma 1:
   `x ⟶ᵉ a` against `x ⟶ˢ A` joins only through a *chain* `a ≤ A`, not one step, and only on
   configurations where the operand is below the bound; Theorem 3, Lemma 10 and Theorem 11 rest
   on it. Small-size search cannot show preservation failing (the known failure needs a term the
   size of Hurkens'); it can show whether A introduces a new unsoundness.
3. **Then Agda for A** as variant relations in new modules (`⟶ˢ` with the changed `Ms-FOp`, the
   judgements of Figure 4 over it), ending in type safety or a refuting module; then B; then C;
   then the argument for which change is least.

## 26. Candidate A probed: it repairs both Hurkens instances, and it is Hutchins' rule — 2026-09-19

`conj8-A-probe.py` (new; nothing existing edited): `Ms-FOp` binds the consumed parameter by an
entry that `⟶ᵉ` reads as `x ≡ a` and `⟶ˢ` reads also as `x ≤ A`.

**What A repairs (mode `hurkens`; goal-directed checker taught to promote through a redex; not
mechanized).** `[L₀ R₀] ≤ (¬φ₀) R₀` — the instance of Conjecture 8 refuted in §22 — and
`[L₀ R₀] ≤ ⊥` are derivable; `t₆` and its reduct `[L₀ R₀] ⊤` (§23) are well-formed; each of the
first 13 head reducts of `[L₀ R₀]` is well-formed, below `⊥`, and well-formed applied to `⊤`.

**What A does not disturb, as far as enumeration reaches.**

- Mode `small 4`, 125 well-formed contexts, terms of size ≤ 4: the well-formed terms are the same
  as printed (2,211); Theorem 11 over `≤*wf`, operational safety and Lemma 6 have no failure;
  Conjecture 8: 539,329 instances, 539,093 by `≤*wf` and 236 by the machine relation only, none
  failing; Theorem 3 on well-formed terms: 23,494 two-layer instances, none failing (14 needed
  chains longer than 4).
- Mode `safety 11`: the closed terms of size ≤ 11 found well-formed are the same as printed
  (14,067 at size 11); none reaches `⊤` applied. Mode `validate 7`: 93,962 terms found well-formed
  by the checker and the oracle, 305 by the checker alone, **all 305 found by the oracle once its
  chains may have length 9** (default 4) — no unsound answer. Also at `validate 7`: the changed checker accepts
  nothing the printed one rejects at that size, so **the enumeration does not exercise A**: A adds
  judgements only where a redex has no abstraction among its reducts, and no well-formed closed
  term of size ≤ 13 is like that (§21).

**What A breaks — machine-checked, `MPSS/CandidateA`.** `¬Lem-1ᴬ`, `¬Thm-3ᴬ`, `¬Thm-11ᴬ` for the
machine relation (no well-formedness): `m = (λx≤λ⊤.⊤. x) ⊤` reduces to `⊤` and promotes to
`(λx≤λ⊤.⊤. λ⊤.⊤) ⊤ ⟶ᵉ λ⊤.⊤`, so `⊤ ≤ m ≤ λ⊤.⊤` in two layers and `⊤ ≤ λ⊤.⊤` in none (`Top≰ᴬlam`
still holds). `m` is ill-formed, so this is not a counterexample to type safety of A. It closes
the paper's route to progress (Lemma 1 → Theorem 3 → Lemma 10, Theorem 11): under A those have to
be stated over `≤*wf`, where the unfolding `x ⟶ᵉ a` and the promotion `x ⟶ˢ A` join through the
chain `a ≤*wf A`.

**A is the rule the paper removed.** v2 §1 gives `(λx≤t.x) v ⟶≤ (λx≤t.t) v` as the elementary
case on which Hutchins' commutativity proof fails, and says that in MPSS this step "doesn't
exist … essentially disallowing premature promotion". Candidate A restores exactly that step. So:

- preservation under A looks within reach syntactically (the one failing case of `MPSS/Push`
  becomes verbatim; `Co[u]` well-formed follows from `Co[t]` well-formed for application
  contexts), but
- progress under A needs transitivity elimination over well-formed terms for a system with
  Hutchins' rule, which is the problem Hutchins left open (thesis §2.7) and MPSS was built to
  avoid. A is not a small change in proof terms even though it is one rule.

**v1 (`PSS/`) for comparison, read not run.** `Srs-FunOp` binds the parameter *below the
operand* (`x ≤ α`; v1 contexts have only `≤` entries) and `W-FunOp` checks the body of a consumed
abstraction under `x ≤ δ`, the operand, at the remaining stack. Under that discipline `t₆` is
not well-formed: its body `x R₀ ⊤` is checked under `x ≤ L₀`, and `L₀ R₀` reaches no abstraction.
So v1 has type safety by rejecting the term that A accepts. This is candidate C, and it answers
"minimum change" differently: A keeps ex falso in applied position and owes Hutchins'
commutation; C gives it up and has a proof already.

**Next.** (1) Candidate C made precise on MPSS's `≡`-contexts: `Wf-App`/`Wf-Fun` reading the
stack, the body of a consumed abstraction checked under `x ≡ α`; which of `PSS/`'s preservation
proof carries over. (2) B (Conjecture 8 as a rule) inherits A's problem for progress — Theorem 3
is lost the same way — and is weaker than A on preservation; probe only if C fails. (3) For A,
the restated Theorem 11: a well-formed term convertible with `⊤` is below no abstraction in
`≤*wf`.

## 27. Candidate C: type safety, machine-checked — 2026-09-19

**The change.** MPSS's machine is kept as printed: `⟶ᵉ`, `⟶ˢ`, contexts with `≡` entries, the
machine relation and everything proved about them (Lemmas 1 and 2 by the variant route, Theorem
3). Figure 4 is replaced by v1's static judgements, indexed by the operand stack
(`MPSS/StackWf`): `Wc-FOp` checks the body of an abstraction that meets an operand `δ` under
`x ≡ δ` at the remaining stack; `Wc-App` asks `u ≤*wf λt.⊤` at `v ∷ s`; a variable is well-formed
at `s` when its annotation is; well-subtyping is the machine relation between terms well-formed
at the same configuration.

**Proved, `--safe`, nothing assumed.**

| module | result |
| --- | --- |
| `StackWf` | the judgements; `Thm-3ˢ`, `Thm-11ˢ`; **progress** `Thm-4ˢ` at every configuration |
| `EvalChain` | `↦⇒⟶ᵉ*`: an evaluation step is a chain of `⟶ᵉ` steps at every configuration, from local closure and scoping alone (β is two steps) — the repaired Proposition 17 without well-formedness |
| `SubstEqvS` | `⟶ˢ` and the machine relation under substitution for a name bound by `x ≡ v`: one step to one step |
| `MachineNarrow` | `⊲-↣`: the machine relation, both modes, is preserved by context reduction, on locally closed scoped terms (from `Lem-1′`, `Lem-2′`) |
| `StackWfSubst` | the three judgements under that substitution (v1's B.5 with `≡`) |
| `StackWfNarrow` | `wfˢ-fv`; narrowing of the three judgements along reductions of annotations and stack entries that preserve well-formedness (v1's B.11, B.12, B.17, B.18) |
| `StackWfPreservation` | **`Lem-6ˢ`** (evaluation preserves `wfˢ`), **`Thm-5ˢ`** (evaluation preserves `≤*wfˢ`), **`type-safetyˢ`**, `closed-safetyˢ` |
| `StackWfExample` | `(λx≤⊤. x) ⊤` is `wfˢ` — the theorem is not vacuous |

**Why it goes through where Figure 4 does not.** The β-case substitutes for a parameter bound by
`x ≡ δ` — its own definition — so nothing of the form "`δ v` is below `A v` because `δ` is below
`A`" is asked; that was Conjecture 8. The price is that an abstraction is checked again at each
operand it meets, and well-formedness is not a judgement about a term in a context alone.

**Probe** (`conj8-C-probe.py`): to size 6 in 125 well-formed contexts, the terms `wfˢ` at the
empty stack include every term well-formed as printed; the few dozen more have the shape of the
long-chain artefacts of the printed oracle (`z z ⊤` under `z ≤ y ≤ λ⊤.0`), not checked one by
one; Lemma 6: 2,693 instances, no failure.

**C rejects `t₆` — machine-checked** (`MPSS/StackWfRejects`: `¬wfˢ-H⊤`, `¬wfˢ-t₆`). By `Lem-6ˢ`
it is enough that `[L₀ R₀] ⊤` is not `wfˢ`, i.e. that `[L₀ R₀]` is below no abstraction at the
stack `[⊤]`. `MPSS/KindingTop` extends the kinds of `MPSS/Kinding` by `⊤` at every kind, so that
kinds are preserved by promotion too (`srˢ`, in contexts without `≤` entries, at stacks that give
an arrow kind its operands — which excludes `Ms-Fun`) and not only by `⟶ᵉ` (`sr⁺`, at stacks that
may carry further operands once the kind is `S`). `S-not-below-lam`: a locally closed term of
kind `S` is below no abstraction in the machine relation, at any stack. So C gives up ex falso
in applied position.

**C accepts a term Figure 4 rejects — machine-checked** (`MPSS/StackWfAccepts`: `wfˢ-t`, `¬wf-t`):
`(λx≤⊤. x ⊤) (λy≤⊤. y)`. The body is checked under `x ≡ λy≤⊤.y`; Figure 4 checks it under
`x ≤ ⊤`, where `x` is below no abstraction. So the two judgements are **incomparable**: C types a
redex by what its body does with the actual operand (as v1 does); the declared bound is consulted
for an abstraction that meets no operand and for the operand itself.

**Agreement cannot be asked of all terms with a normal form** (`MPSS/StackWfRejectsNormalizing`):
`(λz≤⊤. ⊤) t₆` is well-formed by Figure 4, reduces to `⊤` in one step, and is not `wfˢ`, since
`Wc-App` asks the operand well-formed. Open: whether every *strongly normalizing* term that
Figure 4 accepts is `wfˢ` — equivalently, whether Figure 4's preservation can only fail through
a diverging subterm.

**Where the question stands.** Minimum change giving type safety, among the candidates of §25:

- C — Figure 4's shape (stack-indexed judgements; one rule `Wc-FOp` added, `Wf-App` read at the
  stack): **type safe, proved**; machine untouched.
- A — one rule of the machine: repairs the two counterexamples, but it is the promotion the paper
  removed, Lemma 1 and Theorem 3 fail for it (`CandidateA`), progress open (§26).
- B — not probed; loses Theorem 3 as A does.
