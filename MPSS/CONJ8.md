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
| subjects of size 7 that apply their own parameter, sampled (120 per context), stacks of up to three operands, targets read off the subject's forward closure (partial: 20 contexts skipped on memory, 3 shards cut short) | 1,389,958 | 1,155,467 | no invalid step, no unresolved chain, no budget hit; 344 instances keep a promotion point the oracle cannot confirm — terms of about 20 nodes, over its size cap of 18 |

No instance failed, none ran out of budget, the pending stack reached four operands, and nesting
reached two rounds (29,408 instances).

**The order the recursion descends in.** Round `k` narrows a parameter of bound `t_k` to an
operand `v_k`. The next round happens inside `lift(v_k ≤*wf t_k, σ)`: an abstraction
`λx′≤t′.…` of that chain meets the first operand of `σ`. That abstraction is below `t_k`, and `t_k`
is applied to the same operand (`spine t_k σ` is well-formed), so `t_k ≤*wf λt″.⊤` and, by
inversion (Lemma 10), `t′ ≡wf t″`: **the bound of each round is the domain of the bound of the round
before.** The probe checks it on every nested round — 29,414 of 29,414. It is the order on which
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

Three new `--safe` modules, nothing existing touched.

| module | content |
| --- | --- |
| `MPSS/Conj8Pair` | `Lem-9ᵖ`, `Lem-7ᵖ`: Lemmas 9 and 7 for the substitution `x := α` with `α ≤*wf t` need Conjecture 8 **at the pair `(α, t)` only**, in the contexts extending the one the pair lives in (`C8At Γ α t`). The proofs are those of `MPSS/Lemma9` and `MPSS/Lemma7` with the one call replaced |
| `MPSS/FunLift0` | `FunLift₀`: `(λx≤t.u) v ≤*wf (λx≤t.u′) v` from a body promotion under `x ≤ t`, **from `C8At Γ v t`** — §7's sketch: both sides β-reduce through well-formed terms (`Prop-17ʷ`), `v ≤*wf t` by inversion (`operand≤`: Lemmas 10, 15, 16), the middle is `Lem-9ᵖ`, the two ends are well-formed by `Lem-7ᵖ` |
| `MPSS/PushWf` | `⇛-push`: §9's `push`, for the chains the conjecture is about. A promotion derivation at `Γˢ ∣ s₀`, annotated at its leaves, replays at the narrowed `Γᵉ ∣ s₀ ++ s` as `Γᵉ ∣ s₀ ++ s ⊢[ P ] a ◁* a′` (`MPSS/Frame`), the side condition `P` a parameter that becomes `App P v` under an application and `Fun P t x` under a binder. An abstraction that meets an operand narrows its parameter and goes on (`q-fun-cons`); the datum at a narrowed variable is **one chain `α ◁* t` at the stack in force under the side condition in force** — not `MPSS/Push`'s reachability at every stack, which `MPSS/ReachFails` refutes |

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
   points of a lifted chain it follows from `z ≤*wf w` and well-formedness at `w`, frame by frame:
   `app-wf-mid` at an application frame, with `z v ≤*wf w v` from 2 at lower rank at the smaller
   context; `Wf-Fun` at a binder, in the **un-narrowed** context, where 2 applies as well.
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

**Status.** Conjecture 8 is neither proved nor refuted. It is proved, on paper, for every
instance whose targets have finite domain rank, with the structural half mechanized; and any
counterexample has infinite domain rank.
