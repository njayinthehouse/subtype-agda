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
