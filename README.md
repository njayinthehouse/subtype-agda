# subtype-agda — MPSS in Agda

`MPSS/` is an Agda formalization of the metatheory of

> Valentin Pasquale and Álvaro García-Pérez, *Towards the Type Safety of Pure Subtype Systems*.
> CSL 2026, LIPIcs vol. 363, article 37, pp. 37:1–37:16, published 18 February 2026,
> DOI 10.4230/LIPIcs.CSL.2026.37. Full version with the appendix of proofs: arXiv:2407.13882v2
> (13 December 2025).

The paper introduces **MPSS** (Machine-Based Pure Subtype Systems). The CSL version and arXiv v2
state the calculus and results 1–8 identically; the results numbered 9–36, including
Propositions 17 and 18, appear only in v2's appendix. `PSS/` formalizes arXiv v1 (18 July 2024,
*Pure Subtype Systems Are Type-Safe*), which is a different system, λ⊲.

Every module is `{-# OPTIONS --safe #-}` (Agda 2.8.0, `standard-library` via
`subtype.agda-lib`); there are no postulates, holes or termination pragmas. A statement taken as a
hypothesis is declared as a type in `MPSS/Assumed` and passed as an explicit argument, so each
theorem's type lists what it depends on. To check the main result, run
`agda MPSS/Preservation17.lagda.md` from the repository root.

Detailed records: `MPSS/STATUS.md` (every numbered result and its module), `MPSS/AUDIT.md` (each
defect in the paper, with the paper's text quoted), `MPSS/DEAD-ENDS.md` (failed attempts, kept as
Agda), `MPSS/CONJ8.md` (Conjecture 8).

**[The proof ledger](https://njayinthehouse.github.io/subtype-agda/)** shows every numbered result
of the paper as a dependency graph coloured by verdict, with each result's history and the
paper's own proof. It is built with [proof-ledger](https://github.com/njayinthehouse/proof-ledger)
from `MPSS/ledger.json` and `MPSS/ledger-annotations.json`; `MPSS/LEDGER.md` says how those are
derived.

**Continuous integration.** On every push, [a workflow](.github/workflows/ledger.yml)
typechecks every module under Agda 2.8.0 and standard-library 2.3, then builds the ledger and
deploys it to GitHub Pages. The ledger is published only from a tree that typechecks.

---

## Results

### The paper's main theorems

| result | statement | status | where |
| --- | --- | --- | --- |
| Theorem 3 (transitivity elimination) | `Γ;s ⊢ u ≤* v` implies `Γ;s ⊢ u ≤ v` | proved, nothing assumed | `MPSS/VariantTransfer` (`Thm-3ᴸ`) |
| Theorem 4 (progress) | if `Γ ⊢ t wf`, then `t` is a normal form or `t ↦ t′` for some `t′` | proved, nothing assumed | `MPSS/Unconditional` (`Thm-4′`) |
| Lemma 6 | if `Γ ⊢ t wf` and `t ↦ t′`, then `Γ ⊢ t′ wf` | proved from Conjecture 8 | `MPSS/Preservation17` (`Lem-6ʷ`) |
| Theorem 5 (preservation) | if `Γ ⊢ t ≤*wf u` and `t ↦ t′`, then `Γ ⊢ t′ ≤*wf u` | proved from Conjecture 8 | `MPSS/Preservation17` (`Thm-5ʷ`) |
| type safety | Theorems 4 and 5 together | proved from Conjecture 8 | `MPSS/Preservation17` (`type-safety`) |

`type-safety` has type `Conj-8 → (progress × preservation)`, and nothing else is in scope for it.
This is also checked from outside the module: a separate module whose declared type is exactly
that typechecks against it.

> **Conjecture 8 (well-subtyping is context independent).** If `Γ ⊢ u ≤*wf t`, and `Co[u]` and
> `Co[t]` are well-formed in `Γ` for a covariant context `Co ::= □ | λx≤t.Co | Co t`, then
> `Γ ⊢ Co[u] ≤*wf Co[t]`.

**Conjecture 8 is false as stated** (`MPSS/Conj8Refuted`, 2026-09-18: `¬ Conj-8`, and with it
`¬ Lem-6`, `¬ Lem-7₀`, `¬ Preservation`). The paper's contexts are only prevalid — an annotation
is scoped, not well-formed — so `Γ₀ = R ≡ ω ω` with `ω = λs≤⊤. λx≤(s s). (s s)` is a context, in it
`R ≡ λx≤R.R`, and for `δ = λx≤R. x x`, `t′ = λx≤R. R x`, context `□ δ`, every hypothesis holds
and `δ δ ≤*wf t′ δ` does not. So the conditional results above are proved from a false
hypothesis, and as the paper states them Lemma 6 and Theorem 5 are false.

**It is also false over contexts whose annotations are well-formed**, in the empty context
(`MPSS/Conj8WfCtxRefuted`, 2026-09-19: `¬ Conj-8ʷᶜ`, nothing assumed). The instance is Hurkens'
paradox `[L₀ R₀]`, encoded with `Π ↦ λ` and every sort `↦ ⊤`: `u = L₀`, `t = ¬φ₀`, context `□ R₀`.
The conclusion would be the application rule of the source calculus, `[L₀ R₀] ≤ ⊥`, with `⊥` an
abstraction. What is proved: no `⟶ᵉ*`-reduct of `[L₀ R₀]` is an abstraction, and therefore no
chain of promotions from it ends in one — a promotion in a context without `≤` entries is an
equivalence step, or puts `⊤` at the end of the head path (as in `[L₀ R₀] ⟶ˢ (λ0≤φ₀.⊤) R₀`), or
starts from a term that reduces to an abstraction. The well-formedness facts are runs of a checker written in Agda and proved sound
(`MPSS/CheckerFns`, `MPSS/CheckerSound`); that no reduct is an abstraction is subject reduction for
a five-kind system on the proof-level skeleton (`MPSS/Kinding`).

**Lemma 6 and Theorem 5 are false over such contexts as well** (`MPSS/Lem6WfCtxRefuted`,
2026-09-19: `¬ Lem-6ʷᶜ`, `¬ Preservationʷᶜ`, nothing assumed, empty context). With `H = [L₀ R₀]`,
the well-formed `(λx≤¬φ₀. x R₀ ⊤) L₀` — *ex falso* in the source calculus — takes a β-step to
`H ⊤`, which is not well-formed, because no chain of promotions takes `H` to an abstraction.
So type safety of MPSS in the paper's form (progress and preservation of Figure 4's judgements)
is false. `H ⊤` is not stuck, it diverges: operational safety is not refuted. See "Open" below.

### A type-safe variant: v1's well-formedness over MPSS's machine (2026-09-19)

The least change found that gives type safety keeps the machine — `⟶ᵉ`, `⟶ˢ`, contexts with `≡`
entries, and everything proved about them — and replaces Figure 4 by v1's static judgements,
indexed by the operand stack (`MPSS/StackWf`): the body of an abstraction that meets an operand
`δ` is checked under `x ≡ δ`. For these judgements, with nothing assumed:

| result | module |
| --- | --- |
| progress at every configuration (`Thm-4ˢ`), no abstraction above `⊤` (`Thm-11ˢ`) | `MPSS/StackWf` |
| an evaluation step is a chain of `⟶ᵉ` steps at every configuration, without well-formedness | `MPSS/EvalChain` |
| `⟶ˢ` and the machine relation under substitution for a name bound by `≡` | `MPSS/SubstEqvS` |
| the machine relation is preserved by context reduction | `MPSS/MachineNarrow` |
| the judgements under that substitution, and under narrowing | `MPSS/StackWfSubst`, `MPSS/StackWfNarrow` |
| **evaluation preserves well-formedness and well-subtyping; type safety** (`Lem-6ˢ`, `Thm-5ˢ`, `type-safetyˢ`) | `MPSS/StackWfPreservation` |
| the judgement rejects `(λx≤¬φ₀. x R₀ ⊤) L₀`, which Figure 4 accepts | `MPSS/StackWfRejects`, `MPSS/KindingTop` |
| it accepts `(λx≤⊤. x ⊤)(λy≤⊤. y)`, which Figure 4 rejects | `MPSS/StackWfAccepts` |

So the two judgements are incomparable. The variant types a redex by what its body does with the
actual operand; it gives up checking an abstraction once against its declared bound, and with it
*ex falso* in applied position. `MPSS/CONJ8.md` §27.

The other change tried, keeping the bound `x ≤ A` beside `x ≡ a` in `Ms-FOp`, repairs both
counterexamples in a probe (`MPSS/conj8-A-probe.py`) but is the promotion
`(λx≤t.x) v ⟶≤ (λx≤t.t) v` that the paper removed from Hutchins' system: Lemma 1, Theorem 3 and
Theorem 11 fail for its machine relation (`MPSS/CandidateA`), so its progress is open.
`MPSS/CONJ8.md` §26.

### The other numbered results

Proved, with nothing assumed unless stated:

| result | statement | module |
| --- | --- | --- |
| 7 | substitution preserves well-formedness (from Conjecture 8) | `Lemma7` |
| 9 | promotion under substitution, as well-subtyping (from Conjecture 8) | `Lemma9` |
| 10 | inversion: `Γ ⊢ λx≤t.u ≤*wf λx≤t′.u′` implies `Γ ⊢ t ≡wf t′` | `Unconditional` (`Lem-10`) |
| 11 | no abstraction is a supertype of `Top` | `TopLemma` (one step), `Unconditional` (`Thm-11wf`, over `≤*wf`) |
| 12–16 | well-formedness extraction; from well-subtyping to subtyping; from well-equivalence to equivalence; symmetry; equivalence to subtyping | `Static`, `Inversion` |
| 17ʷ | repaired Proposition 17 (see "Changes") | `Prop17Chain` |
| 18ʳ | repaired Proposition 18 (see "Changes") | `StackPush` |
| 19–22 | weakening | `Weakening` |
| 23 | narrowing preserves well-formedness | `Lemma23` |
| 24 | narrowing a promotion, all three conclusions | `Narrowing24`, `Narrow24`, `CoNarrow`, `CoPromote` |
| 25, 26 | narrowing in equivalence reduction; narrowing prevalidity | `Narrowing` |
| 27 | reduction preserves subtyping (via 17ʷ) | `Preservation17` (`Prop-27ʷ`) |
| 28 | substitution preserves prevalidity | `Subst28` |
| 29, 30 | promotion under substitution | `Lemma2930` |
| 31 | reduction under substitution, for a name the context does not bind (see "Changes") | `Subst` |
| 32 | reduction under substitution for a `≡`-bound name, as printed | `SubstEqv` |
| 33–35 | congruence | `Congruence` |
| 36 | context weakening | `Narrowing` |

### Claims of the paper that are false

| claim | counterexample | module |
| --- | --- | --- |
| **Proposition 17**: `u ↦ v` implies `Γ;s ⊢ u ⟶≡ v` for every extended context | `T = λz≤Top.Top`, `Γ = y ≤ λq≤T.Top`: the well-formed redex `(λx≤T. y x) T` steps to `y T`, but has no `⟶≡` step to it | `BetaScope`, `BetaScopeWf`; `Prop17Refuted` refutes the repair `Assumed` used to carry |
| **Proposition 18**: `Γ;s ⊢ u ⟶≡ u` and `Γ;s ⊢ u ⟶≤ u` for every `Γ;s` and `u` | `y y` in the empty context has no `⟶≡` step at all | `ReflFails` |
| **Lemma 2, second conjunct** ("Moreover"): a variable not promoted (by `Me-Pro`) on one edge is not promoted on the other side's join | `Γ₀ = y ≡ Top, x′ ≡ y`, subject `x′` | `Moreover` |
| **a step in Lemma 2's proof**, `Me-App`/`Me-Bet` case: a join that promotes nothing holds without the binding | `(x ≡ Top); nil ⊢ (λ⊤.0) x ⟶≡ (λ⊤.0) x` | `Strengthen` |

Proofs that do not establish their (true) conclusion, all recorded in `MPSS/AUDIT.md`:
- Lemma 2's induction applies its hypothesis to a derivation that is not a subderivation.
- Lemma 24's argument for its third conclusion would prove every term well-formed.
- Theorem 5's last step uses Proposition 17 without citing it.
- Proposition 27 cites `Ws-Lf1` where `Ws-Rgh` is meant.
- Lemma 9 cites a rule `Ws-Lft` that does not exist.
- Lemma 33's proof swaps which side of `≤` promotes.
- Lemma 7 cites Lemma 28 for a substitution Lemma 28 does not cover.

### Open

- **Progress for the calculus with `Ms-FOp` keeping the bound** (`MPSS/CONJ8.md` §26): over
  well-formed terms, that nothing convertible with `⊤` is below an abstraction. It would give a
  type-safe variant that still checks an abstraction once against its bound.
- **How far the stack-reading judgement and Figure 4 agree**: whether every term Figure 4 accepts
  and that has a normal form is accepted (no disagreement of that kind up to size 6).
- **Operational safety**: a well-formed closed term never head-evaluates to `⊤` applied to an
  operand. Preservation of well-formedness being false (above), this is the form of type safety
  left to prove for the calculus as it stands. Plan: a step-indexed model of bounds as sets of
  supported operand stacks (`MPSS/CONJ8.md` §24). Recorded on the way to the refutations, each
  with where it breaks (`MPSS/CONJ8.md`): the nesting-depth measure, the narrowing route, the
  domain-rank induction, the reducibility argument over ranked targets, head-step and size
  measures for the substitution route.
- **Lemma 1** (`⟶≤` and `⟶≡` strongly commute) and **Lemma 2** (`⟶≡` has the diamond property),
  for the paper's relations. Nothing depends on them any more (see "Changes", part C). Proved
  about the original `⟶≡`: the diamond against one variant step (`MixedDiamond`), the strip
  property, and confluence of `⟶≡*` (`Strip`). No counterexample in 630 million checked joins
  at small bounds.
- **Lemma 31 as printed**, with the name bound by `≤`. It is used by nothing in the development.

### Facts about MPSS the paper does not state

- `⟶≡` is infinitely branching: `Ω = (λ⊤. x x)(λ⊤. x x)` has infinitely many one-step reducts
  (`InfiniteBranching`). So no complete development (Takahashi's method) exists.
- `⟶≡` does not preserve well-formedness: with `x ≡ Top Top`, `x` is well-formed and reduces to
  `Top Top`, which is not (`EqvWf`).
- Promotion is not preserved by pushing onto the stack (`Diff`).
- No measure on configurations meets the constraints of Lemma 2's case analysis (`NoMeasure`).

---

## Changes from the paper, and why

### A. The calculus: how it is written down

The rules are not changed. Every rule of Figure 1 (prevalidity), Figure 2 (equivalence and
subtyping reduction), Figure 4 (well-formedness and well-subtyping) and the operational
semantics is transcribed one to one. In particular `Me-Bet` is kept with its unbound body
premise, which is the cause of Proposition 17's failure. The files defining the calculus
(`MPSS/Context`, `Reduction`, `Subtyping`, `WellFormed`, `CtxReduction`) have not changed since
they were first transcribed. Repairs live in new modules and new relations, and every final
theorem is stated over the original relations.

What differs is the encoding:

1. **Binding.** Locally nameless syntax with cofinite quantification, where the paper uses named
   binders with a variable convention. A premise about the body `u` with `x` free becomes a
   premise about `u ^ fvar x` for every `x` outside a finite set. This is the standard way to
   mechanize named binders.
2. **Local closure premises.** `Pv-Ctx`, `Pv-EqA` and `Pv-Sta` require the annotation or stack
   entry to be locally closed, and so does the β-rule of `↦`. Raw locally nameless syntax admits
   dangling indices, which the paper's named terms cannot contain. For v1 this deviation is proved
   to change nothing (`PSS/Faithfulness`, Deviation 3); for MPSS the same argument applies, but it
   is not separately mechanized.
3. **Lookup.** The paper reads `x ≤ t ∈ Γ` as "the rightmost annotation for `x`". Here it is plain
   membership. Prevalidity forbids binding a name twice, so the two coincide.
4. **The metavariable `◁`**, standing for either `≤` or `≡`, is an index `Mode` (`sub-m` or
   `eqv-m`). The rules that mention `◁` become one rule per instance (`PSS/Faithfulness`,
   Deviation 1).
5. **Context reduction has a reflexive base rule `Ct-Refl`.** The printed figure has only `Ct-Ann`
   and `Ct-Stk`, so read as an inductive definition the relation `↣` is empty. The appendix uses
   `Γ;s ↣ Γ;s`, obtaining it "by reflexivity of `⟶≡` (Proposition 18)". `↣` occurs in Lemmas 1
   and 2 and nowhere in the type-safety statements.
6. **Normal forms** require the annotation of an abstraction to be normal too. The paper's
   definition says "functions that have a subtype annotation and a body in normal form". Since
   `λx≤C.t` is an evaluation context, an abstraction whose annotation can step is not normal. The
   stricter definition makes progress a stronger statement, not a weaker one.

`Ws-Lf2`'s well-formedness premises on `v` and `v′` are not an addition: they are in the printed
Figure 4.

### B. Statements that differ from the printed ones

| result | printed | here | why |
| --- | --- | --- | --- |
| Proposition 17 | `u ↦ v` ⇒ `Γ;s ⊢ u ⟶≡ v`, every `Γ;s` | `Prop-17ʷ`: if `u`, `v` are well-formed and `u ↦ v`, then `Γ;nil ⊢ u ⟶≡ … ⟶≡ v` through well-formed terms | The printed statement is false. The chain form is what Lemma 6, Proposition 27 and Theorem 5 need. The β case takes two steps: `Me-App` over `Me-FOp`, which binds the parameter to the operand and unfolds it, then `Me-Bet` on a body that no longer mentions it. The other repair, binding the parameter in `Me-Bet`'s premise, would change `⟶≡` and so the relation of Lemmas 1 and 2. |
| Proposition 18 | reflexivity for every `Γ;s` and `u` | `⟶ᵉ-refl`, `⟶ˢ-refl`: for `Γ;s` prevalid, `u` locally closed, `fv u ⊆ dom Γ` | The printed statement is false (`y y` above). The scoping premise is exactly what `Pv-Sta` asks of an operand pushed by `Me-App`. |
| Lemma 2, second conjunct | a variable not promoted on one edge is not promoted on the other side's join | replaced, in `DiamondStep`: for a set `B` of names closed under the context's annotations, if one edge and its context reduction avoid `B`, the other side's join is derivable with `B` removed from the context | The printed conjunct is false (`Moreover`). The replacement is what the `Me-App`/`Me-Bet` case needs, and it survives the recursion. |
| Theorem 3 | over `≤*` | over transitive chains that record local closure of each term joined (`⊲*ᴸ`); also `Thm-3wf` on well-formed chains | Raw chains can pass through non-terms, since `Me-TAp` fires on `Top u` for any `u`. Named terms are locally closed by construction. |
| Theorem 11 | over `≤*` | the one-step form `Top≰lam` outright; over `≤*wf` as `Thm-11wf` | The `≤*wf` form is what Theorem 4 uses. The `≤*` form follows from Theorem 3 for raw chains. |
| Lemma 24 | join by `⟶≤` | join by `⟶≡` | Stronger than printed; the third conclusion then follows from the covariant-context construction (part C). |
| Lemma 31 | substitution for a `≤`-bound name | substitution for a name the context does not bind | The β-rule's body premise binds no name, so this is the form the proofs use. Lemma 32, the `≡`-bound form, is proved as printed. |
| Lemmas 7, 9 | over `Γ, x≤t, Γ′` | over a context split `Δ ++ x≤t ∷ Γ`, with local closure and scoping premises on the substituted term | Encoding: the premises hold for named terms and follow from the well-subtyping hypothesis. |
| Conjecture 8 | as stated above | the same, plus `u` and `t` locally closed; no requirement that the terms inside `Co` be locally closed | The added premises follow from the others. Inside `λx≤t.Co`, an inner `Co t` may mention `x`, which is a dangling index here, so requiring local closure inside `Co` would assume less than the paper conjectures. Lemma 9 needs the general form. |

### C. Proofs that take a different route

- **Theorem 3, Lemma 10, Theorem 4**, without Lemmas 1 and 2 as printed. The printed induction
  for Lemma 2 applies its hypothesis to a derivation built from the context reduction, which is
  a subderivation of neither edge, and `NoMeasure` shows no measure on configurations rescues it.
  The development instead defines an auxiliary relation `⟶ᵉ′` (`EmptyStackPro`): `⟶≡` with
  `Me-Pro`'s premise taken at the empty stack. Alongside it, `⟶ˢ′` (`VariantSub`) and `↣′`
  (`VariantCtx`) use `⟶ᵉ′` in place of `⟶≡`. The calculus itself is untouched.
  - Diamond (`Lem-2′`, `VariantDiamond`) and commutation (`Lem-1′`, `VariantCommutation`) are
    proved for the auxiliary relations, and transitivity elimination for them follows
    (`VariantTransitivity`).
  - On locally closed terms, every `⟶ᵉ′` step is a `⟶≡` step (`EmptyStackPro`), and every `⟶≡`
    step is a chain of `⟶ᵉ′` steps (`Peel`). So both generate the same subtyping relation `≤`
    (`VariantMachine`: `⊲′⊆⊲`, `⊲⊆⊲′`).
  - Theorem 3 for the paper's `≤` follows (`VariantTransfer`), and Lemma 10 and Theorem 4 through
    it (`Unconditional`).
- **Lemma 6, Proposition 27, Theorem 5**, through the chain form of Proposition 17 in place of
  the printed proposition (`Preservation17`).
- **Lemma 24's third conclusion** (the narrowed target is well-formed), by induction on the
  covariant context rather than on the structure of the target (`CoNarrow`, `CoPromote`).
- **Lemma 2's case analysis** is completed against the diamond as a hypothesis, under the
  invariant of part B (`DiamondStep`). The `Me-Bet` side is reopened with Lemma 32.

Modules kept in place but superseded:
- `Unconditional` and `Preservation`, whose Lemma 6, Proposition 27, Theorem 5 and type safety
  take the refuted `Prop-17ʳ`;
- `Evaluation` and `TypeSafety`, which take Lemmas 1 and 2 and `Prop-17ʳ`;
- `Inversion` and `Progress`, which take Lemmas 1 and 2.

