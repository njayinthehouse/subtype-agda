# MPSS: obligation status

Every entry below is machine-checked under `--safe`, with no postulates, no holes, and no
`TERMINATING` pragmas. Assumptions appear only as declared statement types in `MPSS/Assumed`,
taken as explicit arguments, so each result carries its dependencies in its own type.

## Proved

| # | statement | module | needs |
| --- | --- | --- | --- |
| 3 | transitivity elimination | `Transitivity` | 1, 2 |
| 4 | progress | `Progress` | 1, 2 |
| 5 | preservation | `Preservation` | 1, 2, 17ʳ, Conj 8 |
| 6 | evaluation preserves well-formedness | `Evaluation` | 1, 2, 17ʳ, Conj 8 |
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
| 27 | reduction preserves subtyping | `Preservation` | 17ʳ |
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
| 1, 2 | commutation and the diamond; unproved here, and the printed induction is not well-founded (`AUDIT`) |
| 8 | the paper's own conjecture |
| 17ʳ | repaired form; the printed one is refuted |

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
