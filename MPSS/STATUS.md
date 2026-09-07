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

**Lemmas 1 and 2**, and nothing else in the appendix. For Lemma 2 the case analysis is now
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
