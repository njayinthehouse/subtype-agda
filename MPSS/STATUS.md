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

## Refuted

| # | statement | module |
| --- | --- | --- |
| 17 | `u ↦ v` implies `Γ;s ⊢ u ⟶≡ v` | `BetaScope`, `BetaScopeWf` |
| 18 | reflexivity, as printed | `ReflFails` |
| — | `⟶≡` preserves well-formedness | `EqvWf` |
| — | promotion is stack-monotone | `Diff` |
| — | a stack typing obligation suffices for the `Ms-Fun`/`Ms-FOp` replay | `StackObligation` |
| — | the `Reach` obligation, at arbitrary stacks | `ReachFails` |

Only the first two rows are claims of the paper's. The last three are facts about MPSS, about a
proposed repair, and about this development's own reduction of Conjecture 8; `AUDIT.md` says which
is which, since only a refuted *paper* claim calls for a diagnosis and an assumed repair.

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

**Lemmas 1 and 2**, and nothing else in the appendix. Every other numbered result the two type
safety theorems depend on is proved above, and Conjecture 8 is the paper's own. They are the paper's main theorem. `AUDIT.md` records why the printed induction
carries no well-founded measure and why four families of candidate measures fail, with the
obstruction isolated: `Me-Pro` needs a variable lookup to cost strictly more than its annotation,
while `Me-FOp` needs a stack entry to cost at least as much as the variable it becomes.
