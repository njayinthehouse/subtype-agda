# subtype-agda — MPSS in Agda

An Agda formalization of Pasquale and García-Pérez, *Modal Pure Subtype Systems* (MPSS):
[arXiv:2407.13882](https://arxiv.org/abs/2407.13882), published at CSL 2026. `PSS/` is the
underlying calculus λ⊲ (syntax, substitution, reduction); `MPSS/` is the paper's metatheory.

**Where the results are.** `MPSS/STATUS.md` lists every numbered result of the paper with its
status and module. `MPSS/DEAD-ENDS.md` catalogues the failed attempts on Lemma 2, each with the
module or script that records it. `MPSS/CONJ8.md` is the work on Conjecture 8. The `*.py` files
are the search and probe scripts; the `*.log` files and `cycle-summary-2026-09-12.md` are
their results.

**What is proved and what is assumed.** Every module is `{-# OPTIONS --safe #-}`: no postulates,
holes or termination pragmas anywhere. Statements taken as hypotheses are declared as types in
`MPSS/Assumed` and passed as module parameters, so each dependency is visible in the type.
Transitivity elimination (Theorem 3), Theorem 11, Lemma 10, Theorem 4 and confluence of the
equivalence reduction are proved with nothing assumed. Type safety (`MPSS/Unconditional`) takes
exactly two hypotheses: the paper's Conjecture 8 and the repaired Proposition 17. The paper's
Lemmas 1 and 2, also declared in `MPSS/Assumed`, are no longer hypotheses of any theorem; the
one-step diamond of Lemma 2 for the original reduction is open, and `MPSS/MixedDiamond` proves
it with one edge's promotion premises at the empty stack. Start at `MPSS/Unconditional.lagda.md`.

**Checking.** Agda 2.8.0 with `standard-library-2.3` registered in `~/.agda/libraries`; then

```
agda --safe MPSS/Unconditional.lagda.md
```

from the repository root, or any other module the same way.

References to `../PLAN.md` in the notes point to working notes kept outside this repository.
