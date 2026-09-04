# The proof ledger

`ledger.json` is this development's entry in the `proof-ledger` skill's format: every numbered
result of arXiv:2407.13882v2, its verdict, its dependencies, our proof, the paper's proof, and the
transcribed steps from `MPSS/PaperSteps`.

Rebuild the page with

    python3 ~/.claude/skills/proof-ledger/assets/build.py build MPSS/ledger.json -o ledger.html

and publish `ledger.html`. Edit `ledger.json`, never the built file — a rebuild discards it.

The build refuses to proceed on a dependency to an unknown result, a highlighted sentence that
does not occur in the extracted proof, or a result marked refuted with no invalid step named.
