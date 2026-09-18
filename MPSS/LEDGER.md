# The proof ledger

Derived from the sources, not hand-written. Paths are relative to `1/`; the tools live in
`../skills/proof-ledger/`, which is symlinked into `~/.claude/skills/` so Claude Code finds it
from any project.

    python3 ../skills/proof-ledger/assets/derive.py \
        --paper PSS/pasquale-garciaperez-2407.13882v2.txt --agda MPSS \
        --map MPSS/ledger-map.json --title "MPSS Proof Ledger" -o MPSS/ledger.json

    python3 ../skills/proof-ledger/assets/build.py build MPSS/ledger.json \
        --annotations MPSS/ledger-annotations.json -o ledger.html

`ledger.json` is derived and disposable — re-run `derive.py` after any change to the development
and it refreshes. `ledger-map.json` names the definitions whose names do not follow the convention.
Its `development` list names the lemmas
the paper does not have — 1a, 2a, 8a, 8b, 8c — which are nodes of their own rather than steps in
the log of the result they support.
`ledger-annotations.json` holds everything that is a judgement rather than a fact: the short names,
the prose accounts, the fault sentences, the transcribed steps, and the one pinned verdict
(Lemma 1, which has a proof but rests on the diamond).

The build refuses to proceed on a dependency to an unknown result, a highlighted sentence that
does not occur in the extracted proof, a result marked refuted with no invalid step named, a
result with no short name, or a log that says `proved` twice with no `invalidated` step between
(a log is the history of one statement).
