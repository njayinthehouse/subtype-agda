"""Is there a small well-formed closed term without a weak head normal form? (CONJ8.md §21)

Every closed locally closed term up to MAXSIZE, in the empty context: those the goal-directed
checker of conj8-hurkens-probe.py finds well-formed are head-reduced (β at the head, ⊤ u ⟶ ⊤)
with fuel; a term whose head is still a redex when the fuel runs out is reported. The checker
is sound on everything it was compared on and not complete, so a silent run says that no term
*it accepts* loops, which is what a counterexample to Conj-8ʷᶜ built this way needs.

  python3 conj8-nowhnf-search.py MAXSIZE [FUEL default 400]
"""
import sys, functools
from importlib.machinery import SourceFileLoader
print = functools.partial(print, flush=True)
H = SourceFileLoader('h', '/home/egret/gimmick/1/MPSS/conj8-hurkens-probe.py').load_module()
TOP, B, L = H.TOP, H.B, H.L

@functools.lru_cache(maxsize=None)
def terms(size, k):
    if size <= 0: return ()
    if size == 1: return (TOP,) + tuple(B(i) for i in range(k))
    out = []
    for a in range(1, size - 1):
        for u in terms(a, k):
            for v in terms(size - 1 - a, k): out.append(('a', u, v))
        for w in terms(a, k):
            for b in terms(size - 1 - a, k + 1): out.append(L(w, b))
    return tuple(out)

def main():
    maxsize = int(sys.argv[1]); fuel = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    for sz in range(1, maxsize + 1):
        n = wf = loops = 0
        ck = H.Checker(head_fuel=fuel)
        for t in terms(sz, 0):
            n += 1
            try:
                if not ck.wf((), t): continue
            except (H.Fuel, RecursionError, MemoryError):
                print("  checker gave up on", H.show(t)); continue
            wf += 1
            w = t
            for _ in range(fuel):
                r = H.head_step(w)
                if r is None: break
                w = r
                if H.tsize(w) > 5000: break
            else:
                loops += 1; print("  NO WHNF within fuel:", H.show(t))
            if len(ck.wfmemo) > 2000000: ck = H.Checker(head_fuel=fuel)
        print(f"size {sz}: {n} closed terms, {wf} found well-formed, {loops} without whnf within {fuel} head steps")

main()
