"""Operational safety, tested (CONJ8.md §24): does a well-formed closed term ever evaluate to ⊤
applied to an operand?

Every closed term up to MAXSIZE that the checker of conj8-hurkens-probe.py finds well-formed is
reduced (a) by head β and (b) by leftmost-outermost β everywhere, FUEL steps each; a term with
⊤ in operator position anywhere along (b), or at the head along (a), is reported.

  python3 conj8-safety-search.py MAXSIZE [FUEL default 60]
"""
import sys, functools
from importlib.machinery import SourceFileLoader
print = functools.partial(print, flush=True)
H = SourceFileLoader('h', '/home/egret/gimmick/1/MPSS/conj8-hurkens-probe.py').load_module()
S = SourceFileLoader('s', '/home/egret/gimmick/1/MPSS/conj8-nowhnf-search.py'.replace('.py','.py')).load_module() if False else None
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

def bad(t):
    st = [t]
    while st:
        t = st.pop()
        if t[0] == 'a':
            if t[1] == TOP: return True
            st.append(t[1]); st.append(t[2])
        elif t[0] == 'l': st.append(t[1]); st.append(t[2])
    return False

def lo_step(t):
    """leftmost-outermost β step, or None"""
    c = t[0]
    if c == 'a':
        if t[1][0] == 'l': return H.openRec(0, t[2], t[1][2])
        r = lo_step(t[1])
        if r is not None: return ('a', r, t[2])
        r = lo_step(t[2])
        if r is not None: return ('a', t[1], r)
    elif c == 'l':
        r = lo_step(t[1])
        if r is not None: return ('l', r, t[2])
        r = lo_step(t[2])
        if r is not None: return ('l', t[1], r)
    return None

def main():
    maxsize = int(sys.argv[1]); fuel = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    for sz in range(1, maxsize + 1, 2):
        n = wf = unsafe = 0
        ck = H.Checker(head_fuel=400)
        for t in terms(sz, 0):
            n += 1
            try:
                if not ck.wf((), t): continue
            except (H.Fuel, RecursionError, MemoryError): continue
            wf += 1
            w = t
            for _ in range(fuel):
                if bad(w): unsafe += 1; print("  UNSAFE:", H.show(t), "⟶*", H.show(w)[:200]); break
                r = lo_step(w)
                if r is None or H.tsize(r) > 3000: break
                w = r
            if len(ck.wfmemo) > 2000000: ck = H.Checker(head_fuel=400)
        print(f"size {sz}: {n} closed terms, {wf} found well-formed, {unsafe} reach ⊤ in operator position")
main()
