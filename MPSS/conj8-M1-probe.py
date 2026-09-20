"""(M1) of CONJ8.md §30, tested: if Γ;σ ⊢ g ≤ λd.c then Γ;σ++[a] ⊢ g ≤ λd.⊤, for every operand a.
The machine relation is the bounded one of conj8-search.py (chains of length DEPTH, cap K), so a
reported failure is a candidate: it is retried with longer chains before it is printed.

  python3 conj8-M1-probe.py MAXSIZE
"""
import sys, functools, collections
from importlib.machinery import SourceFileLoader
print = functools.partial(print, flush=True)
P = SourceFileLoader('Aprobe', '/home/egret/gimmick/1/MPSS/conj8-A-probe.py').load_module()
O = P.load_env()
S = O['S']; TOP, A, L, F, B = O['TOP'], O['A'], O['L'], O['F'], O['B']
show, showG, machine, tsize = O['show'], O['showG'], O['machine'], O['tsize']

def main(maxsize):
    anns = [TOP, L(TOP, TOP), L(TOP, B(0)), L(TOP, L(TOP, TOP)), L(L(TOP, TOP), B(0))]
    ctxs = [()] + [(('y', c, a),) for a in anns for c in ('s', 'e')]
    terms = O['gen_terms'](['y'], maxsize)
    small = [t for t in terms if tsize(t) <= 3]
    st = collections.Counter()
    for G in ctxs:
        P.clear(O)
        ts = [t for t in terms if S.fv(t) <= S.dom(G)]
        ops = [t for t in small if S.fv(t) <= S.dom(G)]
        lams = [t for t in ts if t[0] == 'l']
        for sigma in [()] + [(r,) for r in ops]:
            for g in ts:
                for tgt in lams:
                    if not machine(G, sigma, g, tgt, 3, 5): continue
                    st['hypotheses'] += 1
                    goal = L(tgt[1], TOP)
                    for a in ops:
                        s2 = sigma + (a,)
                        st['instances'] += 1
                        if machine(G, s2, g, goal, 3, 5) or machine(G, s2, g, goal, 4, 9): continue
                        st['FAIL'] += 1
                        print("FAIL:", showG(G), "| σ =", [show(x) for x in sigma], "| g =", show(g),
                              "≤", show(tgt), "| a =", show(a))
        print(f"ctx {showG(G)}: {dict(st)}")
main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
