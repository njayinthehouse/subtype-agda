"""Candidate C of CONJ8.md §25: v1's well-formedness, which reads the operand stack, over MPSS's
machine (⟶ᵉ, ⟶ˢ and contexts with ≡ entries unchanged; only Figure 4 is replaced).

    Γ;s ⊢ x wf          if  x ≤ t ∈ Γ or x ≡ t ∈ Γ,  and  Γ;s ⊢ t wf          (v1 W-Var)
    Γ;s ⊢ ⊤ wf
    Γ;[] ⊢ λx≤t.u wf    if  Γ;[] ⊢ t wf  and  x≤t,Γ;[] ⊢ u wf                  (v1 W-Fun)
    Γ;δ∷s ⊢ λx≤t.u wf   if  Γ;[] ⊢ t wf  and  x≡δ,Γ;s ⊢ u wf                   (v1 W-FunOp, with ≡)
    Γ;s ⊢ u v wf        if  Γ;v∷s ⊢ u ≤*wf λt.⊤  and  Γ;[] ⊢ v ≤*wf t          (v1 W-App)
    Γ;s ⊢ u ≤wf t       if  both well-formed at Γ;s and Γ;s ⊢ u ≤ t (the machine relation)

≤*wf is the transitive closure through well-formed middles; by Theorem 3 of MPSS (proved for the
machine relation) it is tested as one layer between well-formed ends.

  python3 conj8-C-probe.py MAXSIZE      per well-formed context: the terms well-formed as printed
                                        and under C, Lemma 6 under C, operational safety
  contexts sharded by the environment: C_SHARD, C_NSHARDS

Bounded (machine chains of length DEPTH, promotion cap K): a failure is a candidate.
"""
import sys, os, functools, collections
sys.path.insert(0, '/home/egret/gimmick/1/MPSS')
from importlib.machinery import SourceFileLoader
print = functools.partial(print, flush=True)
P = SourceFileLoader('Aprobe', '/home/egret/gimmick/1/MPSS/conj8-A-probe.py').load_module()
K, DEPTH = 3, int(os.environ.get('C_DEPTH', 6))

def main(maxsize):
    O = P.load_env()
    S = O['S']; show, showG = O['show'], O['showG']
    TOP, A, L, F, B = O['TOP'], O['A'], O['L'], O['F'], O['B']
    openRec, closeRec, tsize = O['openRec'], O['closeRec'], O['tsize']
    machine, closure, sreds = O['machine'], O['closure'], O['sreds']
    memo = {}
    def lookup(G, x):
        for (y, c, t) in G:
            if y == x: return t
        return None
    def wfC(G, s, t):
        key = (G, s, t)
        if key in memo: return memo[key]
        memo[key] = False
        res = False
        if S.prevalid(G, s) and S.lc(t) and S.fv(t) <= S.dom(G):
            c = t[0]
            if c == 'T': res = True
            elif c == 'f':
                b = lookup(G, t[1])
                res = b is not None and wfC(G, s, b)
            elif c == 'l':
                w, b = t[1], t[2]
                if wfC(G, (), w):
                    if not s:
                        x = S.fresh(G, t)
                        res = wfC(((x, 's', w),) + G, (), openRec(0, ('f', x), b))
                    else:
                        x = S.fresh(G, t, s)
                        res = wfC(((x, 'e', s[0]),) + G, s[1:], openRec(0, ('f', x), b))
            else:
                u, v = t[1], t[2]; s2 = (v,) + s
                if wfC(G, s2, u) and wfC(G, (), v):
                    doms = {a[1] for a in closure(sreds, G, s2, u, K, DEPTH) if a[0] == 'l'}
                    for d in doms:
                        if wfC(G, (), d) and subC(G, s2, u, L(d, TOP)) and subC(G, (), v, d): res = True; break
        memo[key] = res
        return res
    def subC(G, s, u, t):
        return wfC(G, s, u) and wfC(G, s, t) and machine(G, s, u, t, K, DEPTH)

    anns = [TOP, L(TOP, TOP), L(TOP, B(0)), L(TOP, L(TOP, TOP)), L(L(TOP, TOP), B(0)), L(TOP, L(TOP, B(1)))]
    ctxs = [()]
    for a in anns:
        for c in ('s', 'e'): ctxs.append((('y', c, a),))
    for a in anns:
        for c in ('s', 'e'):
            for b in [TOP, F('y'), L(F('y'), B(0)), L(TOP, F('y')), A(F('y'), TOP)]:
                for c2 in ('s', 'e'):
                    G = (('z', c2, b), ('y', c, a))
                    if S.ctx_prevalid(G): ctxs.append(G)
    terms = O['gen_terms'](['y', 'z'], maxsize)
    shard, nshards = int(os.environ.get('C_SHARD', 0)), int(os.environ.get('C_NSHARDS', 1))
    st = collections.Counter()
    for gi, G in enumerate(ctxs):
        if gi % nshards != shard: continue
        P.clear(O); memo.clear()
        if not all(O['wf'](G[i + 1:], b) and wfC(G[i + 1:], (), b) for i, (_, _, b) in enumerate(G)): continue
        st['contexts'] += 1
        ts = [t for t in terms if S.fv(t) <= S.dom(G)]
        wfO = {t for t in ts if O['wf'](G, t)}
        wfc = [t for t in ts if wfC(G, (), t)]
        st['wf_printed'] += len(wfO); st['wf_C'] += len(wfc)
        for t in wfc:
            if t not in wfO:
                st['C-only'] += 1
                if st['C-only'] <= 15: print("C ONLY:", showG(G), show(t))
        for t in wfO:
            if t not in set(wfc):
                st['printed-only'] += 1
                if st['printed-only'] <= 15: print("PRINTED ONLY:", showG(G), show(t))
        for t in wfc:
            for r in set(P.betas(t, openRec, closeRec)):
                st['L6-instances'] += 1
                if not wfC(G, (), r):
                    st['L6-FAIL'] += 1; print("L6 FAIL:", showG(G), "|", show(t), "↦", show(r))
        if not G:
            for t in wfc:
                w = t
                for _ in range(60):
                    if P.top_applied(w): st['UNSAFE'] += 1; print("UNSAFE:", show(t), "⟶*", show(w)); break
                    w = P.lo_step(w, openRec)
                    if w is None or tsize(w) > 400: break
        print(f"ctx {showG(G)}: " + ", ".join(f"{k} {v}" for k, v in sorted(st.items())))
    print(dict(st))

main(int(sys.argv[1]) if len(sys.argv) > 1 else 4)
