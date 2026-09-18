"""Nesting-depth probe for Conjecture 8 (CONJ8.md §4, §7: "the next thing to probe").

The depth of a well-formedness derivation counts how many times it passes from an application's
Wf-App into the well-subtyping chains that justify it:

    depth(Wf-PrS | Wf-PrE | Wf-Top) = 0
    depth(Wf-Fun F d)               = max over its premises
    depth(Wf-App d₁ d₂)             = 1 + max(depth d₁, depth d₂)
    depth of a ≤wf / ≤*wf chain     = max over the wf premises of Ws-Lf2, Ws-Sub, Ws-Trs

Ws-Trs, weakening and the e-steps of a layer leave it unchanged. WF_d is the set of terms with a
derivation of depth ≤ d, and u ≤_d t a chain whose ends and promotion points lie in WF_d. Both are
computed bottom-up in d, bounded (chain length WD, promotion cap WK, term size SIZE), so
"derivable at depth d" is a sound under-approximation and md (the least such d) an upper bound.

An induction on the depth closes the mutual recursion of Conjecture 8 with Lemmas 7 and 9 if the
three lemmas do not raise it. The probe tests exactly that, on minimal depths:

  T0  u ≤*wf t                       ⇒  md(u ≤ t) ≤ max(md u, md t)
  T1  u ≤*wf t, Co[u] wf, Co[t] wf   ⇒  Co[u] ≤_k Co[t]  at k = max(md Co[u], md Co[t])
  T2  x≤w,Γ ⊢ b wf,  Γ ⊢ v ≤*wf w    ⇒  md(b[x\\v]) ≤ max(md b, md(v ≤ w))          (Lemma 7)
  T4  md(b[x\v]) against md((λx≤w.b) v): does contracting the redex lower the depth?
  T5  x≤w,Γ ⊢ b wf,  Γ ⊢ v ≤*wf w    ⇒  md_{x≡v,Γ}(b) ≤ max(md b, md(v ≤ w))   (the operand kept in
      the context as Ms-FOp keeps it, in place of Lemma 7's substitution)
  T6  the recursion's own round: the instance (f v, f′ v) for a promotion of f's parameter in
      covariant position, against the recursive instance (Co″σ[v], Co″σ[w]): does max-depth drop?
  T3  x≤w,Γ ⊢ b ⟶ˢ b′ between wf, Γ ⊢ v ≤*wf w
                                     ⇒  md(b[x\\v] ≤ b′[x\\v]) ≤ max(md b, md b′, md(v ≤ w))  (Lemma 9)

A reported EXCESS is a candidate, to be re-run with larger caps before it means anything.

  python3 conj8-depth-probe.py MAXSIZE SHARD NSHARDS [tests, default 0123]
  caps from the environment: C8_DMAX (4), C8_WD (4), C8_SIZE (18); C8_CTX=i,j,… restricts the contexts
"""
import sys, collections, gc
sys.setrecursionlimit(20000)
argv = sys.argv[1:]; sys.argv = [sys.argv[0]]
src = open('/home/egret/gimmick/1/MPSS/conj8-search.py').read().replace("main()\n", "")
exec(compile(src, 'c8', 'exec'))          # S, sreds, ereds, closure, machine, plugs, gen_terms, tsize …

import os
DMAX = int(os.environ.get('C8_DMAX', 4))
WK, WD, SIZE = 2, int(os.environ.get('C8_WD', 4)), int(os.environ.get('C8_SIZE', 18))
ONLY = {int(i) for i in os.environ.get('C8_CTX', '').split(',') if i}      # context indices; empty = all

_wfd = {}
def wfd(G, t, d):
    """Γ ⊢ t wf by a derivation of depth ≤ d"""
    if d < 0: return False
    key = (G, t, d)
    if key in _wfd: return _wfd[key]
    _wfd[key] = False
    res = False
    if S.ctx_prevalid(G) and S.lc(t) and S.fv(t) <= S.dom(G):
        c = t[0]
        if c == 'f': res = any(y == t[1] for (y, _, _) in G)
        elif c == 'T': res = True
        elif c == 'l':
            w, b = t[1], t[2]; x = S.fresh(G, t)
            res = wfd(G, w, d) and wfd(((x, 's', w),) + G, openRec(0, ('f', x), b), d)
        elif d >= 1:
            u, v = t[1], t[2]
            if wfd(G, u, d - 1) and wfd(G, v, d - 1):
                for a in reach(G, u, d - 1):
                    if a[0] != 'l': continue
                    tt = a[1]; target = ('l', tt, TOP)
                    if not wfd(G, target, d - 1): continue
                    if a != target and not wfd(G, a, d - 1): continue   # λtt.b ⟶ˢ λtt.⊤ between wf terms
                    if layer(G, v, tt, d - 1): res = True; break
    _wfd[key] = res
    return res

_reach = {}
def reach(G, u, d):
    """a with u ⟶* a, e-steps anywhere and s-steps between terms of WF_d (Ws-Lf1, Ws-Lf2)"""
    key = (G, u, d)
    if key in _reach: return _reach[key]
    seen = {u}; frontier = [u]
    for _ in range(WD):
        nxt = []
        for a in frontier:
            for b in ereds(G, (), a, WK):
                if b not in seen and tsize(b) <= SIZE: seen.add(b); nxt.append(b)
            if wfd(G, a, d):
                for b in sreds(G, (), a, WK):
                    if b not in seen and tsize(b) <= SIZE and wfd(G, b, d): seen.add(b); nxt.append(b)
        frontier = nxt
    _reach[key] = seen
    return seen

_ecl = {}
def ecl(G, t):
    key = (G, t)
    if key not in _ecl: _ecl[key] = closure(ereds, G, (), t, WK, WD)
    return _ecl[key]

def layer(G, u, t, d):
    """u ≤_d t : one Ws-Sub layer at depth ≤ d (promotions chained through WF_d)"""
    if not (wfd(G, u, d) and wfd(G, t, d)): return False
    return bool(reach(G, u, d) & ecl(G, t))

def md(G, t):
    for d in range(DMAX + 1):
        if wfd(G, t, d): return d
    return None

def md_sub(G, u, t, lo=0):
    for d in range(lo, DMAX + 1):
        if layer(G, u, t, d): return d
    return None

def ctx_depth(G):
    """the depth the context itself carries: a promotion x ⟶ˢ bound(x) lands on the annotation,
    which Ws-Lf2 wants well-formed, so a chain between depth-0 ends can need the bound's depth"""
    k = 0
    for i, (x, c, t) in enumerate(G):
        m = md(G[i + 1:], t)
        if m is None: m = md(G, t)
        if m is not None: k = max(k, m)
    return k

def subst(x, v, t):
    c = t[0]
    if c == 'f': return v if t[1] == x else t
    if c in 'bT': return t
    return (c, subst(x, v, t[1]), subst(x, v, t[2]))

def contexts():
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
    return ctxs

def main():
    maxsize, shard, nshards = int(argv[0]), int(argv[1]), int(argv[2])
    tests = argv[3] if len(argv) > 3 else '0123'
    terms = gen_terms(['y', 'z'], maxsize)
    ctxs = contexts()
    stats = collections.Counter()
    for i, G in enumerate(ctxs):
        if i % nshards != shard: continue
        if ONLY and i not in ONLY: continue
        try:
            one_context(G, terms, tests, stats)
        except (MemoryError, RecursionError) as e:
            print(f"SKIPPED ctx {showG(G)}: {type(e).__name__}", flush=True)
            stats['skipped'] += 1
        print(f"ctx {i} {showG(G)}: {dict(stats)}", flush=True)
    print("DONE", dict(stats), flush=True)

def one_context(G, terms, tests, stats):
    for m in (S._memo, _smemo, _wfd, _reach, _ecl): m.clear()
    gc.collect()
    dn = S.dom(G)
    ts = [t for t in terms if S.fv(t) <= dn]
    dep = {}
    for t in ts:
        k = md(G, t)
        if k is not None: dep[t] = k; stats[f'wf_depth_{k}'] += 1
    wfs = list(dep)
    cd = ctx_depth(G); stats[f'ctx_depth_{cd}'] += 1
    pairs = []
    for u in wfs:
        for t in wfs:
            if u == t: continue
            k = md_sub(G, u, t)
            if k is None: continue
            pairs.append((u, t, k))
            if '0' in tests:
                stats['T0'] += 1
                if k > max(dep[u], dep[t], cd):
                    stats['T0_EXCESS'] += 1
                    print("T0 EXCESS:", showG(G), "|", show(u), "≤", show(t), "| ends", dep[u], dep[t], "ctx", cd, "chain", k, flush=True)
    if '1' in tests:
        cos = [(('app', v),) for v in ts] + [(('fun', a),) for a in ts]
        for (u, t, _) in pairs:
            for Co in cos:
                cu, ct = plugs(Co, u), plugs(Co, t)
                ku, kt = md(G, cu), md(G, ct)
                if ku is None or kt is None: continue
                k = max(ku, kt, cd); stats['T1'] += 1
                got = md_sub(G, cu, ct, k)
                if got == k: stats['T1_ok'] += 1
                elif got is not None:
                    stats['T1_EXCESS'] += 1
                    print("T1 EXCESS:", showG(G), "|", show(cu), "≤", show(ct), "| ends", ku, kt, "chain", got, flush=True)
                else:
                    stats['T1_unresolved'] += 1
                    if not machine(G, (), cu, ct, WK, 6):
                        stats['T1_NOMACHINE'] += 1
                        print("T1 NO MACHINE CHAIN:", showG(G), "|", show(cu), "vs", show(ct), flush=True)
    if set(tests) & set('2356') and G and G[0][1] == 's':
        x, _, w = G[0]; G0 = G[1:]
        vs = []
        for v in terms:
            if not S.fv(v) <= S.dom(G0): continue
            k = md_sub(G0, v, w) if v != w else md(G0, w)
            if k is not None: vs.append((v, k))
        for b in wfs:
            if ('f', x) not in _subterms(b): continue
            for (v, kv) in vs:
                bound = max(dep[b], kv)
                bs = subst(x, v, b)
                if '2' in tests:
                    stats['T2'] += 1
                    got = md(G0, bs)
                    if got is None:
                        stats['T2_unresolved'] += 1
                        print("T2 UNRESOLVED:", showG(G), "|", show(b), "[", x, "\\", show(v), "] | bound", bound, flush=True)
                    else:
                        # substitution: is the depth bounded by the max, or only by the sum?
                        stats['T2_le_max' if got <= max(bound, cd) else 'T2_le_sum' if got <= dep[b] + kv + cd else 'T2_OVER_SUM'] += 1
                        if got > dep[b] + kv + cd:
                            print("T2 OVER SUM:", showG(G), "|", show(b), "[", x, "\\", show(v), "] | body", dep[b], "operand", kv, "got", got, flush=True)
                        # the β-redex against its contractum: does a round of the recursion descend?
                        redex = ('a', ('l', w, closeRec(0, x, b)), v)
                        kr = md(G0, redex)
                        if kr is not None:
                            stats['T4_reduct_lt_redex' if got < kr else 'T4_reduct_eq_redex' if got == kr else 'T4_REDUCT_GT_REDEX'] += 1
                            if got > kr:
                                print("T4 REDUCT DEEPER:", showG(G0), "|", show(redex), "depth", kr, "⟶", show(bs), "depth", got, flush=True)
                if '6' in tests:
                    # the recursion itself: f = λx≤w.Co″[x] ⟶ˢ f′ = λx≤w.Co″[w] under the operand v.
                    # The instance is (f v, f′ v); the recursive instance is (Co″σ[v], Co″σ[w]), σ = x\v.
                    for bw in covariant_promotions(b, x, w):
                        f, f2 = ('l', w, closeRec(0, x, b)), ('l', w, closeRec(0, x, bw))
                        k1, k2 = md(G0, ('a', f, v)), md(G0, ('a', f2, v))
                        if k1 is None or k2 is None: continue
                        r1, r2 = md(G0, bs), md(G0, subst(x, v, bw))
                        stats['T6'] += 1
                        if r1 is None or r2 is None: stats['T6_unresolved'] += 1; continue
                        mu, mu2 = max(k1, k2), max(r1, r2)
                        stats['T6_lower' if mu2 < mu else 'T6_equal' if mu2 == mu else 'T6_HIGHER'] += 1
                        if mu2 > mu:
                            print("T6 HIGHER:", showG(G0), "| f =", show(f), "| v =", show(v), "| instance", mu,
                                  "| recursive", show(bs), "vs", show(subst(x, v, bw)), mu2, flush=True)
                if '5' in tests:
                    # keep the operand in the context, as Ms-FOp does, instead of substituting it:
                    # x stays a variable (Wf-PrE, depth 0), so is the depth the max and not the sum?
                    Ge = ((x, 'e', v),) + G0
                    if S.ctx_prevalid(Ge):
                        stats['T5'] += 1
                        got = md(Ge, b)
                        if got is None:
                            stats['T5_unresolved'] += 1
                            print("T5 UNRESOLVED:", showG(Ge), "|", show(b), "| under ≤ it has depth", dep[b], flush=True)
                        elif got > max(bound, cd):
                            stats['T5_EXCESS'] += 1
                            print("T5 EXCESS:", showG(Ge), "|", show(b), "| bound", max(bound, cd), "got", got, flush=True)
                        else: stats['T5_ok'] += 1
                if '3' in tests and wfd(G, b, DMAX):
                    for b2 in sreds(G, (), b, WK):
                        if b2 == b or b2 not in dep: continue
                        bnd = max(bound, dep[b2]); b2s = subst(x, v, b2)
                        if bs == b2s: continue
                        stats['T3'] += 1
                        lo = max(md(G0, bs) or 0, md(G0, b2s) or 0)
                        got = md_sub(G0, bs, b2s, 0)
                        if got is None:
                            stats['T3_unresolved'] += 1
                            print("T3 UNRESOLVED:", showG(G), "|", show(bs), "≤", show(b2s), "| bound", bnd, flush=True)
                        elif got > max(bnd, cd, md(G0, bs) or 0, md(G0, b2s) or 0):
                            stats['T3_EXCESS'] += 1
                            print("T3 EXCESS:", showG(G), "|", show(bs), "≤", show(b2s), "| bound", bnd, "got", got, flush=True)
                        else: stats['T3_ok'] += 1

def covariant_promotions(b, x, w):
    """b with one occurrence of x in covariant position (function position or an abstraction's
    body, never the hole alone) promoted to its bound w"""
    def go(t, top):
        c = t[0]
        if c == 'f' and t[1] == x and not top: yield w
        elif c == 'a':
            for r in go(t[1], False): yield ('a', r, t[2])
        elif c == 'l':
            for r in go(t[2], False): yield ('l', t[1], r)
    return list(go(b, True))

def _subterms(t):
    out = {t}
    if t[0] in 'al': out |= _subterms(t[1]) | _subterms(t[2])
    return out

main()
