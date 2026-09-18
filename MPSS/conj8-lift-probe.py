"""Conjecture 8 without substitution: FunLift and FOpLift as an algorithm, run and checked.

CONJ8.md §8 left two things to try. This is the second: a formulation of the two binding rules
that never substitutes the operand, and keeps it in the context as the machine does.

The obligation (MPSS.Conj8Push). A promotion a ⟶ˢ a′ at the empty stack, between well-formed
terms, is to be lifted under further operands S:  spine a S ≤*wf spine a′ S.  Every rule lifts as
itself except Ms-Fun meeting an operand: the body was promoted under x ≤ t, and under the operand
v the machine reduces it under x ≡ v (Ms-FOp). So the body's derivation is *narrowed*, x ≤ t to
x ≡ v, and pushed under the rest of the stack, by recursion on the derivation itself:

  push(F, S)      F : p ⟶ˢ q at stack s₀, some parameters narrowed; result: a zigzag of machine
                  steps from p to q at stack s₀ ++ S in the narrowed context
    Ms-Top, Ms-Equ, Ms-Pro y (y not narrowed)   the step itself
    Ms-App F′                                   push(F′, S), one operand deeper
    Ms-Fun F′, S = []                           push(F′, []) under x ≤ t, each step under Ms-Fun
    Ms-Fun F′, S = v ∷ s                        narrow x to v; push(F′, s) under x ≡ v, under Ms-FOp
    Ms-FOp F′                                   push(F′, S) under x ≡ α, each step under Ms-FOp
    Ms-Pro x, x narrowed to v with bound t      x ⟶ᵉ v, then lift(D, s₀ ++ S) for a chain D : v ≤*wf t

  lift(D, σ)      every e-step of D at stack σ (pushᵉ), every promotion by push(its derivation, σ)

lift calls push calls lift: that loop is the conjecture. The probe runs the algorithm on every
instance it can find (a chain u ≤*wf t, a stack S with spine u S and spine t S well-formed), and
checks the zigzag it returns *at the top level*, in the original context at the empty stack:
every step is a machine step, every promotion is between well-formed terms, every turn from
backward e-steps to forward steps is at a well-formed term. It also records the shape of the
recursion: how deep lift nests, and what each nested call is given.

  python3 conj8-lift-probe.py MAXSIZE SHARD NSHARDS [STACKSIZE default 3]
  C8_PERVERSE=k: nested chains by a randomised walk (longest of k tries) instead of the shortest
  C8_SAMPLE=n: n sampled subjects of size MAXSIZE per context, in place of all pairs; C8_K, C8_WFD, C8_BUDGET, and the depth probe's caps
"""
import sys, os, collections, gc
argv0 = sys.argv[1:]
sys.argv = [sys.argv[0], '0', '0', '1']
src = open('/home/egret/gimmick/1/MPSS/conj8-depth-probe.py').read()
src = src[:src.rindex("main()")]
exec(compile(src, 'c8d', 'exec'))     # S, sreds, ereds, wfd, tsize, contexts, gen_terms, show, …

K = int(os.environ.get('C8_K', 3))            # Me-Pro nesting cap for step membership
WFD = int(os.environ.get('C8_WFD', 5))        # depth cap of the well-formedness oracle
BUDGET = int(os.environ.get('C8_BUDGET', 400))

SAMPLE = int(os.environ.get('C8_SAMPLE', 0))
import random

def applies_parameter(t):
    c = t[0]
    if c == 'a': return t[1][0] == 'b' or applies_parameter(t[1]) or applies_parameter(t[2])
    if c == 'l': return applies_parameter(t[1]) or applies_parameter(t[2])
    return False

class Unresolved(Exception): pass
class Budget(Exception): pass

def wf_(G, t): return wfd(G, t, WFD)

def wf_strong(G, t):
    """the oracle again with longer chains, for a term the first pass did not find well-formed"""
    global WD
    saved = (WD, dict(_wfd), dict(_reach), dict(_ecl))
    try:
        WD = int(os.environ.get('C8_WD_STRONG', 8))
        _wfd.clear(); _reach.clear(); _ecl.clear()
        return wfd(G, t, WFD + 2)
    except (MemoryError, RecursionError):
        return False
    finally:
        WD = saved[0]
        _wfd.clear(); _wfd.update(saved[1]); _reach.clear(); _reach.update(saved[2]); _ecl.clear(); _ecl.update(saved[3])

def spine(a, s):
    for v in s: a = ('a', a, v)
    return a

# ---- a chain u ≤*wf t, with its steps: ('e',p,q) p⟶ᵉq · ('s',p,q) p⟶ˢq between wf · ('r',p,q) q⟶ᵉp
_fwd, _bwd = {}, {}
def fwd_(G, u, steps):
    key = (G, u, steps)
    if key in _fwd: return _fwd[key]
    par = {u: None}; frontier = [u]
    for _ in range(steps):
        nxt = []
        for a in frontier:
            for b in ereds(G, (), a, WK):
                if b not in par and tsize(b) <= SIZE: par[b] = ('e', a); nxt.append(b)
            if wf_(G, a):
                for b in sreds(G, (), a, WK):
                    if b not in par and tsize(b) <= SIZE and wf_(G, b): par[b] = ('s', a); nxt.append(b)
        frontier = nxt
    _fwd[key] = par
    return par

def bwd_(G, t, steps):
    key = (G, t, steps)
    if key in _bwd: return _bwd[key]
    back = {t: None}; bfront = [t]
    for _ in range(steps):
        nxt = []
        for a in bfront:
            for b in ereds(G, (), a, WK):
                if b not in back and tsize(b) <= SIZE: back[b] = a; nxt.append(b)
        bfront = nxt
    _bwd[key] = back
    return back

PERVERSE = int(os.environ.get('C8_PERVERSE', 0))
_prng = random.Random(7)

def perverse_chain(G, u, t, steps):
    """a chain u ≤*wf t found by a randomised depth-first walk, promotions tried first: the
    nested chains of a proof are given, not chosen, so the recursion should not depend on
    their being short"""
    back = bwd_(G, t, steps)
    best = None
    for _ in range(PERVERSE):
        path = []; a = u; seen = {u}
        for _ in range(steps + 3):
            if a in back and path and _prng.random() < 0.5: break
            nxt = []
            if wf_(G, a):
                nxt += [('s', b) for b in sreds(G, (), a, WK) if b not in seen and tsize(b) <= SIZE and wf_(G, b)]
            nxt += [('e', b) for b in ereds(G, (), a, WK) if b not in seen and tsize(b) <= SIZE]
            if not nxt: break
            k, b = _prng.choice(nxt[:6]) if _prng.random() < 0.7 else _prng.choice(nxt)
            path.append((k, a, b)); seen.add(b); a = b
        if a in back:
            bwd = []; c = a
            while back[c] is not None:
                bwd.append(('r', c, back[c])); c = back[c]
            cand = path + bwd
            if best is None or len(cand) > len(best): best = cand
    return best

def chain(G, u, t, steps=None, nested=False):
    steps = steps or WD
    if PERVERSE and nested:
        c = perverse_chain(G, u, t, steps)
        if c is not None: return [s for s in c if not (s[0] == 'e' and s[1] == s[2])]
    par, back = fwd_(G, u, steps), bwd_(G, t, steps)
    c = None
    small, big = (par, back) if len(par) <= len(back) else (back, par)
    for a in small:                      # breadth-first insertion order: the first hit is a shortest one
        if a in big: c = a; break
    if c is None: return None
    fwd = []; a = c
    while par[a] is not None:
        k, p = par[a]; fwd.append((k, p, a)); a = p
    fwd.reverse()
    bwd = []; a = c
    while back[a] is not None:
        bwd.append(('r', a, back[a])); a = back[a]
    return [s for s in fwd + bwd if not (s[0] == 'e' and s[1] == s[2])]

# ---- a derivation of p ⟶ˢ q at G;s
def deriv(G, s, p, q):
    c = p[0]
    if c == 'f' and lookup_sub(G, p[1]) == q and q is not None: return ('Pro', p[1])
    if c == 'a' and q[0] == 'a' and q[2] == p[2]:
        d = deriv(G, (p[2],) + s, p[1], q[1])
        if d: return ('App', d)
    if c == 'l' and q[0] == 'l' and q[1] == p[1]:
        w = p[1]
        if not s:
            x = S.fresh(G, p, q)
            d = deriv(((x, 's', w),) + G, (), openRec(0, ('f', x), p[2]), openRec(0, ('f', x), q[2]))
            if d: return ('Fun', x, w, d)
        else:
            x = S.fresh(G, p, q, s)
            d = deriv(((x, 'e', s[0]),) + G, s[1:], openRec(0, ('f', x), p[2]), openRec(0, ('f', x), q[2]))
            if d: return ('FOp', x, w, d)
    if q == TOP: return ('Top',)
    if q in ereds(G, s, p, K): return ('Equ',)
    return None

# ---- the algorithm
class Run:
    def __init__(self): self.calls = 0; self.maxdepth = 0; self.trace = []

def push(R, Gn, N, F, p, q, s0, S_, depth):
    k = F[0]
    if k == 'Pro':
        y = F[1]
        if y not in N: return [('s', p, q)]
        v, t = N[y]
        D = chain(Gn, v, t, 8, nested=True)
        if D is None: raise Unresolved(f"no chain {show(v)} ≤ {show(t)} in {showG(Gn)}")
        return [('e', p, v)] + lift(R, Gn, D, s0 + S_, depth + 1, (v, t))
    if k == 'Top': return [('s', p, q)]
    if k == 'Equ': return [('e', p, q)]
    if k == 'App':
        o = p[2]
        Z = push(R, Gn, N, F[1], p[1], q[1], (o,) + s0, S_, depth)
        return [(kk, ('a', a, o), ('a', b, o)) for (kk, a, b) in Z]
    x, w, F2 = F[1], F[2], F[3]
    ob, oq = openRec(0, ('f', x), p[2]), openRec(0, ('f', x), q[2])
    if k == 'Fun':
        if not S_:
            Z = push(R, ((x, 's', w),) + Gn, N, F2, ob, oq, (), (), depth)
        else:
            v = S_[0]
            N2 = dict(N); N2[x] = (v, w)
            Z = push(R, ((x, 'e', v),) + Gn, N2, F2, ob, oq, (), S_[1:], depth)
    else:
        Z = push(R, ((x, 'e', s0[0]),) + Gn, N, F2, ob, oq, s0[1:], S_, depth)
    return [(kk, ('l', w, closeRec(0, x, a)), ('l', w, closeRec(0, x, b))) for (kk, a, b) in Z]

def lift(R, G, D, sigma, depth, what):
    R.calls += 1; R.maxdepth = max(R.maxdepth, depth)
    if R.calls > BUDGET or depth > 40: raise Budget()
    R.trace.append((depth, len(sigma), sum(1 for s in D if s[0] == 's'), what, G))
    out = []
    for (k, a, b) in D:
        if k != 's': out.append((k, a, b)); continue
        F = deriv(G, (), a, b)
        if F is None: raise Unresolved(f"no derivation {show(a)} ⟶ˢ {show(b)}")
        out += push(R, G, {}, F, a, b, (), sigma, depth)
    return out

# ---- the bounds along a nesting path: is each the domain of the one before?
# Round k narrows a parameter of bound t_k to an operand v_k. The next round happens inside
# lift(v_k ≤ t_k): an abstraction λx′≤t′.… of that chain meets an operand, and t_{k+1} = t′. That
# abstraction is below t_k, and t_k is applied to the same operand, so t_k ≤*wf λt″.⊤ with t″ ≡ t′:
# the bound of each round is, up to ≡, the domain of the bound of the round before — the order on
# which hereditary substitution terminates for simple types.
def domain_descent(R, stats):
    path = {}
    for (d, n, k, w, G) in R.trace:
        path[d] = (w, G)
        if d < 2: continue
        (vp, tp), _ = path[d - 1]; (v, t), Gc = path[d]
        stats['descent_checked'] += 1
        doms = [a[1] for a in fwd_(Gc, tp, 6) if a[0] == 'l']
        tcl = set(bwd_(Gc, t, 6))
        if any(dm == t or (set(bwd_(Gc, dm, 6)) & tcl) for dm in doms): stats['descent_ok'] += 1
        else:
            stats['DESCENT_FAILS'] += 1
            if stats['DESCENT_FAILS'] <= 20:
                print("DESCENT FAILS:", showG(Gc), "| bound", show(tp), "then bound", show(t), flush=True)

# ---- checking the result at the top level
def check(G, Z, S_, stats):
    bad = []
    prev = None
    for (k, a, b) in Z:
        A, B = spine(a, S_), spine(b, S_)
        if k == 'e' and B not in ereds(G, (), A, K): bad.append(('not an e-step', A, B))
        if k == 'r' and A not in ereds(G, (), B, K): bad.append(('not a backward e-step', A, B))
        if k == 's':
            if B not in sreds(G, (), A, K): bad.append(('not an s-step', A, B))
            if not wf_(G, A): bad.append(('promotion from a term not found wf', A, B))
            if not wf_(G, B): bad.append(('promotion to a term not found wf', A, B))
        if prev == 'r' and k != 'r' and not wf_(G, A): bad.append(('turn at a term not found wf', A, B))
        prev = k
    return bad

def main():
    maxsize, shard, nshards = int(argv0[0]), int(argv0[1]), int(argv0[2])
    stacksize = int(argv0[3]) if len(argv0) > 3 else 3
    terms = gen_terms(['y', 'z'], maxsize)
    small = [t for t in terms if tsize(t) <= stacksize]
    stats = collections.Counter(); depthhist = collections.Counter()
    for i, G in enumerate(contexts()):
        if i % nshards != shard: continue
        if ONLY and i not in ONLY: continue
        try:
            for m in (S._memo, _smemo, _wfd, _reach, _ecl, _fwd, _bwd): m.clear()
            gc.collect()
            dn = S.dom(G)
            wfs = [t for t in terms if S.fv(t) <= dn and wf_(G, t)]
            if SAMPLE:
                # sampled mode: subjects of the largest size whose abstractions apply their own
                # parameter (the rounds that put new operands on the stack); targets read off the
                # subject's own forward closure, so every pair comes with a chain
                rng = random.Random(1000 * i + SAMPLE)
                big = [t for t in terms if tsize(t) == maxsize and applies_parameter(t) and S.fv(t) <= dn]
                rng.shuffle(big)
                subjects = [t for t in big[:SAMPLE * 4] if wf_(G, t)][:SAMPLE]
                pairs = []
                for u in subjects:
                    par = fwd_(G, u, WD)
                    for c in par:
                        if c != u and tsize(c) <= maxsize + 4 and wf_(G, c) and any(st[0] == 's' for st in (chain(G, u, c) or [])):
                            pairs.append((u, c))
                stats['subjects'] += len(subjects)
            else:
                pairs = [(u, t) for u in wfs for t in wfs if u != t]
            ops = [t for t in small if S.fv(t) <= dn]
            stacks = [(v,) for v in ops] + [(v, v2) for v in ops for v2 in ops if tsize(v) + tsize(v2) <= 4]
            if os.environ.get('C8_STACK3'):
                stacks += [(v, v2, v3) for v in ops for v2 in ops for v3 in ops if tsize(v) + tsize(v2) + tsize(v3) <= 5]
            for (u, t) in pairs:
                if True:
                    D = chain(G, u, t)
                    if D is None or not any(s[0] == 's' for s in D): continue
                    for S_ in stacks:
                        if not (wf_(G, spine(u, S_)) and wf_(G, spine(t, S_))): continue
                        stats['instances'] += 1
                        R = Run()
                        try:
                            Z = lift(R, G, D, S_, 0, (u, t))
                        except Unresolved as e:
                            stats['unresolved'] += 1
                            if stats['unresolved'] <= 40: print("UNRESOLVED:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)), "|", e, flush=True)
                            continue
                        except Budget:
                            stats['BUDGET'] += 1
                            print("BUDGET:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)), flush=True)
                            continue
                        depthhist[R.maxdepth] += 1
                        domain_descent(R, stats)
                        stats['max_sigma'] = max(stats['max_sigma'], max(n for (_, n, _, _, _) in R.trace))
                        if R.maxdepth >= 1: stats['with_a_round'] += 1
                        bad = check(G, Z, S_, stats)
                        if bad and all('not found wf' in b[0] for b in bad):
                            bad = [b for b in bad if not wf_strong(G, b[1] if 'from' in b[0] or 'turn' in b[0] else b[2])]
                            if not bad: stats['ok_after_longer_chains'] += 1
                        if not bad: stats['ok'] += 1
                        else:
                            kinds = {b[0] for b in bad}
                            hard = kinds & {'not an e-step', 'not a backward e-step', 'not an s-step'}
                            stats['BAD_STEP' if hard else 'wf_not_found'] += 1
                            if stats['BAD_STEP' if hard else 'wf_not_found'] <= 60:
                                print("BAD STEP:" if hard else "WF NOT FOUND:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)),
                                      "| rounds", R.maxdepth, "|", "; ".join(f"{m}: {show(a)} → {show(b)}" for (m, a, b) in bad[:3]), flush=True)
                        if R.maxdepth >= 2 and stats['deep_printed'] < 25:
                            stats['deep_printed'] += 1
                            print("NESTED:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)), "|",
                                  " / ".join(f"d{d} |σ|={n} promotions={k} {show(w[0])}≤{show(w[1])}" for (d, n, k, w, _) in R.trace), flush=True)
        except (MemoryError, RecursionError) as e:
            print(f"SKIPPED ctx {showG(G)}: {type(e).__name__}", flush=True); stats['skipped'] += 1
        print(f"ctx {i} {showG(G)}: {dict(stats)} rounds {dict(depthhist)}", flush=True)
    print("DONE", dict(stats), "rounds", dict(depthhist), flush=True)

main()
