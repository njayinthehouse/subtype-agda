"""Conjecture 8 by the substitution route, run as an algorithm and checked (CONJ8.md §13).

The narrowing route keeps an abstraction in place under its operand and produces ill-formed
points when a bound depends on a parameter an earlier operand instantiates. This is the other
route, the paper's own (Lemma 9 with Conjecture 8): contract the redex FIRST.

  under(A ⟶ˢ B, v)      the chain from A v to B v
      A v ⟶ˢ B v is a machine step                        that step
      A = λx≤t.u (then B = λx≤t.u′)                        β on both sides (two equivalence steps each,
                                                           as in Prop17Chain), then pair(u^v, u′^v)
      otherwise (the head of A is a redex)                 contract the head redex of A v and of B v,
                                                           then pair of the two contracta
  pair(X, Y)            X and Y differ at one covariant position, X[a] and X[b]
      Y is a machine step from X                           that step
      the difference is at the root                        a chain a ≤*wf b, by search (this is the
                                                           operand against the bound, v ≤*wf t)
      otherwise                                            pair(a, b) under the binders of the position,
                                                           then frame by frame: under(·, operand) at an
                                                           application, Ms-Fun/Me-Fun at a binder
  lift(D, S)            D's equivalence steps by congruence, its promotions by `under`, operand by operand

The result is checked at the top level exactly as in conj8-lift-probe.py: every step a machine
step, every promotion between well-formed terms, every turn at a well-formed term. Every call of
`pair` at the root (a use of the conjecture at a new pair) is logged with the pair, so that the
order the calls descend in — if there is one — can be read off.

  python3 conj8-subst-probe.py MAXSIZE SHARD NSHARDS [STACKSIZE default 3]
  C8_SAMPLE, C8_STACK3, C8_K, C8_WFD, C8_BUDGET as in conj8-lift-probe.py
"""
import sys, os, collections, gc, functools
print = functools.partial(print, flush=True)
argv1 = sys.argv[1:]
sys.argv = [sys.argv[0], '0', '0', '1']
src = open('/home/egret/gimmick/1/MPSS/conj8-lift-probe.py').read()
src = src[:src.rindex("main()")]
exec(compile(src, 'lift', 'exec'))   # chain, deriv, check, wf_, wf_strong, spine, Run, Budget, Unresolved, contexts, …

def head_and_args(t):
    args = []
    while t[0] == 'a': args.append(t[2]); t = t[1]
    return t, args[::-1]            # innermost operand first

def beta_head(G, X):
    """contract the head redex of X: two equivalence steps (bind-and-unfold, then Me-Bet on the
    closed body), returned with the contractum"""
    h, args = head_and_args(X)
    if h[0] != 'l' or not args: return None
    v = args[0]
    body = openRec(0, v, h[2])
    mid = ('l', h[1], body)
    def rebuild(f):
        t = ('a', f, v)
        for a in args[1:]: t = ('a', t, a)
        return t
    t2 = body
    for a in args[1:]: t2 = ('a', t2, a)
    return [X, rebuild(mid), t2]

def diff(G, X, Y):
    """X and Y differ at one covariant position: the frames down to it (outermost first), the two
    subterms, and the context extended by the binders passed"""
    frames = []
    while True:
        if X[0] == 'a' and Y[0] == 'a' and X[2] == Y[2] and X[1] != Y[1]:
            frames.append(('app', X[2])); X, Y = X[1], Y[1]
        elif X[0] == 'l' and Y[0] == 'l' and X[1] == Y[1] and X[2] != Y[2]:
            x = S.fresh(G, X, Y)
            frames.append(('fun', x, X[1])); G = ((x, 's', X[1]),) + G
            X, Y = openRec(0, ('f', x), X[2]), openRec(0, ('f', x), Y[2])
        else:
            return frames, X, Y, G

def pair(R, G, X, Y, depth, origin):
    if X == Y: return []
    if Y in sreds(G, (), X, K): return [('s', X, Y)]
    frames, a, b, Gx = diff(G, X, Y)
    if not frames:
        R.calls += 1; R.maxdepth = max(R.maxdepth, depth)
        if R.calls > BUDGET or depth > 30: raise Budget()
        D = chain(G, a, b, 8)
        if D is None: raise Unresolved(f"no chain {show(a)} ≤ {show(b)} in {showG(G)} ({origin})")
        R.trace.append((depth, origin, a, b, G))
        return D
    Kc = pair(R, Gx, a, b, depth, origin)
    Gk = Gx
    for fr in reversed(frames):
        if fr[0] == 'app':
            Kc = lift1(R, Gk, Kc, fr[1], depth)
        else:
            _, x, ann = fr
            Kc = [(k, ('l', ann, closeRec(0, x, p)), ('l', ann, closeRec(0, x, q))) for (k, p, q) in Kc]
            Gk = Gk[1:]
    return Kc

def under(R, G, A_, B_, v, depth):
    X, Y = ('a', A_, v), ('a', B_, v)
    if Y in sreds(G, (), X, K): return [('s', X, Y)]
    bx, by = beta_head(G, X), beta_head(G, Y)
    if bx is None or by is None:
        raise Unresolved(f"{show(X)} ⟶ˢ {show(Y)} is not a step and the head is not a redex")
    left  = [('e', bx[0], bx[1]), ('e', bx[1], bx[2])]
    right = [('r', by[2], by[1]), ('r', by[1], by[0])]
    origin = 'operand meets abstraction' if A_[0] == 'l' else 'redex at the head'
    return left + pair(R, G, bx[2], by[2], depth + 1, origin) + right

def lift1(R, G, D, v, depth):
    out = []
    for (k, a, b) in D:
        if k == 'e':   out.append(('e', ('a', a, v), ('a', b, v)))
        elif k == 'r': out.append(('r', ('a', a, v), ('a', b, v)))
        else:          out += under(R, G, a, b, v, depth)
    return out

def check0(G, Z):
    bad = []; prev = None
    for (k, a, b) in Z:
        if k == 'e' and b not in ereds(G, (), a, K): bad.append(('not an e-step', a, b))
        if k == 'r' and a not in ereds(G, (), b, K): bad.append(('not a backward e-step', a, b))
        if k == 's':
            if b not in sreds(G, (), a, K): bad.append(('not an s-step', a, b))
            if not wf_(G, a): bad.append(('promotion from a term not found wf', a, b))
            if not wf_(G, b): bad.append(('promotion to a term not found wf', a, b))
        if prev == 'r' and k != 'r' and not wf_(G, a): bad.append(('turn at a term not found wf', a, b))
        prev = k
    return bad

def run_instance(G, D, S_):
    R = Run(); Kc = D
    for v in S_: Kc = lift1(R, G, Kc, v, 0)
    return R, Kc

def main():
    maxsize, shard, nshards = int(argv1[0]), int(argv1[1]), int(argv1[2])
    stacksize = int(argv1[3]) if len(argv1) > 3 else 3
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
            ops = [t for t in small if S.fv(t) <= dn]
            stacks = [(v,) for v in ops] + [(v, v2) for v in ops for v2 in ops if tsize(v) + tsize(v2) <= 4]
            if os.environ.get('C8_STACK3'):
                stacks += [(v, v2, v3) for v in ops for v2 in ops for v3 in ops if tsize(v) + tsize(v2) + tsize(v3) <= 5]
            if SAMPLE:
                rng = random.Random(1000 * i + SAMPLE)
                big = [t for t in terms if tsize(t) == maxsize and applies_parameter(t) and S.fv(t) <= dn]
                rng.shuffle(big)
                subjects = [t for t in big[:SAMPLE * 4] if wf_(G, t)][:SAMPLE]
                pairs = []
                for u in subjects:
                    for c in fwd_(G, u, WD):
                        if c != u and tsize(c) <= maxsize + 4 and wf_(G, c) and any(st[0] == 's' for st in (chain(G, u, c) or [])):
                            pairs.append((u, c))
            else:
                pairs = [(u, t) for u in wfs for t in wfs if u != t]
            for (u, t) in pairs:
                D = chain(G, u, t)
                if D is None or not any(s[0] == 's' for s in D): continue
                for S_ in stacks:
                    if not (wf_(G, spine(u, S_)) and wf_(G, spine(t, S_))): continue
                    stats['instances'] += 1
                    try:
                        R, Z = run_instance(G, D, S_)
                    except Unresolved as e:
                        stats['unresolved'] += 1
                        if stats['unresolved'] <= 30: print("UNRESOLVED:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)), "|", e)
                        continue
                    except Budget:
                        stats['BUDGET'] += 1
                        print("BUDGET:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)))
                        continue
                    depthhist[R.maxdepth] += 1
                    if R.trace: stats['with_a_call'] += 1
                    for (d, origin, a, b, Gc) in R.trace: stats['call: ' + origin] += 1
                    bad = check0(G, Z)
                    if bad and all('not found wf' in b[0] for b in bad):
                        bad = [b for b in bad if not wf_strong(G, b[1] if ('from' in b[0] or 'turn' in b[0]) else b[2])]
                        if not bad: stats['ok_after_longer_chains'] += 1
                    if not bad: stats['ok'] += 1
                    else:
                        hard = {b[0] for b in bad} & {'not an e-step', 'not a backward e-step', 'not an s-step'}
                        key = 'BAD_STEP' if hard else 'wf_not_found'
                        stats[key] += 1
                        if stats[key] <= 40:
                            print("BAD STEP:" if hard else "WF NOT FOUND:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)),
                                  "|", "; ".join(f"{m}: {show(a)} → {show(b)}" for (m, a, b) in bad[:2]))
                    if R.maxdepth >= 2 and stats['deep_printed'] < 20:
                        stats['deep_printed'] += 1
                        print("NESTED:", showG(G), "|", show(spine(u, S_)), "≤", show(spine(t, S_)), "|",
                              " / ".join(f"d{d} [{o}] {show(a)}≤{show(b)}" for (d, o, a, b, _) in R.trace))
        except (MemoryError, RecursionError) as e:
            print(f"SKIPPED ctx {showG(G)}: {type(e).__name__}"); stats['skipped'] += 1
        print(f"ctx {i} {showG(G)}: {dict(stats)} depth {dict(depthhist)}")
    print("DONE", dict(stats), "depth", dict(depthhist))

if __name__ == '__main__' and not os.environ.get('C8_NOMAIN'):
    main()
