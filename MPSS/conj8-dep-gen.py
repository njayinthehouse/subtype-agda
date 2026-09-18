"""Random closed instances with DEPENDENT bounds, for both algorithms.

p = λy₁≤B₁. … λy_k≤B_k. body, each bound built from ⊤, earlier parameters and abstractions over
them; a promotion p ⟶ˢ p′; operands v_i chosen below the instantiated bounds. The exhaustive
probes (two names, terms to size 7) cannot reach these shapes. Both routes are run on every
instance: the substitution route (conj8-subst-probe.py) and the narrowing route
(conj8-lift-probe.py), and the result of each is checked at the top level.

  python3 conj8-dep-gen.py SEED COUNT
"""
import sys, os, random, functools, collections
os.environ['C8_NOMAIN'] = '1'
print = functools.partial(print, flush=True)
args = sys.argv[1:]
src = open('/home/egret/gimmick/1/MPSS/conj8-subst-probe.py').read()
exec(compile(src, 'subst', 'exec'))
globals()['WD'] = 6; globals()['SIZE'] = 44
seed, count = int(args[0]), int(args[1])
rng = random.Random(seed)
G = ()

def gen_type(vars_, depth):
    r = rng.random()
    if depth <= 0 or r < 0.35: return TOP if (not vars_ or rng.random() < 0.5) else F(rng.choice(vars_))
    if r < 0.5 and vars_: return F(rng.choice(vars_))
    a = gen_type(vars_, depth - 1)
    z = 'q%d' % rng.randrange(10**6)
    b = gen_type(vars_ + [z] if rng.random() < 0.4 else vars_, depth - 1)
    return L(a, closeRec(0, z, b))

def gen_body(vars_, depth):
    r = rng.random()
    if depth <= 0 or r < 0.25: return F(rng.choice(vars_))
    if r < 0.85:
        f = gen_body(vars_, depth - 1) if rng.random() < 0.4 else F(rng.choice(vars_))
        return A(f, gen_body(vars_, depth - 1) if rng.random() < 0.3 else F(rng.choice(vars_)))
    z = 'q%d' % rng.randrange(10**6)
    return L(gen_type(vars_, 1), closeRec(0, z, gen_body(vars_ + [z], depth - 1)))

def gen_p():
    k = rng.choice([2, 3, 3, 4])
    names = ['y%d' % i for i in range(k)]
    bounds = [gen_type(names[:i], 2) for i in range(k)]
    body = gen_body(names, 3)
    t = body
    for i in reversed(range(k)): t = L(bounds[i], closeRec(0, names[i], t))
    return t, names, bounds

def operands(bounds, names):
    out = []; sub = []
    for i, b in enumerate(bounds):
        inst = b
        for (n, v) in sub: inst = subst(n, v, inst)
        cands = [inst]
        if inst[0] == 'l':
            cands += [L(inst[1], B(0)), L(inst[1], inst[1])]
            if inst[2][0] == 'l': cands.append(L(inst[1], L(inst[2][1], B(0))))
        rng.shuffle(cands)
        pick = None
        for c in cands:
            if S.lc(c) and wf_(G, c) and (c == inst or layer(G, c, inst, WFD)): pick = c; break
        if pick is None: return None
        out.append(pick); sub.append((names[i], pick))
    return tuple(out)

stats = collections.Counter()
tries = 0
while stats['instances'] < count and tries < count * 400:
    tries += 1
    for m in (_wfd, _reach, _ecl, _fwd, _bwd):
        if len(m) > 200000: m.clear()
    try:
        p, names, bounds = gen_p()
        if tsize(p) > 21 or not wf_(G, p): continue
        S_ = operands(bounds, names)
        if S_ is None: continue
        m = rng.randrange(1, len(S_) + 1); S_ = S_[:m]
        targets = [q for q in sreds(G, (), p, 2) if q != p and q != TOP and wf_(G, q)]
        rng.shuffle(targets)
        for p2 in targets[:3]:
            lhs, rhs = spine(p, S_), spine(p2, S_)
            if rhs in sreds(G, (), lhs, 2): stats['trivial'] += 1; continue
            if not (wf_(G, lhs) and wf_(G, rhs)): continue
            stats['instances'] += 1
            line = f"p = {show(p)} | p′ = {show(p2)} | stack {S.showS(S_)}"
            for route in ('subst', 'narrow'):
                try:
                    if route == 'subst': R, Z = run_instance(G, [('s', p, p2)], S_); bad = check0(G, Z)
                    else:
                        R = Run(); Z = lift(R, G, [('s', p, p2)], S_, 0, (p, p2)); bad = check(G, Z, S_, None)
                    bad = [b for b in bad if not ('not found wf' in b[0] and wf_strong(G, b[1] if ('from' in b[0] or 'turn' in b[0]) else b[2]))]
                    if not bad: stats[route + '_ok'] += 1
                    else:
                        hard = any('not a' in b[0] for b in bad)
                        stats[route + ('_BAD_STEP' if hard else '_illformed_point')] += 1
                        if stats[route + '_printed'] < 12:
                            stats[route + '_printed'] += 1
                            print(f"{route.upper()} FLAG: {line} | {bad[0][0]}: {show(bad[0][1])} → {show(bad[0][2])}")
                except (Unresolved, Budget) as e:
                    stats[route + '_' + type(e).__name__] += 1
                    if stats[route + '_eprinted'] < 8:
                        stats[route + '_eprinted'] += 1
                        print(f"{route.upper()} {type(e).__name__}: {line} | {e}")
            if stats['instances'] % 50 == 0: print("…", dict(stats))
    except (MemoryError, RecursionError):
        stats['skipped'] += 1
        for m in (_wfd, _reach, _ecl, _fwd, _bwd, S._memo, _smemo): m.clear()
print("DONE", dict(stats), "tries", tries)
