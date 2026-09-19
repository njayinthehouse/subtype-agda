"""Candidate A of CONJ8.md §25: Ms-FOp keeps the bound.

As printed, Ms-FOp promotes the body of a consumed abstraction (λx≤A.b, operand a on the stack)
under x ≡ a, and x ≤ A is forgotten. Candidate A promotes it under an entry that ⟶ᵉ reads as
x ≡ a and ⟶ˢ reads also as x ≤ A, so Ms-Pro fires on a consumed parameter:

    x ≡ a ≤ A, Γ ; s ⊢ b ⟶ˢ b′
    ─────────────────────────────── Ms-FOpᴬ
    Γ ; a ∷ s ⊢ λx≤A.b ⟶ˢ λx≤A.b′

⟶ᵉ, Figure 4 and ↦ are unchanged. Nothing existing is edited: the enumerating probes are loaded
and their `sreds` replaced; the goal-directed checker of conj8-hurkens-probe.py is subclassed.
The entry is a third kind 'p' whose payload ('P', a, A) pairs the two terms (fv and lc of the
base module read such a payload componentwise, so prevalidity is unchanged).

  python3 conj8-A-probe.py small MAXSIZE      enumeration: wf_old ⊆ wf_A, Theorem 11, safety,
                                              Lemma 6, Conjecture 8, Theorem 3 (contexts sharded
                                              by the environment: A_SHARD, A_NSHARDS)
  python3 conj8-A-probe.py t3                 Theorem 3 at the machine level fails under A
  python3 conj8-A-probe.py validate MAXSIZE   the goal-directed A-checker against the A-oracle
  python3 conj8-A-probe.py hurkens [STEPS]    the two Hurkens instances (§22, §23) under A
  python3 conj8-A-probe.py safety MAXSIZE     closed terms the A-checker accepts, evaluated

Bounded throughout: a reported failure is a candidate until analysed by hand.
"""
import sys, functools, collections, gc, random
from importlib.machinery import SourceFileLoader
sys.setrecursionlimit(1000000)
print = functools.partial(print, flush=True)
HERE = '/home/egret/gimmick/1/MPSS/'

# ---------------------------------------------------------------- the changed rule, enumerating
def load_env(path='conj8-search.py'):
    src = open(HERE + path).read()
    src = src[:src.rindex("main()")]
    env = {}
    exec(compile(src, path, 'exec'), env)
    return env

def install_A(env):
    """replace sreds in env by the machine with Ms-FOpᴬ; teach the lookups the third kind"""
    S = env['S']; openRec, closeRec, TOP = env['openRec'], env['closeRec'], env['TOP']
    def lookup_eqv(G, x):
        for (y, c, t) in G:
            if y == x: return t if c == 'e' else (t[1] if c == 'p' else None)
        return None
    def lookup_sub(G, x):
        for (y, c, t) in G:
            if y == x: return t if c == 's' else (t[2] if c == 'p' else None)
        return None
    S.lookup_eqv = lookup_eqv
    env['lookup_sub'] = lookup_sub
    smemo = {}
    def sreds(G, s, t, k):
        key = (G, s, t, k)
        if key in smemo: return smemo[key]
        out = set()
        if not S.prevalid(G, s): smemo[key] = out; return out
        c = t[0]
        out.add(TOP)                                                           # Ms-Top
        out |= env['ereds'](G, s, t, k)                                        # Ms-Equ
        if c == 'f':
            b = lookup_sub(G, t[1])
            if b is not None: out.add(b)                                       # Ms-Pro, also at 'p'
        elif c == 'a':
            u, v = t[1], t[2]
            for up in sreds(G, (v,) + s, u, k): out.add(('a', up, v))          # Ms-App
        elif c == 'l':
            w, b = t[1], t[2]
            if not s:                                                          # Ms-Fun
                x = S.fresh(G, t)
                for r in sreds(((x, 's', w),) + G, (), openRec(0, ('f', x), b), k):
                    out.add(('l', w, closeRec(0, x, r)))
            else:                                                              # Ms-FOpᴬ
                al, rest = s[0], s[1:]; x = S.fresh(G, t, s)
                for r in sreds(((x, 'p', ('P', al, w)),) + G, rest, openRec(0, ('f', x), b), k):
                    out.add(('l', w, closeRec(0, x, r)))
        smemo[key] = out
        return out
    env['sreds'] = sreds; env['_smemoA'] = smemo

def clear(env):
    env['S']._memo.clear(); env['S']._elems[0] = 0
    env['_smemo'].clear(); env['_wfmemo'].clear()
    if '_smemoA' in env: env['_smemoA'].clear()
    for m in ('_wfd', '_reach', '_ecl'):
        if m in env: env[m].clear()
    gc.collect()

# ---------------------------------------------------------------- β anywhere, locally nameless
_n = [0]
def betas(t, openRec, closeRec):
    """all one-step ↦ reducts of a locally closed term"""
    c = t[0]
    if c == 'a':
        if t[1][0] == 'l': yield openRec(0, t[2], t[1][2])
        for r in betas(t[1], openRec, closeRec): yield ('a', r, t[2])
        for r in betas(t[2], openRec, closeRec): yield ('a', t[1], r)
    elif c == 'l':
        for r in betas(t[1], openRec, closeRec): yield ('l', r, t[2])
        _n[0] += 1; x = 'w%d' % _n[0]
        for r in betas(openRec(0, ('f', x), t[2]), openRec, closeRec):
            yield ('l', t[1], closeRec(0, x, r))

def top_applied(t):
    st = [t]
    while st:
        t = st.pop()
        if t[0] == 'a':
            if t[1] == ('T',): return True
            st += [t[1], t[2]]
        elif t[0] == 'l': st += [t[1], t[2]]
    return False

def lo_step(t, openRec):
    c = t[0]
    if c == 'a':
        if t[1][0] == 'l': return openRec(0, t[2], t[1][2])
        r = lo_step(t[1], openRec)
        if r is not None: return ('a', r, t[2])
        r = lo_step(t[2], openRec)
        if r is not None: return ('a', t[1], r)
    elif c == 'l':
        r = lo_step(t[1], openRec)
        if r is not None: return ('l', r, t[2])
        r = lo_step(t[2], openRec)
        if r is not None: return ('l', t[1], r)
    return None

def t3():
    """Theorem 3 and Lemma 1 at the machine level (no well-formedness) under A: the middle term
    m = (λx≤λ⊤.⊤. x) ⊤ is ill-formed (⊤ is not below λ⊤.⊤), ⊤ ⊲ m by one ⟶ᵉ step on the right,
    m ⊲ λ⊤.⊤ by Ms-App over Ms-FOpᴬ over Ms-Pro and then ⟶ᵉ, and ⊤ ⊲ λ⊤.⊤ fails"""
    O = load_env(); E = load_env(); install_A(E)
    TOP, A, L, B, show = E['TOP'], E['A'], E['L'], E['B'], E['show']
    a = L(TOP, TOP); m = A(L(a, B(0)), TOP)
    for name, env in (("as printed", O), ("under A", E)):
        print(f"{name}:  ⊤ ⊲ {show(m)}: {env['machine']((), (), TOP, m, 3, 6)};  {show(m)} ⊲ {show(a)}: "
              f"{env['machine']((), (), m, a, 3, 6)};  ⊤ ⊲ {show(a)}: {env['machine']((), (), TOP, a, 3, 6)};  "
              f"{show(m)} wf: {env['wf']((), m)}")

def small(maxsize):
    O = load_env(); E = load_env(); install_A(E)          # O: as printed (shares S; the patch is inert there)
    S = E['S']; show, showG0 = E['show'], E['showG']
    TOP, A, L, F, B = E['TOP'], E['A'], E['L'], E['F'], E['B']
    openRec, closeRec, tsize = E['openRec'], E['closeRec'], E['tsize']
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
    terms = E['gen_terms'](['y', 'z'], maxsize)
    print(len(ctxs), "contexts,", len(terms), "terms")
    st = collections.Counter(); rng = random.Random(1)
    import os
    shard, nshards = int(os.environ.get('A_SHARD', 0)), int(os.environ.get('A_NSHARDS', 1))
    for gi, G in enumerate(ctxs):
        if gi % nshards != shard: continue
        clear(O); clear(E)
        # well-formed contexts only (§15): every annotation well-formed in its tail, as printed
        if not all(O['wf'](G[i + 1:], b) for i, (_, _, b) in enumerate(G)): continue
        st['contexts'] += 1
        dn = S.dom(G)
        ts = [t for t in terms if S.fv(t) <= dn]
        wfO = [t for t in ts if O['wf'](G, t)]
        wfA = [t for t in ts if E['wf'](G, t)]
        sA = set(wfA)
        st['wf_old'] += len(wfO); st['wf_A'] += len(wfA)
        for t in wfO:
            if t not in sA: st['OLD-NOT-A'] += 1; print("OLD NOT A:", showG0(G), show(t))
        for t in wfA:
            if t not in set(wfO): st['A-only'] += 1
        # Theorem 11: a term convertible with ⊤ (or ⊤ applied) is below no abstraction
        for u in wfA:
            ecl = E['closure'](E['ereds'], G, (), u, 2, 3)
            if any(r == TOP or (r[0] == 'a' and top_applied(r) and r[1] == TOP) for r in ecl):
                if any(r[0] == 'l' for r in E['wsub_reach'](G, u, 5)):
                    st['T11-FAIL'] += 1; print("T11 FAIL:", showG0(G), show(u))
        # safety: closed well-formed terms under leftmost-outermost β
        if not G:
            for t in wfA:
                w = t
                for _ in range(60):
                    if top_applied(w): st['UNSAFE'] += 1; print("UNSAFE:", show(t), "⟶*", show(w)); break
                    w = lo_step(w, openRec)
                    if w is None or tsize(w) > 400: break
        # Lemma 6: every ↦-reduct of a well-formed term is well-formed (as printed, and under A)
        for name, env, wfs in (('old', O, wfO), ('A', E, wfA)):
            for t in wfs:
                for r in set(betas(t, openRec, closeRec)):
                    st['L6-%s-instances' % name] += 1
                    if not env['wf'](G, r):
                        st['L6-%s-FAIL' % name] += 1
                        if name == 'A' or st['L6-old-FAIL'] <= 20:
                            print("L6 %s FAIL:" % name, showG0(G), "|", show(t), "↦", show(r))
        # Conjecture 8 under A
        pairs = [(u, t) for u in wfA for t in wfA if u != t and E['wsub'](G, u, t, 5)]
        st['pairs'] += len(pairs)
        cos = [(('app', v),) for v in ts] + [(('fun', a),) for a in ts] \
            + [(('app', v), ('app', w)) for v in ts for w in ts if tsize(v) + tsize(w) <= 4] \
            + [(('fun', a), ('app', v)) for a in ts for v in ts if tsize(a) + tsize(v) <= 4]
        for (u, t) in pairs:
            for Co in cos:
                cu, ct = E['plugs'](Co, u), E['plugs'](Co, t)
                if not (E['wf'](G, cu) and E['wf'](G, ct)): continue
                st['C8-instances'] += 1
                if E['wsub'](G, cu, ct, 5): st['C8-wsub'] += 1
                elif E['machine'](G, (), cu, ct, 3, 4) or E['machine'](G, (), cu, ct, 3, 9): st['C8-machine-only'] += 1
                else:
                    st['C8-FAIL'] += 1
                    print("C8 FAIL:", showG0(G), "| u =", show(u), "| t =", show(t), "| Co[u] =", show(cu), "| Co[t] =", show(ct))
        # Theorem 3: two layers give one machine layer
        by_left = collections.defaultdict(list)
        for (u, t) in pairs: by_left[u].append(t)
        trip = [(u, m, t) for (u, m) in pairs for t in by_left.get(m, ()) if t != u]
        if len(trip) > 4000: trip = rng.sample(trip, 4000)
        for (u, m, t) in trip:
            st['T3-instances'] += 1
            if not E['machine'](G, (), u, t, 3, 4):
                if E['machine'](G, (), u, t, 3, 9): st['T3-longer-chain'] += 1; continue
                st['T3-FAIL'] += 1
                print("T3 FAIL:", showG0(G), "|", show(u), "≤", show(m), "≤", show(t),
                      "| as printed:", O['machine'](G, (), u, t, 3, 9))
        print(f"ctx {showG0(G)}: " + ", ".join(f"{k} {v}" for k, v in sorted(st.items())))
    print(dict(st))

# ---------------------------------------------------------------- the goal-directed checker under A
H = SourceFileLoader('hurkens', HERE + 'conj8-hurkens-probe.py').load_module()
unspine, openR, closeR, fresh, lookup = H.unspine, H.openRec, H.closeRec, H.fresh, H.lookup
Fuel, Tank, head_step, whnf, conv = H.Fuel, H.Tank, H.head_step, H.whnf, H.conv

class CheckerA(H.Checker):
    """the checker of conj8-hurkens-probe.py, with promotion through a redex (Ms-App over Ms-FOpᴬ)"""

    def prom(self, Gp, t):
        """one ⟶ˢ step promoting the variable at the head of t's spine, descending through
        consumed abstractions by Ms-FOpᴬ; Gp extends the checker's context by 'p' entries"""
        h, args = unspine(t)
        if h[0] == 'f':
            kb = lookup(Gp, h[1])
            if kb is None: return None
            if kb[0] == 's': return H.A(kb[1], *args)
            if kb[0] == 'p': return H.A(kb[1][1], *args)
            return None
        if h[0] == 'l' and args:
            x = fresh()
            r = self.prom(((x, 'p', (args[0], h[1])),) + Gp, H.A(openR(0, H.F(x), h[2]), *args[1:]))
            if r is None: return None
            for _ in args[1:]: r = r[1]
            return H.A(H.L(h[1], closeR(0, x, r)), *args)
        return None

    def promote_head(self, G, t):
        p = self.prom(G, t)
        if p is None: return None
        if not self.wf(G, t) or not self.wf(G, p): return None      # Ws-Lf2, both ends
        self.promotions += 1
        return p

    def dom(self, G, f):
        return self.domA(G, f, f, Tank(self.head_fuel))

    def domA(self, G, f, w, tank):
        h, args = unspine(w)
        if h[0] == 'l' and not args:
            if w is not f and not self.wf(G, w): return None
            if not self.wf(G, H.L(h[1], H.TOP)): return None
            return h[1]
        if h[0] == 'f':
            tank.use()
            p = self.promote_head(G, w)
            return None if p is None else self.domA(G, f, p, tank)
        if h[0] != 'l': return None
        tank.use()
        p = self.promote_head(G, w)                  # promote through the redex first …
        if p is not None:
            d = self.domA(G, f, p, tank)
            if d is not None: return d
        return self.domA(G, f, head_step(w), tank)   # … and contract it if that leads nowhere

    def sub(self, G, v, t):
        tank = Tank(self.head_fuel)
        tw = whnf(t, tank)
        if tw == H.TOP: return True
        return self.subA(G, v, t, tw, tank)

    def subA(self, G, v, t, tw, tank):
        while True:
            if v == t: return True
            h, args = unspine(v)
            if h[0] == 'l' and not args:
                if tw[0] != 'l': return conv(v, t)
                if not conv(h[1], tw[1]): return False
                x = fresh(); Gx = ((x, 's', h[1]),) + G
                bv, bt = openR(0, H.F(x), h[2]), openR(0, H.F(x), tw[2])
                if not self.wf(Gx, bt): return False
                return self.sub(Gx, bv, bt)
            if h[0] == 'f':
                th, targs = unspine(tw)
                if th == h and len(targs) == len(args) and conv(v, tw): return True
                tank.use()
                p = self.promote_head(G, v)
                if p is None: return False
                v = p; continue
            if h[0] == 'T': return conv(v, t)
            tank.use()
            p = self.promote_head(G, v)
            if p is not None and self.subA(G, p, t, tw, tank): return True
            v = head_step(v)

def validate(maxsize):
    """soundness of CheckerA against the enumerating A-oracle (wfd of conj8-depth-probe.py with
    sreds replaced), and that it accepts whatever the checker as printed accepts"""
    import os
    os.environ.setdefault('C8_SIZE', '14')
    argv = sys.argv; sys.argv = [argv[0], '0', '0', '1']
    env = load_env('conj8-depth-probe.py')
    sys.argv = argv
    install_A(env)
    wfd, S = env['wfd'], env['S']
    terms = env['gen_terms'](['y', 'z'], maxsize)
    n = collections.Counter()
    for G in env['contexts']():
        if any(k != 's' for (_, k, _) in G): continue
        clear(env)
        ck = CheckerA(head_fuel=200); ck0 = H.Checker(head_fuel=200)
        if not all(ck0.wf(G[i + 1:], b) for i, (_, _, b) in enumerate(G)): continue
        for t in terms:
            if not (S.lc(t) and S.fv(t) <= S.dom(G)): continue
            try: mine = ck.wf(G, t); old = ck0.wf(G, t)
            except Fuel: n['fuel'] += 1; continue
            theirs = wfd(G, t, 6)
            if old and not mine: n['PRINTED-NOT-A'] += 1; print("PRINTED NOT A:", env['showG'](G), H.show(t))
            if mine and not old: n['A-only'] += 1
            if mine and theirs: n['both'] += 1
            elif mine: n['CHECKER-ONLY'] += 1; print("CHECKER ONLY:", env['showG'](G), H.show(t))
            elif theirs: n['oracle-only'] += 1
    print("validate:", dict(n))

def hurkens(steps):
    ck = CheckerA(log=False)
    G = (); TOP = H.TOP; App = H.A
    Hx = H.PARADOX
    print("— what conj8-hurkens-probe.py checks, under A")
    for name, t in [("U", H.U), ("⊥", H.BOT), ("Δ", H.DELTA), ("Ω", H.OMEGA), ("φ₀", H.PHI0), ("R₀", H.R0),
                    ("M₀", H.M0), ("L₀", H.L0), ("¬φ₀", H.L0_TYPE), ("[L₀ R₀]", Hx), ("(¬φ₀) R₀", App(H.L0_TYPE, H.R0))]:
        print(f"{name}: size {H.tsize(t)}, wf {ck.wf(G, t)}")
    print("R₀ ≤ φ₀:", ck.sub(G, H.R0, H.PHI0), "  L₀ ≤ ¬φ₀:", ck.sub(G, H.L0, H.L0_TYPE))
    print("— the instance of Conjecture 8 (§22): u = L₀, t = ¬φ₀, context □ R₀")
    print("[L₀ R₀] ≤ (¬φ₀) R₀:", ck.sub(G, Hx, App(H.L0_TYPE, H.R0)))
    print("[L₀ R₀] ≤ ⊥:", ck.sub(G, Hx, H.BOT))
    print("— the instance of Lemma 6 (§23): t₆ = (λx≤¬φ₀. x R₀ ⊤) L₀ ↦ [L₀ R₀] ⊤")
    t6 = App(H.lam('x', H.L0_TYPE, App(H.F('x'), H.R0, TOP)), H.L0)
    print("t₆ wf:", ck.wf(G, t6), "  [L₀ R₀] ⊤ wf:", ck.wf(G, App(Hx, TOP)))
    print("— along head evaluation of [L₀ R₀]: the reduct wf, below ⊥, and wf when applied to ⊤")
    w = Hx
    for i in range(steps + 1):
        try:
            a, b, c = ck.wf(G, w), None, None
            if a: b = ck.sub(G, w, H.BOT); c = ck.wf(G, App(w, TOP))
            print(f"step {i}: size {H.tsize(w)}, wf {a}, ≤ ⊥ {b}, applied to ⊤ wf {c}")
        except Fuel:
            print(f"step {i}: size {H.tsize(w)}, out of fuel")
        w = head_step(w)
        if w is None: print("  a weak head normal form"); break
    print("promotions made:", ck.promotions, " wf judgements:", len(ck.wfmemo))

def safety(maxsize, fuel=60):
    S = SourceFileLoader('safety', HERE + 'conj8-safety-search.py')
    src = open(HERE + 'conj8-safety-search.py').read(); src = src[:src.rindex("main()")]
    env = {}; exec(compile(src, 'safety', 'exec'), env)
    for sz in range(1, maxsize + 1, 2):
        n = wf = wf0 = unsafe = 0
        ck = CheckerA(head_fuel=400); ck0 = H.Checker(head_fuel=400)
        for t in env['terms'](sz, 0):
            n += 1
            try:
                if ck0.wf((), t): wf0 += 1
                if not ck.wf((), t): continue
            except (Fuel, RecursionError, MemoryError): continue
            wf += 1
            w = t
            for _ in range(fuel):
                if env['bad'](w): unsafe += 1; print("  UNSAFE:", H.show(t), "⟶*", H.show(w)[:200]); break
                r = env['lo_step'](w)
                if r is None or H.tsize(r) > 3000: break
                w = r
            if len(ck.wfmemo) > 2000000: ck = CheckerA(head_fuel=400); ck0 = H.Checker(head_fuel=400)
        print(f"size {sz}: {n} closed terms, well-formed {wf0} as printed, {wf} under A, {unsafe} reach ⊤ in operator position")

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'hurkens'
    arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
    if mode == 'small': small(arg or 5)
    elif mode == 't3': t3()
    elif mode == 'validate': validate(arg or 5)
    elif mode == 'safety': safety(arg or 9)
    else: hurkens(arg if arg is not None else 15)
