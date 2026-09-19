"""Hurkens' paradox in MPSS (CONJ8.md §20, §21).

The term is transcribed from A. J. C. Hurkens, "A simplification of Girard's paradox" (TLCA 1995),
Section 3, p. 269, and Section 7, p. 277 (refs/hurkens95tlca.pdf). The encoding is the one CONJ8
§20 fixes:  Πx:A.B ↦ λx≤A.B,   λx:A.M ↦ λx≤A.M,   every sort ↦ ⊤,   M : A ↦ M ≤ A.

The enumerating checkers of the other probes (all reducts of a term, breadth first) were built
for terms of size 7; the paradox has about two thousand nodes. This file has a goal-directed
checker instead, which follows the typing derivation of the source:

  wf(G, t)       Wf-PrS, Wf-Top, Wf-Fun as they stand; Wf-App by dom and sub
  dom(G, f)      the d with f ≤*wf λx≤d.⊤ : promote the head variable of f to its bound and
                 β-reduce at the head until an abstraction λx≤d.b appears, then Ms-Fun over Ms-Top;
                 every promotion is between terms checked well-formed
  sub(G, v, t)   one Ws-Sub layer v ≤wf t : t ≡ ⊤ (Ms-Top); or v, t convertible (e-steps on both
                 sides to a common reduct); or both abstractions with convertible annotations and
                 the bodies related under the binder (Ms-Fun, Me-Fun); or v is headed by a
                 variable, which is promoted to its bound (the result checked well-formed) and the
                 comparison repeated; or v is headed by a redex, which is contracted (e-steps)

β at any position is two ⟶ᵉ steps (bind-and-unfold by Me-App over Me-FOp, then Me-Bet on the
closed body; MPSS/Prop17Chain), so conversion is comparison of β-normal forms with Me-TAp.
Normalization is only ever asked of type-level terms; every call has fuel, and running out is
reported, not silently taken for a no.

Soundness of the checker is cross-checked against the enumerating oracle wfd of
conj8-depth-probe.py on every small term (mode `validate`).

  python3 conj8-hurkens-probe.py validate [MAXSIZE]
  python3 conj8-hurkens-probe.py check
  python3 conj8-hurkens-probe.py head [STEPS]
"""
import sys, functools
sys.setrecursionlimit(1000000)
print = functools.partial(print, flush=True)

TOP = ('T',)
def B(i): return ('b', i)
def F(x): return ('f', x)
def L(a, b): return ('l', a, b)
def A(f, *vs):
    for v in vs: f = ('a', f, v)
    return f

class Fuel(Exception): pass
class Reject(Exception): pass

# ---------------------------------------------------------------- syntax, locally nameless
_open = {}
def openRec(k, v, t):
    c = t[0]
    if c == 'b': return v if t[1] == k else t
    if c in 'fT': return t
    key = (k, id(v), id(t))
    r = _open.get(key)
    if r is not None and r[0] is v and r[1] is t: return r[2]
    if c == 'l': res = ('l', openRec(k, v, t[1]), openRec(k + 1, v, t[2]))
    else:        res = ('a', openRec(k, v, t[1]), openRec(k, v, t[2]))
    _open[key] = (v, t, res)
    return res

def closeRec(k, x, t):
    c = t[0]
    if c == 'f': return ('b', k) if t[1] == x else t
    if c in 'bT': return t
    if c == 'l': return ('l', closeRec(k, x, t[1]), closeRec(k + 1, x, t[2]))
    return ('a', closeRec(k, x, t[1]), closeRec(k, x, t[2]))

def tsize(t):
    n = 0; st = [t]
    while st:
        t = st.pop(); n += 1
        if t[0] in 'la': st.append(t[1]); st.append(t[2])
    return n

_ctr = [0]
def fresh():
    _ctr[0] += 1
    return f"_{_ctr[0]}"

def lookup(G, x):
    for (y, k, b) in G:
        if y == x: return (k, b)
    return None

def unspine(t):
    args = []
    while t[0] == 'a': args.append(t[2]); t = t[1]
    return t, args[::-1]

# ---------------------------------------------------------------- β with Me-TAp, fuelled
class Tank:
    def __init__(self, n): self.n = n
    def use(self):
        self.n -= 1
        if self.n < 0: raise Fuel()

def head_step(t):
    """one head step of t, or None: β at the head, or ⊤ u ⟶ ⊤"""
    h, args = unspine(t)
    if not args: return None
    if h[0] == 'l': return A(openRec(0, args[0], h[2]), *args[1:])
    if h[0] == 'T': return A(TOP, *args[1:])
    return None

def whnf(t, tank):
    while True:
        r = head_step(t)
        if r is None: return t
        tank.use(); t = r

_nf = {}
def nf(t, tank):
    """β-normal form; binders are opened with fresh names so that the memo is on closed shapes"""
    r = _nf.get(t)
    if r is not None: return r
    w = whnf(t, tank)
    h, args = unspine(w)
    if h[0] == 'l':
        x = fresh()
        body = nf(openRec(0, F(x), h[2]), tank)
        res = ('l', nf(h[1], tank), closeRec(0, x, body))
    else:
        res = h
    for a in args: res = ('a', res, nf(a, tank))
    _nf[t] = res
    return res

NF_FUEL = 200000
def conv(a, b):
    if a == b: return True
    tank = Tank(NF_FUEL)
    return nf(a, tank) == nf(b, tank)

# ---------------------------------------------------------------- the checker
class Checker:
    def __init__(self, head_fuel=2000, log=False):
        self.wfmemo = {}; self.head_fuel = head_fuel; self.log = log
        self.promotions = 0; self.maxterm = 0

    def wf(self, G, t):
        key = (G, t)
        r = self.wfmemo.get(key)
        if r is not None: return r
        self.wfmemo[key] = False          # a cyclic demand is a failure
        c = t[0]
        if c == 'T': res = True
        elif c == 'f': res = lookup(G, t[1]) is not None
        elif c == 'b': res = False
        elif c == 'l':
            x = fresh()
            res = self.wf(G, t[1]) and self.wf(((x, 's', t[1]),) + G, openRec(0, F(x), t[2]))
        else:
            res = False
            if self.wf(G, t[1]) and self.wf(G, t[2]):
                d = self.dom(G, t[1])
                res = d is not None and self.sub(G, t[2], d)
        self.wfmemo[key] = res
        if not res and self.log: print("  not wf:", show(t)[:200])
        return res

    def promote_head(self, G, t):
        """t = x args with x ≤ b in G: the promotion x args ⟶ˢ b args (Ms-App over Ms-Pro), if
        x args and b args are both well-formed; None otherwise"""
        h, args = unspine(t)
        if h[0] != 'f': return None
        kb = lookup(G, h[1])
        if kb is None or kb[0] != 's': return None
        p = A(kb[1], *args)
        # Ws-Lf2 asks both ends of a promotion to be well-formed; the source may be an
        # e-reduct of a well-formed term, which is not known to be well-formed (Lemma 6)
        if not self.wf(G, t): return None
        if not self.wf(G, p): return None
        self.promotions += 1
        return p

    def dom(self, G, f):
        """d with f ≤*wf λx≤d.⊤ (f already checked well-formed)"""
        tank = Tank(self.head_fuel)
        w = f
        while True:
            h, args = unspine(w)
            if h[0] == 'l' and not args:
                # λd.b ⟶ˢ λd.⊤ between well-formed terms
                if w is not f and not self.wf(G, w): return None
                if not self.wf(G, L(h[1], TOP)): return None
                return h[1]
            if h[0] == 'f':
                w = self.promote_head(G, w)
                if w is None: return None
                continue
            r = head_step(w)
            if r is None: return None          # ⊤, or ⊤ applied: below no abstraction (Theorem 11)
            tank.use(); w = r

    def sub(self, G, v, t):
        """one layer v ≤wf t, for v and t already checked well-formed"""
        tank = Tank(self.head_fuel)
        tw = whnf(t, tank)
        if tw == TOP: return True
        while True:
            if v == t: return True
            h, args = unspine(v)
            if h[0] == 'l' and not args:
                if tw[0] != 'l': return conv(v, t)
                if not conv(h[1], tw[1]): return False
                x = fresh(); Gx = ((x, 's', h[1]),) + G
                bv, bt = openRec(0, F(x), h[2]), openRec(0, F(x), tw[2])
                # the right body is well-formed under x ≤ (its own annotation); under the
                # convertible annotation of v it is checked again
                if not self.wf(Gx, bt): return False
                return self.sub(Gx, bv, bt)
            if h[0] == 'f':
                th, targs = unspine(tw)
                if th == h and len(targs) == len(args) and conv(v, tw): return True
                p = self.promote_head(G, v)
                if p is None: return False
                v = p; continue
            if h[0] == 'T': return conv(v, t)
            r = head_step(v)                   # a redex at the head: contract it
            tank.use(); v = r

# ---------------------------------------------------------------- printing
def show(t, names=()):
    c = t[0]
    if c == 'T': return '⊤'
    if c == 'f': return str(t[1])
    if c == 'b': return names[t[1]] if t[1] < len(names) else f"#{t[1]}"
    if c == 'l':
        x = f"v{len(names)}"
        return f"(λ{x}≤{show(t[1], names)}. {show(t[2], (x,) + names)})"
    return f"({show(t[1], names)} {show(t[2], names)})"

# ---------------------------------------------------------------- Hurkens' term
# Named syntax for transcription, closed into locally nameless at the end.
def lam(x, ann, body): return L(ann, closeRec(0, x, body))
Pi = lam
def arrow(a, b): return L(a, b)                     # a → b, the codomain not mentioning the binder

def P(S): return arrow(S, TOP)                      # ℘S ≡ (S → *)
BOT = Pi('p', TOP, F('p'))                          # ⊥ ≡ ∀p:*.p
def neg(phi): return arrow(phi, BOT)                # ¬φ ≡ [φ ⇒ ⊥]

# U ≡ ΠX:□.((℘℘X → X) → ℘℘X)
U = Pi('X', TOP, arrow(arrow(P(P(F('X'))), F('X')), P(P(F('X')))))

def tau(t):
    # τt ≡ ΛX:□. λf:(℘℘X→X). λp:℘X. (t λx:U.(p (f ({x X} f))))
    X, f, p, x = F('X'), F('f'), F('p'), F('x')
    inner = lam('x', U, A(p, A(f, A(x, X, f))))
    return lam('X', TOP, lam('f', arrow(P(P(X)), X), lam('p', P(X), A(t, inner))))

def sigma(s):
    # σs ≡ ({s U} λt:℘℘U.τt)
    return A(s, U, lam('t', P(P(U)), tau(F('t'))))

def tausigma(s): return tau(sigma(s))

# Δ ≡ λy:U.¬∀p:℘U.[(σy p) ⇒ (p τσy)]
DELTA = lam('y', U, neg(Pi('p', P(U), arrow(A(sigma(F('y')), F('p')), A(F('p'), tausigma(F('y')))))))

# Ω ≡ τ λp:℘U.∀x:U.[(σx p) ⇒ (p x)]          (Hurkens takes its normal form; see `omega_nf`)
OMEGA_RAW = tau(lam('p', P(U), Pi('x', U, arrow(A(sigma(F('x')), F('p')), A(F('p'), F('x'))))))

def omega_nf():
    # Ω ≡ ΛX:□.λf:(℘℘X→X).λp:℘X.∀x:U.[(σx λy:U.(p (f ({y X} f)))) ⇒ (p (f ({x X} f)))]
    X, f, p, x, y = F('X'), F('f'), F('p'), F('x'), F('y')
    inner = lam('y', U, A(p, A(f, A(y, X, f))))
    body = Pi('x', U, arrow(A(sigma(x), inner), A(p, A(f, A(x, X, f)))))
    return lam('X', TOP, lam('f', arrow(P(P(X)), X), lam('p', P(X), body)))
OMEGA = omega_nf()

def lam_y_p_tausigma_y(p):          # λy:U.(p τσy)
    return lam('y', U, A(p, tausigma(F('y'))))

# φ₀ ≡ ∀p:℘U.[∀x:U.[(σx p) ⇒ (p x)] ⇒ (p Ω)]
PHI0 = Pi('p', P(U), arrow(Pi('x', U, arrow(A(sigma(F('x')), F('p')), A(F('p'), F('x')))), A(F('p'), OMEGA)))

# R₀ ≡ let p:℘U. suppose 1:∀x:U.[(σx p) ⇒ (p x)]. [⟨1 Ω⟩ let x:U.⟨1 τσx⟩]
R0 = lam('p', P(U), lam('h1', Pi('x', U, arrow(A(sigma(F('x')), F('p')), A(F('p'), F('x')))),
         A(F('h1'), OMEGA, lam('x', U, A(F('h1'), tausigma(F('x')))))))

# M₀ ≡ let x:U. suppose 2:(σx Δ). suppose 3:∀p:℘U.[(σx p) ⇒ (p τσx)].
#        [[⟨3 Δ⟩ 2] let p:℘U.⟨3 λy:U.(p τσy)⟩]
M0 = lam('x', U, lam('h2', A(sigma(F('x')), DELTA),
         lam('h3', Pi('p', P(U), arrow(A(sigma(F('x')), F('p')), A(F('p'), tausigma(F('x'))))),
             A(F('h3'), DELTA, F('h2'), lam('p', P(U), A(F('h3'), lam_y_p_tausigma_y(F('p'))))))))

# L₀ ≡ suppose 0:φ₀. [[⟨0 Δ⟩ M₀] let p:℘U.⟨0 λy:U.(p τσy)⟩]
L0_BODY = A(F('h0'), DELTA, M0, lam('p', P(U), A(F('h0'), lam_y_p_tausigma_y(F('p')))))
L0 = lam('h0', PHI0, L0_BODY)
L0_TYPE = arrow(PHI0, BOT)                          # ¬φ₀
PARADOX = A(L0, R0)                                 # [L₀ R₀] : ⊥

# ---------------------------------------------------------------- modes
def validate(maxsize):
    """soundness of the checker against the enumerating oracle, on all terms up to maxsize"""
    import os
    os.environ.setdefault('C8_SIZE', '14')
    argv = sys.argv; sys.argv = [argv[0], '0', '0', '1']
    src = open('/home/egret/gimmick/1/MPSS/conj8-depth-probe.py').read()
    src = src[:src.rindex("main()")]
    env = {}
    exec(compile(src, 'c8d', 'exec'), env)
    sys.argv = argv
    wfd, gen_terms, contexts, S = env['wfd'], env['gen_terms'], env['contexts'], env['S']
    terms = gen_terms(['y', 'z'], maxsize)
    terms = [t for ts in terms.values() for t in ts] if isinstance(terms, dict) else list(terms)
    agree = mine_only = oracle_only = 0
    for G in contexts():
        if any(k != 's' for (_, k, _) in G): continue          # the checker reads ≤ entries only
        ck = Checker(head_fuel=200)
        for m in (env['_wfd'], env['_reach'], env['_ecl']): m.clear()
        ok_ctx = all(ck.wf(G[i + 1:], b) for i, (_, _, b) in enumerate(G))
        for t in terms:
            if not (S.lc(t) and S.fv(t) <= S.dom(G)): continue
            try: mine = ck.wf(G, t)
            except Fuel: continue
            theirs = wfd(G, t, 6)
            if mine and theirs: agree += 1
            elif mine:
                mine_only += 1
                print("CHECKER ONLY", env['showG'](G), show(t), "(context annotations wf: %s)" % ok_ctx)
            elif theirs: oracle_only += 1
    print(f"validate: both {agree}, checker only {mine_only}, oracle only {oracle_only}")

def check():
    ck = Checker(log=True)
    G = ()
    items = [("U", U), ("⊥", BOT), ("Δ", DELTA), ("Ω", OMEGA), ("φ₀", PHI0), ("R₀", R0), ("M₀", M0),
             ("L₀", L0), ("¬φ₀", L0_TYPE), ("[L₀ R₀]", PARADOX), ("(¬φ₀) R₀", A(L0_TYPE, R0))]
    for name, t in items:
        print(f"{name}: size {tsize(t)}, wf {ck.wf(G, t)}")
    print("Ω is the normal form of τ λp.…:", nf(OMEGA_RAW, Tank(NF_FUEL)) == OMEGA)
    print("Δ ≤ ℘U:", ck.sub(G, DELTA, P(U)))
    print("Ω ≤ U:", ck.sub(G, OMEGA, U))
    print("R₀ ≤ φ₀:", ck.sub(G, R0, PHI0))
    print("L₀ ≤ ¬φ₀:", ck.sub(G, L0, L0_TYPE))
    print("(¬φ₀) R₀ ⟶ᵉ* ⊥:", nf(A(L0_TYPE, R0), Tank(NF_FUEL)) == BOT)
    print("promotions made:", ck.promotions, " wf judgements:", len(ck.wfmemo))

def head(steps):
    """head reduction of [L₀ R₀]: the shape of the head at every step"""
    t = PARADOX; seen = {}
    for i in range(steps + 1):
        h, args = unspine(t)
        kind = {'l': 'λ', 'T': '⊤', 'f': 'var', 'b': 'bvar'}[h[0]]
        print(f"step {i}: head {kind}, {len(args)} operands, size {tsize(t)}")
        if h[0] != 'l' or not args:
            print("  a weak head normal form"); return
        t = head_step(t)
    print(f"no weak head normal form within {steps} head steps")

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if mode == 'validate': validate(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
    elif mode == 'head': head(int(sys.argv[2]) if len(sys.argv) > 2 else 60)
    else: check()
