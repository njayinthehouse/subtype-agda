"""Does every strongly normalizing term that Figure 4 accepts satisfy the stack-reading judgement
of MPSS/StackWf (CONJ8.md §27, open question)?  A search for a counterexample among closed terms.

Figure 4: the goal-directed checker of conj8-hurkens-probe.py (validated there against the
enumerating oracle). The stack-reading judgement, goal-directed, in SUBSTITUTED form: where Wc-FOp
binds x ≡ δ, the operand is substituted. MPSS/StackWfSubst proves "wfˢ with the entry" implies
"wfˢ substituted", so a term this checker rejects for a reason that is not lack of fuel is a
candidate for not being wfˢ; every report is to be analysed by hand.

    wfC(G, s, ⊤)          always
    wfC(G, s, x)          if the bound of x is wfC at s                       (Wc-PrS)
    wfC(G, [], λx≤t.u)    if t is wfC at [] and u is under x ≤ t              (Wc-Fun)
    wfC(G, δ∷s, λx≤t.u)   if t is wfC at [] and u[δ] is wfC at s              (Wc-FOp, substituted)
    wfC(G, s, u v)        if u is wfC at v∷s, v at [], and with d the domain the head of u reaches
                          by promotion and head β: d wfC at [], v ≤ d          (Wc-App)

≤ is the machine relation in one layer (Theorem 3), with no side conditions on the terms between.

Strong normalization is approximated: leftmost-outermost and leftmost-innermost β both reach a
normal form within FUEL steps.

  python3 conj8-C-agree.py MAXSIZE [FUEL]      shards by the environment: AG_SHARD, AG_NSHARDS
"""
import sys, os, functools
from importlib.machinery import SourceFileLoader
sys.setrecursionlimit(1000000)
print = functools.partial(print, flush=True)
HERE = '/home/egret/gimmick/1/MPSS/'
H = SourceFileLoader('hurkens', HERE + 'conj8-hurkens-probe.py').load_module()
TOP, B, L = H.TOP, H.B, H.L
unspine, openR, Fuel, Tank = H.unspine, H.openRec, H.Fuel, H.Tank

class Machine(H.Checker):
    """the machine relation alone: promotions carry no well-formedness conditions"""
    def wf(self, G, t): return True
    def promote_head(self, G, t):
        h, args = unspine(t)
        if h[0] != 'f': return None
        kb = H.lookup(G, h[1])
        if kb is None or kb[0] != 's': return None
        return H.A(kb[1], *args)

class StackWf:
    def __init__(self, fuel=400):
        self.m = Machine(head_fuel=fuel); self.memo = {}; self.depth = 0
    def wf(self, G, s, t):
        # a derivation that follows a diverging evaluation has no end: bound the depth
        self.depth += 1
        try:
            if self.depth > 1500: raise Fuel()
            return self.wf1(G, s, t)
        finally:
            self.depth -= 1
    def wf1(self, G, s, t):
        key = (G, s, t)
        r = self.memo.get(key)
        if r is not None: return r
        self.memo[key] = False
        c = t[0]
        if c == 'T': res = True
        elif c == 'b': res = False
        elif c == 'f':
            kb = H.lookup(G, t[1])
            res = kb is not None and self.wf(G, s, kb[1])
        elif c == 'l':
            res = self.wf(G, (), t[1])
            if res:
                if not s:
                    x = H.fresh()
                    res = self.wf(((x, 's', t[1]),) + G, (), openR(0, H.F(x), t[2]))
                else:
                    res = self.wf(G, s[1:], openR(0, s[0], t[2]))
        else:
            u, v = t[1], t[2]
            res = False
            if self.wf(G, (v,) + s, u) and self.wf(G, (), v):
                d = self.m.dom(G, u)
                res = d is not None and self.wf(G, (), d) and self.m.sub(G, v, d)
        self.memo[key] = res
        return res

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

def lo_step(t):
    c = t[0]
    if c == 'a':
        if t[1][0] == 'l': return openR(0, t[2], t[1][2])
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

def li_step(t):
    """leftmost-innermost: a redex is contracted only when its parts are normal"""
    c = t[0]
    if c == 'a':
        r = li_step(t[1])
        if r is not None: return ('a', r, t[2])
        r = li_step(t[2])
        if r is not None: return ('a', t[1], r)
        if t[1][0] == 'l': return openR(0, t[2], t[1][2])
    elif c == 'l':
        r = li_step(t[1])
        if r is not None: return ('l', r, t[2])
        r = li_step(t[2])
        if r is not None: return ('l', t[1], r)
    return None

def normalizes(t, step, fuel):
    for _ in range(fuel):
        r = step(t)
        if r is None: return True
        if H.tsize(r) > 2000: return False
        t = r
    return False

def main():
    maxsize = int(sys.argv[1]); fuel = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    shard, nshards = int(os.environ.get('AG_SHARD', 0)), int(os.environ.get('AG_NSHARDS', 1))
    for sz in range(1, maxsize + 1, 2):
        n = fig4 = both = conly = ponly = ponly_sn = skipped = 0
        ck = H.Checker(head_fuel=400); sw = StackWf()
        for i, t in enumerate(terms(sz, 0)):
            if i % nshards != shard: continue
            n += 1
            try:
                p = ck.wf((), t); c = sw.wf((), (), t)
            except (Fuel, RecursionError, MemoryError):
                skipped += 1; continue
            if p: fig4 += 1
            if p and c: both += 1
            elif c: conly += 1
            elif p:
                ponly += 1
                sn = normalizes(t, lo_step, fuel) and normalizes(t, li_step, fuel)
                if sn: ponly_sn += 1
                print(("  FIGURE 4 ONLY, NORMALIZING: " if sn else "  figure 4 only, not normalizing: ") + H.show(t))
            if len(ck.wfmemo) > 1500000: ck = H.Checker(head_fuel=400)
            if len(sw.memo) > 1500000: sw = StackWf()
        print(f"size {sz}: {n} closed terms, Figure 4 {fig4}, both {both}, stack-reading only {conly}, "
              f"Figure 4 only {ponly} (normalizing {ponly_sn}), out of fuel {skipped}")

main()
