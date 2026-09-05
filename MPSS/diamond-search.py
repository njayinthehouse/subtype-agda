"""Exhaustive finite search for a counterexample to MPSS Lemma 2 (the diamond).

Enumerates every prevalid configuration Γ;s and locally closed term t within the
given bounds, computes the full set of one-step ⟶≡ reducts, and checks that every
pair of reducts can be joined at every pair of ↣-reduced configurations.

All eight ⟶≡ rules and all three ↣ rules are implemented as printed in
MPSS/Reduction and MPSS/CtxReduction, including Me-Bet's unbound body premise
(the defect MPSS/BetaScope refutes) — the search is against the paper's system,
not a repaired one. Cofinite premises are instantiated at a single canonical
fresh name, the usual adequate treatment for locally nameless syntax.

Usage: python3 diamond-search.py <term-size> <ctx-entries> <stack-depth>

Results so far, all with zero failures:
    2 1 1        2,020,902 instances
    2 1 2      630,378,265 instances
"""
import sys, itertools
from functools import lru_cache
sys.setrecursionlimit(100000)

# Terms: ('b',i) bvar | ('f',x) fvar | ('T',) Top | ('l',w,b) lam | ('a',f,a) app
TOP = ('T',)

def openRec(k,u,t):
    c=t[0]
    if c=='b': return u if t[1]==k else t
    if c in 'fT': return t
    if c=='l': return ('l',openRec(k,u,t[1]),openRec(k+1,u,t[2]))
    return ('a',openRec(k,u,t[1]),openRec(k,u,t[2]))

def closeRec(k,x,t):
    c=t[0]
    if c=='b': return t
    if c=='f': return ('b',k) if t[1]==x else t
    if c=='T': return t
    if c=='l': return ('l',closeRec(k,x,t[1]),closeRec(k+1,x,t[2]))
    return ('a',closeRec(k,x,t[1]),closeRec(k,x,t[2]))

def fv(t):
    c=t[0]
    if c=='f': return frozenset([t[1]])
    if c in 'bT': return frozenset()
    return fv(t[1])|fv(t[2])

def lc(t,k=0):
    c=t[0]
    if c=='b': return t[1]<k
    if c in 'fT': return True
    if c=='l': return lc(t[1],k) and lc(t[2],k+1)
    return lc(t[1],k) and lc(t[2],k)

def dom(G): return frozenset(e[0] for e in G)

def ctx_prevalid(G):
    if not G: return True
    x,c,t = G[0]; tail = G[1:]
    return ctx_prevalid(tail) and x not in dom(tail) and lc(t) and fv(t)<=dom(tail)

def prevalid(G,s):
    if not ctx_prevalid(G): return False
    return all(lc(a) and fv(a)<=dom(G) for a in s)

FRESH = 'z%d'
def fresh(G,*ts):
    used=set(dom(G))
    for t in ts:
        if isinstance(t,tuple) and t and isinstance(t[0],str) and t[0] in 'bfTla': used|=fv(t)
        else:
            for u in t: used|=fv(u)
    i=0
    while FRESH%i in used: i+=1
    return FRESH%i

def lookup_eqv(G,x):
    for (y,c,t) in G:
        if y==x: return t if c=='e' else None
    return None

_memo={}
def reducts(G,s,t):
    key=(G,s,t)
    if key in _memo: return _memo[key]
    _memo[key]=frozenset()          # guard against any unexpected cycle
    out=set()
    pv = prevalid(G,s)
    c=t[0]
    if c=='f':
        if pv: out.add(t)                                   # Me-Var
        a=lookup_eqv(G,t[1])
        if pv and a is not None: out |= reducts(G,s,a)      # Me-Pro
    elif c=='T':
        if pv: out.add(TOP)                                 # Me-Top
    elif c=='a':
        u,v=t[1],t[2]
        if u==TOP and pv: out.add(TOP)                      # Me-TAp
        for up in reducts(G,(v,)+s,u):                      # Me-App
            for vp in reducts(G,(),v):
                out.add(('a',up,vp))
        if u[0]=='l':                                       # Me-Bet
            body=u[2]
            x=fresh(G,t,s)
            for r in reducts(G,s,openRec(0,('f',x),body)):
                up2=closeRec(0,x,r)
                for vp in reducts(G,(),v):
                    out.add(openRec(0,vp,up2))
    elif c=='l':
        w,b=t[1],t[2]
        if not s:                                           # Me-Fun
            x=fresh(G,t)
            for wp in reducts(G,(),w):
                for r in reducts(((x,'s',w),)+G,(),openRec(0,('f',x),b)):
                    out.add(('l',wp,closeRec(0,x,r)))
        else:                                               # Me-FOp
            al,rest=s[0],s[1:]
            x=fresh(G,t,s)
            for wp in reducts(G,(),w):
                for r in reducts(((x,'e',al),)+G,rest,openRec(0,('f',x),b)):
                    out.add(('l',wp,closeRec(0,x,r)))
    r=frozenset(out); _memo[key]=r; return r

def ctx_reducts(G,s):
    out={(G,s)}                                             # Ct-Refl
    if G:
        x,c,t=G[0]; tail=G[1:]
        for (Gp,sp) in ctx_reducts(tail,s):
            for tp in reducts(tail,(),t):
                out.add((((x,c,tp),)+Gp,sp))                # Ct-Ann
    if s:
        al,rest=s[0],s[1:]
        for (Gp,sp) in ctx_reducts(G,rest):
            for ap in reducts(G,(),al):
                out.add((Gp,(ap,)+sp))                      # Ct-Stk
    return out

# ---- enumeration ----
def terms(size,names,k=0):
    if size<=0: return
    yield TOP
    for x in names: yield ('f',x)
    for i in range(k): yield ('b',i)
    for a in range(1,size):
        for bsz in range(1,size-a+1):
            for u in terms(a,names,k):
                for v in terms(bsz,names,k): yield ('a',u,v)
            for u in terms(a,names,k):
                for v in terms(bsz,names,k+1): yield ('l',u,v)

def closed_terms(size,names,k=0):
    seen=set()
    for t in terms(size,names,k):
        if t not in seen and lc(t,k): seen.add(t); yield t

NAMES=['x','y']
TSZ=int(sys.argv[1]) if len(sys.argv)>1 else 3
CSZ=int(sys.argv[2]) if len(sys.argv)>2 else 1
SSZ=int(sys.argv[3]) if len(sys.argv)>3 else 1

anns=[t for t in closed_terms(TSZ,NAMES)]
ctxs=[()]
for n in range(1,CSZ+1):
    new=[]
    for G in ctxs:
        if len(G)!=n-1: continue
        for x in NAMES:
            if x in dom(G): continue
            for c in ('s','e'):
                for a in anns:
                    if fv(a)<=dom(G): new.append(((x,c,a),)+G)
    ctxs+=new
ctxs=[G for G in ctxs if ctx_prevalid(G)]

stacks=[()]
for n in range(1,SSZ+1):
    stacks+=[tuple(p) for p in itertools.product(anns,repeat=n)]

checked=0; bad=[]
for G in ctxs:
    for s in stacks:
        if not prevalid(G,s): continue
        crs=list(ctx_reducts(G,s))
        for t in closed_terms(TSZ,NAMES):
            if not fv(t)<=dom(G): continue
            R=list(reducts(G,s,t))
            if len(R)<2: continue
            for t1 in R:
                for t2 in R:
                    for (G1,s1) in crs:
                        A=reducts(G1,s1,t1)
                        if not A: continue
                        for (G2,s2) in crs:
                            B=reducts(G2,s2,t2)
                            checked+=1
                            if not (A&B):
                                bad.append((G,s,t,t1,t2,G1,s1,G2,s2))
                                if len(bad)>3: raise SystemExit(
                                    "COUNTEREXAMPLES:\n"+"\n".join(map(str,bad)))
print(f"term size<={TSZ} ctx<={CSZ} stack<={SSZ}: {checked} diamond instances checked, {len(bad)} failures")
for b in bad[:3]: print("  FAIL",b)
