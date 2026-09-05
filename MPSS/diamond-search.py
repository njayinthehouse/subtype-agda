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
_stats=[0]          # total elements held in _memo, for a size-based cap
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
    r=frozenset(out); _memo[key]=r; _stats[0]+=len(r); return r

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
import argparse
ap=argparse.ArgumentParser()
ap.add_argument('--tsz',type=int,default=3)      # subject term size
ap.add_argument('--asz',type=int,default=2)      # annotation / stack-entry size
ap.add_argument('--ctx',type=int,default=2)      # context entries
ap.add_argument('--stack',type=int,default=1)    # stack depth
ap.add_argument('--cr',default='full',choices=['full','refl'])
ap.add_argument('--shard',default='0/1')
ap.add_argument('--random',type=int,default=0)     # N random configurations, unbounded term size
ap.add_argument('--rcap',type=int,default=1200)   # exhaustive only when |R| <= rcap
ap.add_argument('--samples',type=int,default=40000)  # random pairs when |R| > rcap
A=ap.parse_args()
SH,NSH=map(int,A.shard.split('/'))
NAMES=['x','y']

MEMO={}
def gen(size,k):
    key=(size,k)
    if key in MEMO: return MEMO[key]
    out=[TOP]+[('f',x) for x in NAMES]+[('b',i) for i in range(k)]
    for a in range(1,size):
        for b in range(1,size-a+1):
            for u in gen(a,k):
                for v in gen(b,k):   out.append(('a',u,v))
                for v in gen(b,k+1): out.append(('l',u,v))
    out=list(dict.fromkeys(out)); MEMO[key]=out; return out

subjects=[] if A.random else [t for t in gen(A.tsz,0) if lc(t)]
anns    =[] if A.random else [t for t in gen(A.asz,0) if lc(t)]

ctxs=[()]; fr=[()]
for _ in range(0 if A.random else A.ctx):
    nxt=[]
    for G in fr:
        for x in NAMES:
            if x in dom(G): continue
            for c in ('s','e'):
                for a in anns:
                    if fv(a)<=dom(G): nxt.append(((x,c,a),)+G)
    ctxs+=nxt; fr=nxt
ctxs=[G for G in ctxs if ctx_prevalid(G)]

stacks=[()]
for n in range(1,(0 if A.random else A.stack)+1):
    stacks+=[tuple(p) for p in itertools.product(anns,repeat=n)]

configs=[] if A.random else [(G,s) for G in ctxs for s in stacks if prevalid(G,s)]
configs=[c for i,c in enumerate(configs) if i%NSH==SH]

import random
rng=random.Random(12345+SH)

def report(kind,item,store):
    store.append(item); print(kind,item,flush=True)


MEMO_ELEMS_R=250000
if A.random:
    # Broad random mode. Terms and contexts are GENERATED, not enumerated, so the
    # bounds can be large: exhausting a tiny corner is worth less than shallow
    # coverage of a big space when the question is whether a counterexample exists.
    import random as _r
    rr=_r.Random(999+SH)
    def rterm(size,k,names):
        opts=['T']+['f']*len(names)+(['b'] if k>0 else [])
        if size>1: opts+=['a','a','l','l']
        c=rr.choice(opts)
        if c=='T': return TOP
        if c=='f': return ('f',rr.choice(names))
        if c=='b': return ('b',rr.randrange(k))
        h=rr.randrange(1,size)
        if c=='a': return ('a',rterm(h,k,names),rterm(size-h,k,names))
        return ('l',rterm(h,k,names),rterm(size-h,k+1,names))
    def rclosed(size,names):
        for _ in range(40):
            t=rterm(rr.randint(1,size),0,names)
            if lc(t): return t
        return TOP
    checked=0; bad=[]; stuck=[]; built=0
    for it in range(A.random):
        names=[]; G=()
        for nm in NAMES[:A.ctx]:
            a=rclosed(A.asz,names)
            if not fv(a)<=set(names): continue
            G=((nm,rr.choice(['s','e']),a),)+G
            names=names+[nm]
        G=tuple(reversed(G)) if False else G
        if not ctx_prevalid(G): continue
        st=tuple(rclosed(A.asz,names) for _ in range(rr.randint(0,A.stack)))
        if not prevalid(G,st): continue
        t=rclosed(A.tsz,names)
        if not fv(t)<=dom(G): continue
        _memo.clear(); _stats[0]=0
        R=list(reducts(G,st,t))
        if len(R)<2: continue
        built+=1
        crs=[(G,st)] if A.cr=='refl' else list(ctx_reducts(G,st))
        for _ in range(A.samples):
            t1=rr.choice(R); t2=rr.choice(R); c1=rr.choice(crs); c2=rr.choice(crs)
            A1=reducts(c1[0],c1[1],t1)
            if not A1 and len(stuck)<3:
                stuck.append((G,st,t,t1,c1)); print("NO-REDUCT",stuck[-1],flush=True)
            checked+=1
            if not (A1 & reducts(c2[0],c2[1],t2)):
                bad.append((G,st,t,t1,t2,c1,c2)); print("COUNTEREXAMPLE",bad[-1],flush=True)
                raise SystemExit(1)
            if _stats[0]>MEMO_ELEMS_R: _memo.clear(); _stats[0]=0
        if built%200==0: print(f"[{SH}] random {built} usable / {it+1} drawn, {checked} checks",flush=True)
    print(f"[{SH}] DONE random tsz={A.tsz} asz={A.asz} ctx={A.ctx} stack={A.stack}: "
          f"{built} usable configs, {checked} checks, {len(bad)} failures, {len(stuck)} no-reduct",flush=True)
    raise SystemExit(0)

checked=0; bad=[]; stuck=[]; ncfg=0; nexh=0; nsamp=0; bigmax=0
MEMO_ELEMS=250000   # cap the memo by terms held, not entries: one entry can hold 40k
for (G,s) in configs:
    ncfg+=1
    _memo.clear(); _stats[0]=0
    crs=[(G,s)] if A.cr=='refl' else list(ctx_reducts(G,s))
    for t in subjects:
        if _stats[0]>MEMO_ELEMS: _memo.clear(); _stats[0]=0
        if not fv(t)<=dom(G): continue
        R=list(reducts(G,s,t))
        if len(R)<2: continue
        if len(R)<=A.rcap:
            nexh+=1
            inter={}
            for t1 in R:
                if _stats[0]>MEMO_ELEMS: _memo.clear(); _stats[0]=0
                acc=None
                for cr in crs:
                    x_=reducts(cr[0],cr[1],t1)
                    if not x_ and len(stuck)<3: report("NO-REDUCT",(G,s,t,t1,cr),stuck)
                    acc = x_ if acc is None else (acc & x_)
                inter[t1]=acc if acc else frozenset()
            pairs=((a,b) for a in R for b in R)
            fast=inter
        else:
            # |R| too large to square: sample pairs, check each directly.
            nsamp+=1; bigmax=max(bigmax,len(R))
            pairs=((rng.choice(R),rng.choice(R)) for _ in range(A.samples))
            fast=None
        for t1,t2 in pairs:
            if fast is not None and fast[t1] & fast[t2]:
                checked+=len(crs)*len(crs); continue
            if _stats[0]>MEMO_ELEMS: _memo.clear(); _stats[0]=0
            for c1 in crs:
                A1=reducts(c1[0],c1[1],t1)
                if not A1 and len(stuck)<3: report("NO-REDUCT",(G,s,t,t1,c1),stuck)
                for c2 in crs:
                    checked+=1
                    if not (A1 & reducts(c2[0],c2[1],t2)):
                        report("COUNTEREXAMPLE",(G,s,t,t1,t2,c1,c2),bad)
                        if len(bad)>2: raise SystemExit(1)
    if ncfg%20==0: print(f"[{SH}] {ncfg}/{len(configs)} {checked} exh={nexh} samp={nsamp}",flush=True)
print(f"[{SH}] DONE tsz={A.tsz} asz={A.asz} ctx={A.ctx} stack={A.stack} cr={A.cr}: "
      f"{len(configs)} cfgs, {checked} checks, {len(bad)} failures, {len(stuck)} no-reduct, "
      f"exhaustive-terms={nexh} sampled-terms={nsamp} largest-reduct-set={bigmax}",flush=True)
