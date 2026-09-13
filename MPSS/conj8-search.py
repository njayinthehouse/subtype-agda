"""Counterexample search for MPSS Conjecture 8 (well-subtyping is context independent).

Hypotheses are checked soundly (well-formedness side conditions included, chains bounded);
the conclusion Co[u] ≤*wf Co[t] is tested through the weaker machine relation Co[u] ⊲ Co[t]
(u ⟶ˢ* a ⟵ᵉ* t, no side conditions) with a cap, so a reported failure is a candidate, not a
refutation, until analysed by hand.
"""
import sys, random, itertools, collections, gc
sys.setrecursionlimit(20000)
from importlib.machinery import SourceFileLoader
S=SourceFileLoader('dsc','/home/egret/gimmick/1/MPSS/diamond-search-capped.py').load_module()
TOP=S.TOP; A,L,F,B=S.A,S.L,S.F,S.B; openRec=S.openRec; closeRec=S.closeRec
show,showG=S.show,S.showG

def tsize(t):
    c=t[0]
    if c in 'bfT': return 1
    return 1+tsize(t[1])+tsize(t[2])

def lookup_sub(G,x):
    for (y,c,t) in G:
        if y==x: return t if c=='s' else None
    return None

# ---- one-step relations with a promotion cap k ----
def ereds(G,s,t,k): return S.reducts(G,s,t,k)      # ⟶ᵉ
_smemo={}
def sreds(G,s,t,k):
    """⟶ˢ one-step reducts"""
    key=(G,s,t,k)
    if key in _smemo: return _smemo[key]
    out=set()
    if not S.prevalid(G,s): _smemo[key]=out; return out
    c=t[0]
    out.add(TOP)                                           # Ms-Top
    out|=ereds(G,s,t,k)                                    # Ms-Equ
    if c=='f':
        b=lookup_sub(G,t[1])
        if b is not None: out.add(b)                       # Ms-Pro
    elif c=='a':
        u,v=t[1],t[2]
        for up in sreds(G,(v,)+s,u,k): out.add(('a',up,v))  # Ms-App
    elif c=='l':
        w,b=t[1],t[2]
        if not s:                                          # Ms-Fun
            x=S.fresh(G,t)
            for r in sreds(((x,'s',w),)+G,(),openRec(0,('f',x),b),k): out.add(('l',w,closeRec(0,x,r)))
        else:                                              # Ms-FOp
            al,rest=s[0],s[1:]; x=S.fresh(G,t,s)
            for r in sreds(((x,'e',al),)+G,rest,openRec(0,('f',x),b),k): out.add(('l',w,closeRec(0,x,r)))
    _smemo[key]=out; return out

SIZE=18
def closure(step,G,s,t,k,depth):
    """terms reachable by ≤depth steps, sizes capped"""
    seen={t}; frontier=[t]
    for _ in range(depth):
        nxt=[]
        for a in frontier:
            for b in step(G,s,a,k):
                if b not in seen and tsize(b)<=SIZE: seen.add(b); nxt.append(b)
        frontier=nxt
        if not frontier: break
    return seen

def machine(G,s,u,t,k,depth):
    """u ⊲ t at Γ;s : ∃a. u ⟶ˢ* a ⟵ᵉ* t (capped)"""
    return bool(closure(sreds,G,s,u,k,depth) & closure(ereds,G,s,t,k,depth))

# ---- well-formedness (sound, bounded) ----
WK=2; WD=3
_wfmemo={}
def wf(G,t,fuel=6):
    key=(G,t)
    if key in _wfmemo: return _wfmemo[key]
    if fuel<=0: return False
    _wfmemo[key]=False
    res=False
    if not S.ctx_prevalid(G) or not S.lc(t) or not S.fv(t)<=S.dom(G): res=False
    else:
        c=t[0]
        if c=='f': res=any(y==t[1] for (y,_,_) in G)
        elif c=='T': res=True
        elif c=='l':
            w,b=t[1],t[2]; x=S.fresh(G,t)
            res=wf(G,w,fuel-1) and wf(((x,'s',w),)+G,openRec(0,('f',x),b),fuel-1)
        else:
            u,v=t[1],t[2]
            # u ≤*wf λt''.Top  and  v ≤*wf t''   (Ws-Sub: both ends well-formed)
            if wf(G,u,fuel-1) and wf(G,v,fuel-1):
                for a in wsub_reach(G,u,fuel-1):
                    if a[0]=='l':
                        tt=a[1]
                        if wf(G,tt,fuel-1) and wsub(G,v,tt,fuel-1): res=True; break
    _wfmemo[key]=res
    return res

def wsub_reach(G,u,fuel):
    """terms a with u ⟶(ᵉ|ˢ)* a where every promotion step is between wf terms (sound under-approx.)"""
    seen={u}; frontier=[u]
    for _ in range(WD):
        nxt=[]
        for a in frontier:
            for b in ereds(G,(),a,WK):
                if b not in seen and tsize(b)<=SIZE: seen.add(b); nxt.append(b)
            if wf(G,a,fuel):
                for b in sreds(G,(),a,WK):
                    if b not in seen and tsize(b)<=SIZE and wf(G,b,fuel): seen.add(b); nxt.append(b)
        frontier=nxt
    return seen

def wsub(G,u,t,fuel):
    """u ≤*wf t (single layer with wf side conditions; transitivity through wf middles is
    subsumed for the bounded search since the left set already chains promotions between wf terms)"""
    if not (wf(G,u,fuel) and wf(G,t,fuel)): return False
    return bool(wsub_reach(G,u,fuel) & closure(ereds,G,(),t,WK,WD))

# ---- covariant contexts ----
def plugs(Co,u):
    for kind,arg in Co:
        if kind=='app': u=('a',u,arg)
        else: u=('l',arg,u)          # λx≤arg. u  (u locally closed, so no capture)
    return u

def gen_terms(names,maxsize):
    """all terms up to maxsize over the given free names (locally closed)"""
    def go(size,k):
        if size<=0: return []
        out=[TOP]+[F(n) for n in names]+[B(i) for i in range(k)]
        if size==1: return out
        for a in range(1,size-1):
            for u in go(a,k):
                for v in go(size-1-a,k): out.append(A(u,v))
        for a in range(1,size-1):
            for w in go(a,k):
                for b in go(size-1-a,k+1): out.append(L(w,b))
        return out
    seen=set(); res=[]
    for sz in range(1,maxsize+1):
        for t in go(sz,0):
            if t not in seen and S.lc(t): seen.add(t); res.append(t)
    return res

def main():
    maxsize=int(sys.argv[1]); K=int(sys.argv[2]); D=int(sys.argv[3])
    names=['y','z']
    anns=[TOP, L(TOP,TOP), L(TOP,B(0)), L(TOP,L(TOP,TOP)), L(L(TOP,TOP),B(0)), L(TOP,L(TOP,B(1)))]
    ctxs=[()]
    for a in anns:
        for c in ('s','e'):
            ctxs.append((('y',c,a),))
    for a in anns:
        for c in ('s','e'):
            for b in [TOP,F('y'),L(F('y'),B(0)),L(TOP,F('y')),A(F('y'),TOP)]:
                for c2 in ('s','e'):
                    G=(('z',c2,b),('y',c,a))
                    if S.ctx_prevalid(G): ctxs.append(G)
    terms=gen_terms(names,maxsize)
    print(len(ctxs),"contexts",len(terms),"terms",flush=True)
    stats=collections.Counter(); found=[]
    for G in ctxs:
        S._memo.clear(); _smemo.clear(); _wfmemo.clear(); gc.collect()
        dn=S.dom(G)
        ts=[t for t in terms if S.fv(t)<=dn]
        wfs=[t for t in ts if wf(G,t)]
        stats['wf']+=len(wfs)
        pairs=[(u,t) for u in wfs for t in wfs if u!=t and wsub(G,u,t,5)]
        stats['pairs']+=len(pairs)
        cos=[(('app',v),) for v in ts]+[(('fun',a),) for a in ts]+[(('app',v),('app',w)) for v in ts for w in ts if tsize(v)+tsize(w)<=4]+[(('fun',a),('app',v)) for a in ts for v in ts if tsize(a)+tsize(v)<=4]
        for (u,t) in pairs:
            for Co in cos:
                cu,ct=plugs(Co,u),plugs(Co,t)
                if not (wf(G,cu) and wf(G,ct)): continue
                stats['instances']+=1
                if machine(G,(),cu,ct,K,D): stats['ok']+=1
                else:
                    stats['FAIL']+=1; found.append((G,u,t,Co,cu,ct))
                    print("CANDIDATE:",showG(G),"| u =",show(u),"| t =",show(t),"| Co[u] =",show(cu),"| Co[t] =",show(ct),flush=True)
        print(f"ctx {showG(G)}: wf {len(wfs)} pairs {len(pairs)} instances so far {stats['instances']} fail {stats['FAIL']}",flush=True)
    print(dict(stats))
main()
