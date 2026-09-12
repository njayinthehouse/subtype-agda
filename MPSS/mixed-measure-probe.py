"""Probe for the asymmetric statement W: side 1 = variant derivation (Me-Pro premise at the empty
stack), side 2 = original derivation; c1 has variant pieces, c2 original pieces.
Measure Psi(state) = size(d2) + sum of sizes of c2's stack pieces + sum of sizes of c2's Ann pieces
for variables reachable from fv(subject) ∪ fv(stack) through the context's annotations.
Checks Psi strictly decreases at every recursive call (non-leaf)."""
import sys, random, gc, collections
sys.setrecursionlimit(100000)
from importlib.machinery import SourceFileLoader
R=SourceFileLoader('dr','/home/egret/gimmick/1/MPSS/diamond-recursion.py').load_module()
S=R.S
A,L,F,B,TOP=S.A,S.L,S.F,S.B,S.TOP
D=R.D; openRec=S.openRec; closeRec=S.closeRec; prevalid=S.prevalid; lookup_eqv=S.lookup_eqv

_vmemo={}
def vderivs(G,s,t,k):
    """variant derivations: Me-Pro premise at the empty stack"""
    key=(G,s,t,k)
    if key in _vmemo: return _vmemo[key]
    out=[]; pv=prevalid(G,s); c=t[0]
    if c=='f':
        if pv: out.append(D('Var',t,t,G,s,x=t[1]))
        a=lookup_eqv(G,t[1])
        if pv and a is not None and k>0:
            for e in vderivs(G,(),a,k-1): out.append(D('Pro',t,e['tgt'],G,s,x=t[1],alpha=a,e=e))
    elif c=='T':
        if pv: out.append(D('Top',t,t,G,s))
    elif c=='a':
        u,v=t[1],t[2]
        if u==TOP and pv: out.append(D('TAp',t,TOP,G,s))
        for du in vderivs(G,(v,)+s,u,k):
            for dv in vderivs(G,(),v,k):
                out.append(D('App',t,('a',du['tgt'],dv['tgt']),G,s,o=du,p=dv))
        if u[0]=='l':
            body=u[2]; x=S.fresh(G,t,s)
            for db in vderivs(G,s,openRec(0,('f',x),body),k):
                for dv in vderivs(G,(),v,k):
                    out.append(D('Bet',t,openRec(0,dv['tgt'],closeRec(0,x,db['tgt'])),G,s,x=x,F=db,p=dv,ann=u[1]))
    elif c=='l':
        w,b=t[1],t[2]
        if not s:
            x=S.fresh(G,t)
            for dw in vderivs(G,(),w,k):
                for db in vderivs(((x,'s',w),)+G,(),openRec(0,('f',x),b),k):
                    out.append(D('Fun',t,('l',dw['tgt'],closeRec(0,x,db['tgt'])),G,s,x=x,a=dw,F=db))
        else:
            al,rest=s[0],s[1:]; x=S.fresh(G,t,s)
            for dw in vderivs(G,(),w,k):
                for db in vderivs(((x,'e',al),)+G,rest,openRec(0,('f',x),b),k):
                    out.append(D('FOp',t,('l',dw['tgt'],closeRec(0,x,db['tgt'])),G,s,x=x,alpha=al,a=dw,F=db))
    _vmemo[key]=out; return out
def vctx_derivs(G,s,k):
    out=[('Refl',G,s)]
    if G:
        x,kind,t=G[0]; tail=G[1:]
        for c in vctx_derivs(tail,s,k):
            for d in vderivs(tail,(),t,k): out.append(('Ann',c,x,kind,t,d['tgt'],d))
    if s:
        al,rest=s[0],s[1:]
        for c in vctx_derivs(G,rest,k):
            for d in vderivs(G,(),al,k): out.append(('Stk',c,al,d['tgt'],d))
    return out

def refl_size(t):
    c=t[0]
    if c in 'bfT': return 1
    if c=='a': return 1+refl_size(t[1])+refl_size(t[2])
    return 1+refl_size(t[1])+refl_size(t[2])   # lam: 1 + ann + body (opening keeps size)
def ann_piece_size(c,x):
    """size of c's Ann piece for x (refl piece if in the Refl suffix)"""
    if c[0]=='Refl':
        for (n,k,t) in c[1]:
            if n==x: return refl_size(t)
        raise ValueError
    if c[0]=='Stk': return ann_piece_size(c[1],x)
    if c[2]==x: return R.size(c[6])
    return ann_piece_size(c[1],x)
def stk_pieces_size(c):
    if c[0]=='Refl': return sum(refl_size(a) for a in c[2])
    if c[0]=='Stk': return R.size(c[4])+stk_pieces_size(c[1])
    return stk_pieces_size(c[1])
def reach(G,N):
    """variables reachable from N in one pass down G (G head = newest)"""
    N=set(N); out=set()
    for (n,k,t) in G:
        if n in N: out.add(n); N|=S.fv(t)
    return out
def psi(d2,c2):
    G,s,t=d2['G'],d2['s'],d2['src']
    N=set(S.fv(t))
    for a in s: N|=S.fv(a)
    return R.size(d2)+stk_pieces_size(c2)+sum(ann_piece_size(c2,x) for x in reach(G,N))

ST=collections.Counter(); EX={}; PARENT=[None]
def _vweaken(d,Gt,sx):
    r=d['rule']; G=R._insert(d['G'],Gt); s=d['s']+sx
    if r=='Var': return D('Var',d['src'],d['tgt'],G,s,x=d['x'])
    if r=='Top': return D('Top',d['src'],d['tgt'],G,s)
    if r=='TAp': return D('TAp',d['src'],d['tgt'],G,s)
    if r=='Pro': return D('Pro',d['src'],d['tgt'],G,s,x=d['x'],alpha=d['alpha'],e=_vweaken(d['e'],Gt,()))
    if r=='App': return D('App',d['src'],d['tgt'],G,s,o=_vweaken(d['o'],Gt,sx),p=_vweaken(d['p'],Gt,()))
    if r=='Bet': return D('Bet',d['src'],d['tgt'],G,s,x=d['x'],F=_vweaken(d['F'],Gt,sx),p=_vweaken(d['p'],Gt,()),ann=d['ann'])
    if r=='Fun':
        if not sx: return D('Fun',d['src'],d['tgt'],G,s,x=d['x'],a=_vweaken(d['a'],Gt,()),F=_vweaken(d['F'],Gt,()))
        al,rest=sx[0],sx[1:]
        Fb=R._relabel(d['F'],d['x'],'e',al)
        return D('FOp',d['src'],d['tgt'],G,s,x=d['x'],alpha=al,a=_vweaken(d['a'],Gt,()),F=_vweaken(Fb,Gt,rest))
    if r=='FOp':
        return D('FOp',d['src'],d['tgt'],G,s,x=d['x'],alpha=d['alpha'],a=_vweaken(d['a'],Gt,()),F=_vweaken(d['F'],Gt,sx))
    raise ValueError(r)
def vweaken(d,G_target,s_extra):
    avoid=set(R.dom(G_target))
    for a in s_extra: avoid|=S.fv(a)
    for (_,_,t) in G_target: avoid|=S.fv(t)
    d=R._rename_binders(d,avoid)
    return _vweaken(d,G_target,s_extra)
class Budget(Exception): pass
CALLS=[0]
def rec(d1,d2,c1,c2,parent_psi,depth=0):
    """d1 variant side, d2 original side"""
    CALLS[0]+=1
    if CALLS[0]>200000: raise Budget()
    r1,r2=d1['rule'],d2['rule']
    PARENT.append((r1,r2))
    leaf=(r1,r2) in (('Var','Var'),('Top','Top'),('TAp','TAp'),('TAp','App'),('App','TAp'))
    p=psi(d2,c2)
    if parent_psi is not None:
        ST['calls']+=1
        if not (p<parent_psi):
            ST['PSI_FAIL']+=1; EX.setdefault('psi',(r1,r2,S.show(d2['src']),S.showG(d2['G']),S.showS(d2['s']),parent_psi,p))
    if leaf: return
    if r1=='Pro' and r2=='Pro':
        # variant premise at [], pushed under s; original premise at s
        piece=vweaken(d1['e'],d1['G'],d1['s'])
        rec(piece,d2['e'],c1,c2,p,depth+1); return
    if r1=='Var' and r2=='Pro':
        piece=vweaken(R.extract(c1,d1['x']),d1['G'],d1['s'])
        ST['pull_v']+=1
        rec(piece,d2['e'],c1,c2,p,depth+1); return
    if r1=='Pro' and r2=='Var':
        piece=R.extract(c2,d2['x']); piece=R.weaken(piece,d2['G'],())
        ST['pull_d']+=1
        rec(d1['e'],piece,R.empty(c1),R.empty(c2),p,depth+1); return
    if r1=='App' and r2=='App':
        rec(d1['o'],d2['o'],R.stk(c1,d1['p']),R.stk(c2,d2['p']),p,depth+1)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),p,depth+1); return
    if (r1,r2) in (('App','Bet'),('Bet','App')):
        if r1=='App':
            o1=d1['o']; x=o1['x']; F2=d2['F']; y=d2['x']
            if y!=x:
                if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(o1)))
                F2=R.rename_d(F2,y,x)
            F2w=R._weaken(F2,((x,'e',d1['src'][2]),)+d1['G'],())
            rec(o1['F'],F2w,R.ann(c1,x,'e',d1['src'][2],d1['p']),R.ann(c2,x,'e',d1['src'][2],d2['p']),p,depth+1)
        else:
            o2=d2['o']; x=o2['x']; F1=d1['F']; y=d1['x']
            if y!=x:
                if x in R.names_d(F1): F1=R.rename_d(F1,x,R.fresh_name(R.names_d(F1)|R.names_d(o2)))
                F1=R.rename_d(F1,y,x)
            F1w=_vweaken(F1,((x,'e',d2['src'][2]),)+d2['G'],())
            rec(F1w,o2['F'],R.ann(c1,x,'e',d2['src'][2],d1['p']),R.ann(c2,x,'e',d2['src'][2],d2['p']),p,depth+1)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),p,depth+1); return
    if r1=='Bet' and r2=='Bet':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        rec(F1,F2,c1,c2,p,depth+1)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),p,depth+1); return
    if r1=='Fun' and r2=='Fun':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        rec(d1['a'],d2['a'],c1,c2,p,depth+1)
        rec(F1,F2,R.ann(c1,x,'s',d1['src'][1],d1['a']),R.ann(c2,x,'s',d1['src'][1],d2['a']),p,depth+1); return
    if r1=='FOp' and r2=='FOp':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        c1p,q1=R.pop_any(c1); c2p,q2=R.pop_any(c2)
        rec(d1['a'],d2['a'],R.empty(c1),R.empty(c2),p,depth+1)
        rec(F1,F2,R.ann(c1p,x,'e',d1['alpha'],q1),R.ann(c2p,x,'e',d1['alpha'],q2),p,depth+1); return
    raise ValueError((r1,r2,S.show(d1['src']),S.showS(d1['s']),S.showS(d2['s']),S.show(d2['src']),PARENT[-1]))

def main():
    k=int(sys.argv[1]); kc=int(sys.argv[2]); maxruns=int(sys.argv[3])
    cfgs=S.families()
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    y,v,x,w,u='y','v','x','w','u'
    cfgs.append((((v,'e',A(F(y),A(A(TOP,TOP),A(TOP,TOP)))),(y,'e',L(TOP,A(B(0),B(0))))),(),F(v)))
    cfgs.append((((u,'e',L(TOP,A(F(w),B(0)))),(w,'e',L(TOP,B(0)))),(),A(F(u),F(u))))
    cfgs.append(((),(),A(L(TOP,A(B(0),B(0))),L(TOP,B(0)))))
    cfgs.append(((),(),A(L(TOP,A(B(0),B(0))),L(TOP,A(B(0),F(u))))) )  # not scoped; filtered below
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    for i,(G,s,t) in enumerate(cfgs):
        R._dmemo.clear(); _vmemo.clear(); gc.collect()
        try:
            ds=R.derivs(G,s,t,k); vs=vderivs(G,s,t,k); cs=R.ctx_derivs(G,s,kc); vcs=vctx_derivs(G,s,kc)
        except MemoryError:
            R._dmemo.clear(); _vmemo.clear(); gc.collect(); print(f"[{i}] skipped (memory)",flush=True); continue
        if max(len(ds),len(vs),len(cs),len(vcs))>30000: print(f"[{i}] skipped (big)",flush=True); continue
        total=len(vs)*len(ds)*len(vcs)*len(cs); rng=random.Random(i)
        if total<=maxruns: quads=((a,b,c,d) for a in vs for b in ds for c in vcs for d in cs)
        else: quads=((rng.choice(vs),rng.choice(ds),rng.choice(vcs),rng.choice(cs)) for _ in range(maxruns))
        n=0
        for (v1,d2,c1,c2) in quads:
            CALLS[0]=0
            try: rec(v1,d2,c1,c2,None); n+=1
            except Budget: ST['budget']+=1
            except (MemoryError,RecursionError): ST['crash']+=1
        print(f"[{i}] {S.show(t)} @ {S.showG(G)};{S.showS(s)} — {n} runs",flush=True)
    for kk,vv in sorted(ST.items(),key=str): print(kk,vv)
    for name,ex in EX.items(): print("EXAMPLE",name,ex)
main()
