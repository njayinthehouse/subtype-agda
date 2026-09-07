"""Probe termination orders that use each side's HISTORY: the variable whose pull created the
current material (its anchor), the size of that material, and whether the pull's trigger was
external or internal to the other side's material. Static features could not see this
(DEAD-ENDS rows 19-26); this probe threads it through the recursion and tests orders on it.
"""
import sys, collections
from importlib.machinery import SourceFileLoader
R = SourceFileLoader('dr','/home/egret/gimmick/1/MPSS/diamond-recursion.py').load_module()
S = R.S
INF = 10**9

def bt(G,x):
    names=[e[0] for e in reversed(G)]
    return names.index(x) if x in names else -1

EDGES=[]
class Budget(Exception): pass
CALLS=[0]

def rec(d1,d2,c1,c2,meta,parent):
    """meta = dict(a=[a1,a2], m=[m1,m2], k=[k1,k2])"""
    CALLS[0]+=1
    if CALLS[0]>200000: raise Budget()
    me=(d1,d2,c1,c2,dict(a=list(meta['a']),m=list(meta['m']),k=list(meta['k'])))
    if parent is not None: EDGES.append((parent,me,d1['rule']+'/'+d2['rule']))
    r1,r2=d1['rule'],d2['rule']
    if (r1,r2) in (('Var','Var'),('Top','Top'),('TAp','TAp'),('TAp','App'),('App','TAp')): return
    def pull(side,var,G):
        other=1-side
        v=bt(G,var)
        kind='ext' if v<meta['a'][other] else 'int'
        m2=dict(a=list(meta['a']),m=list(meta['m']),k=list(meta['k']))
        m2['a'][side]=v; m2['k'][side]=kind
        return m2
    if r1=='Pro' and r2=='Pro':
        rec(d1['e'],d2['e'],c1,c2,meta,me); return
    if r1=='Var' and r2=='Pro':
        piece=R.weaken(R.extract(c1,d1['x']),d1['G'],d1['s'])
        m2=pull(0,d1['x'],d1['G']); m2['m'][0]=R.size(piece)
        rec(piece,d2['e'],c1,c2,m2,me); return
    if r1=='Pro' and r2=='Var':
        piece=R.weaken(R.extract(c2,d2['x']),d2['G'],d2['s'])
        m2=pull(1,d2['x'],d2['G']); m2['m'][1]=R.size(piece)
        rec(d1['e'],piece,c1,c2,m2,me); return
    if r1=='App' and r2=='App':
        rec(d1['o'],d2['o'],R.stk(c1,d1['p']),R.stk(c2,d2['p']),meta,me)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),meta,me); return
    if r1=='App' and r2=='Bet':
        o1=d1['o']; x=o1['x']; F2=d2['F']; y=d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(o1)))
            F2=R.rename_d(F2,y,x)
        F2w=R._weaken(F2,((x,'e',d1['src'][2]),)+d1['G'],())
        rec(o1['F'],F2w,R.ann(c1,x,'e',d1['src'][2],d1['p']),R.ann(c2,x,'e',d1['src'][2],d2['p']),meta,me)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),meta,me); return
    if r1=='Bet' and r2=='App':
        sw=dict(a=[meta['a'][1],meta['a'][0]],m=[meta['m'][1],meta['m'][0]],k=[meta['k'][1],meta['k'][0]])
        # swap sides: continue with swapped meta but record edges consistently (drop the swap edge)
        SWAP.append(1)
        rec(d2,d1,c2,c1,sw,None); SWAP.pop(); return
    if r1=='Bet' and r2=='Bet':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        rec(F1,F2,c1,c2,meta,me)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),meta,me); return
    if r1=='Fun' and r2=='Fun':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        rec(d1['a'],d2['a'],c1,c2,meta,me)
        rec(F1,F2,R.ann(c1,x,'s',d1['src'][1],d1['a']),R.ann(c2,x,'s',d1['src'][1],d2['a']),meta,me); return
    if r1=='FOp' and r2=='FOp':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        c1p,q1=R.pop_any(c1); c2p,q2=R.pop_any(c2)
        rec(d1['a'],d2['a'],R.empty(c1),R.empty(c2),meta,me)
        rec(F1,F2,R.ann(c1p,x,'e',d1['alpha'],q1),R.ann(c2p,x,'e',d1['alpha'],q2),meta,me); return
    raise ValueError("unexpected %s/%s"%(r1,r2))
SWAP=[]

# ---- candidate orders on (state, meta) ----
def feats(st):
    d1,d2,c1,c2,meta=st
    a=meta['a']; t=(R.size(d1),R.size(d2)); m=meta['m']
    return a,t,m,(R.pros(d1),R.pros(d2))

def cands(st):
    a,t,m,p=feats(st); c={}
    # max-anchor side first
    if a[0]>a[1]: mx,mn=0,1
    elif a[1]>a[0]: mx,mn=1,0
    else: mx,mn=None,None
    A=max(a)
    if mx is None: c['A,Tmax,Tmin']=(A,t[0]+t[1],0)
    else: c['A,Tmax,Tmin']=(A,t[mx],t[mn])
    c['ms(a,T)']=tuple(sorted([(a[0],t[0]),(a[1],t[1])],reverse=True))
    c['ms(a),Tsum']=(tuple(sorted(a,reverse=True)),t[0]+t[1])
    c['A,Tsum']=(A,t[0]+t[1])
    c['A,Psum,Tsum']=(A,p[0]+p[1],t[0]+t[1])
    # min-anchor first variants
    c['minA,Tsum']=(min(a),t[0]+t[1])
    c['Tsum']=t[0]+t[1]
    c['ms(a,T)+m']=tuple(sorted([(a[0],t[0],m[0]),(a[1],t[1],m[1])],reverse=True))
    return c

def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    viol=collections.defaultdict(collections.Counter); shown=collections.defaultdict(collections.Counter); total=0
    import random
    for i,(G,s,t) in enumerate(cfgs):
        R._dmemo.clear()
        ds=R.derivs(G,s,t,k); cs=R.ctx_derivs(G,s,kc)
        quads=[(d1,d2,c1,c2) for d1 in ds for d2 in ds for c1 in cs for c2 in cs]
        if len(quads)>maxruns:
            rng=random.Random(len(quads)); quads=[rng.choice(quads) for _ in range(maxruns)]
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {len(quads)} runs",flush=True)
        for (d1,d2,c1,c2) in quads:
            EDGES.clear(); CALLS[0]=0
            meta=dict(a=[INF,INF],m=[R.size(d1),R.size(d2)],k=['root','root'])
            try: rec(d1,d2,c1,c2,meta,None)
            except Budget: print("  budget hit",flush=True); continue
            for (par,ch,case) in EDGES:
                total+=1
                fp=cands(par); fc=cands(ch)
                for name in fp:
                    if not (fc[name] < fp[name]):
                        viol[name][case]+=1
                        if shown[name][case]<2:
                            shown[name][case]+=1
                            print(f"  VIOL {name} [{case}] {fp[name]} -> {fc[name]}  anchors {par[4]['a']}->{ch[4]['a']} kinds {ch[4]['k']}",flush=True)
                            print(f"       {S.show(par[0]['src'])}  ->  {S.show(ch[0]['src'])} at {S.showG(ch[0]['G'])};{S.showS(ch[0]['s'])}",flush=True)
    print(f"\n{total} edges",flush=True)
    for name in sorted(cands((None,)*5) if False else viol.keys()|set(cands(EDGES[0][0]).keys())):
        v=viol.get(name,{})
        print(f"  {name:20s} violations: {sum(v.values()):7d} {dict(v)}",flush=True)

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    run(k,1,int(sys.argv[2]) if len(sys.argv)>2 else 20000)
