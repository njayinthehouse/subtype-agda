"""The diamond's recursion, run as a program on real derivation trees.

Every proof attempt on MPSS Lemma 2 fails at the induction, never at a case. This script
executes the recursion the printed proof describes — with the corrected second conjunct's
weakening at Me-App/Me-Bet, and the context-reduction copy at Me-Var/Me-Pro — on explicit
derivation trees, and reports whether it terminates, how deep it goes, and which pieces it
copies. It does not build the joins (those only feed outputs, never recursive calls); it
builds exactly the recursive calls.

Derivations d = (rule, src, tgt, G, s, ...premises). Context reductions c = ('Refl',G,s) |
('Ann', c', x, kind, t, t', d) | ('Stk', c', a, a', d).

Usage:
    python3 diamond-recursion.py --k 2 --kc 1 --budget 200000
"""
import sys, argparse, random, itertools, time
sys.setrecursionlimit(1000000)
from importlib.machinery import SourceFileLoader
S = SourceFileLoader('dsc', __file__.replace('diamond-recursion.py','diamond-search-capped.py')).load_module()
TOP=S.TOP; openRec=S.openRec; closeRec=S.closeRec; fv=S.fv; lc=S.lc; dom=S.dom
prevalid=S.prevalid; lookup_eqv=S.lookup_eqv; show=S.show; showG=S.showG; showS=S.showS
A=S.A; L=S.L; F=S.F; B=S.B

# ---------------------------------------------------------------- derivation trees
# node: dict with rule, src, tgt, G, s, and rule-specific fields
def D(rule, src, tgt, G, s, **kw):
    d={'rule':rule,'src':src,'tgt':tgt,'G':G,'s':s}; d.update(kw); return d

_dmemo={}
def derivs(G,s,t,k):
    """all derivations of G;s ⊢ t ⟶≡ _ with Me-Pro nested at most k deep"""
    key=(G,s,t,k)
    if key in _dmemo: return _dmemo[key]
    out=[]
    pv=prevalid(G,s)
    c=t[0]
    if c=='f':
        if pv: out.append(D('Var',t,t,G,s,x=t[1]))
        a=lookup_eqv(G,t[1])
        if pv and a is not None and k>0:
            for e in derivs(G,s,a,k-1): out.append(D('Pro',t,e['tgt'],G,s,x=t[1],alpha=a,e=e))
    elif c=='T':
        if pv: out.append(D('Top',t,t,G,s))
    elif c=='a':
        u,v=t[1],t[2]
        if u==TOP and pv: out.append(D('TAp',t,TOP,G,s))
        for du in derivs(G,(v,)+s,u,k):
            for dv in derivs(G,(),v,k):
                out.append(D('App',t,('a',du['tgt'],dv['tgt']),G,s,o=du,p=dv))
        if u[0]=='l':
            body=u[2]; x=S.fresh(G,t,s)
            for db in derivs(G,s,openRec(0,('f',x),body),k):
                for dv in derivs(G,(),v,k):
                    out.append(D('Bet',t,openRec(0,dv['tgt'],closeRec(0,x,db['tgt'])),G,s,x=x,F=db,p=dv,ann=u[1]))
    elif c=='l':
        w,b=t[1],t[2]
        if not s:
            x=S.fresh(G,t)
            for dw in derivs(G,(),w,k):
                for db in derivs(((x,'s',w),)+G,(),openRec(0,('f',x),b),k):
                    out.append(D('Fun',t,('l',dw['tgt'],closeRec(0,x,db['tgt'])),G,s,x=x,a=dw,F=db))
        else:
            al,rest=s[0],s[1:]; x=S.fresh(G,t,s)
            for dw in derivs(G,(),w,k):
                for db in derivs(((x,'e',al),)+G,rest,openRec(0,('f',x),b),k):
                    out.append(D('FOp',t,('l',dw['tgt'],closeRec(0,x,db['tgt'])),G,s,x=x,alpha=al,a=dw,F=db))
    _dmemo[key]=out; return out

def ctx_derivs(G,s,k):
    out=[('Refl',G,s)]
    if G:
        x,kind,t=G[0]; tail=G[1:]
        for c in ctx_derivs(tail,s,k):
            for d in derivs(tail,(),t,k):
                out.append(('Ann',c,x,kind,t,d['tgt'],d))
    if s:
        al,rest=s[0],s[1:]
        for c in ctx_derivs(G,rest,k):
            for d in derivs(G,(),al,k):
                out.append(('Stk',c,al,d['tgt'],d))
    return out

def cr_src(c):
    if c[0]=='Refl': return c[1],c[2]
    if c[0]=='Ann': G,s=cr_src(c[1]); return ((c[2],c[3],c[4]),)+G, s
    G,s=cr_src(c[1]); return G,(c[2],)+s
def cr_tgt(c):
    if c[0]=='Refl': return c[1],c[2]
    if c[0]=='Ann': G,s=cr_tgt(c[1]); return ((c[2],c[3],c[5]),)+G, s
    G,s=cr_tgt(c[1]); return G,(c[3],)+s

def refl_deriv(G,s,t):
    """a reflexivity derivation G;s ⊢ t ⟶≡ t (assumes prevalid, lc, scoped)"""
    c=t[0]
    if c=='f': return D('Var',t,t,G,s,x=t[1])
    if c=='T': return D('Top',t,t,G,s)
    if c=='a': return D('App',t,t,G,s,o=refl_deriv(G,(t[2],)+s,t[1]),p=refl_deriv(G,(),t[2]))
    w,b=t[1],t[2]
    if not s:
        x=S.fresh(G,t); return D('Fun',t,t,G,s,x=x,a=refl_deriv(G,(),w),F=refl_deriv(((x,'s',w),)+G,(),openRec(0,('f',x),b)))
    al,rest=s[0],s[1:]; x=S.fresh(G,t,s)
    return D('FOp',t,t,G,s,x=x,alpha=al,a=refl_deriv(G,(),w),F=refl_deriv(((x,'e',al),)+G,rest,openRec(0,('f',x),b)))

# ---------------------------------------------------------------- names, renaming
def names_t(t):
    return fv(t)
def names_d(d):
    n=set(dom(d['G']))|fv(d['src'])|fv(d['tgt'])
    for (_,_,t) in d['G']: n|=fv(t)
    for a in d['s']: n|=fv(a)
    for key in ('e','o','p','F','a'):
        if key in d: n|=names_d(d[key])
    if 'x' in d: n.add(d['x'])
    return n
def names_c(c):
    if c[0]=='Refl': n=set(dom(c[1]))
    elif c[0]=='Ann': n=names_c(c[1])|{c[2]}|names_d(c[6])
    else: n=names_c(c[1])|names_d(c[4])
    return n

def subst_t(t,x,u):
    c=t[0]
    if c=='f': return u if t[1]==x else t
    if c in 'bT': return t
    if c=='l': return ('l',subst_t(t[1],x,u),subst_t(t[2],x,u))
    return ('a',subst_t(t[1],x,u),subst_t(t[2],x,u))
def rename_G(G,x,y): return tuple(((y if n==x else n),k,subst_t(t,x,('f',y))) for (n,k,t) in G)
def rename_s(s,x,y): return tuple(subst_t(a,x,('f',y)) for a in s)
def rename_d(d,x,y):
    """rename the name x to y throughout the tree (y assumed absent)"""
    e=dict(d)
    e['src']=subst_t(d['src'],x,('f',y)); e['tgt']=subst_t(d['tgt'],x,('f',y))
    e['G']=rename_G(d['G'],x,y); e['s']=rename_s(d['s'],x,y)
    if 'x' in d and d['x']==x: e['x']=y
    if 'alpha' in d: e['alpha']=subst_t(d['alpha'],x,('f',y))
    if 'ann' in d: e['ann']=subst_t(d['ann'],x,('f',y))
    for key in ('e','o','p','F','a'):
        if key in d: e[key]=rename_d(d[key],x,y)
    return e

_fresh_counter=[0]
def fresh_name(avoid):
    while True:
        _fresh_counter[0]+=1; n='n%d'%_fresh_counter[0]
        if n not in avoid: return n

# ---------------------------------------------------------------- weakening
def weaken(d,G_target,s_extra):
    """d is at (Δ ++ G_d) ; s_d with G_d a suffix of G_target, and s_extra is pushed under s_d.
    Returns the derivation at (Δ' ++ G_target) ; s_d ++ s_extra, renaming Δ's binders fresh."""
    # rename internal binders that clash with G_target's names or s_extra's names
    avoid=set(dom(G_target))
    for a in s_extra: avoid|=fv(a)
    for (_,_,t) in G_target: avoid|=fv(t)
    d=_rename_binders(d,avoid)
    return _weaken(d,G_target,s_extra)

def _binders(d,acc):
    if d['rule'] in ('Bet','Fun','FOp'): acc.add(d['x'])
    for key in ('e','o','p','F','a'):
        if key in d: _binders(d[key],acc)
    return acc
def _rename_binders(d,avoid):
    bs=_binders(d,set())
    all_names=names_d(d)|avoid
    for b in bs:
        if b in avoid:
            y=fresh_name(all_names); all_names.add(y)
            d=rename_d(d,b,y)
    return d

def _insert(G,G_target):
    """replace the suffix of G that is a suffix of G_target by G_target itself"""
    n=len(G_target)
    # find the largest suffix of G equal to a suffix of G_target
    for i in range(len(G)+1):
        suf=G[i:]
        if len(suf)<=n and suf==G_target[n-len(suf):]:
            return G[:i]+G_target
    raise ValueError("no common suffix")

def _weaken(d,Gt,sx):
    r=d['rule']; G=_insert(d['G'],Gt); s=d['s']+sx
    if r=='Var': return D('Var',d['src'],d['tgt'],G,s,x=d['x'])
    if r=='Top': return D('Top',d['src'],d['tgt'],G,s)
    if r=='TAp': return D('TAp',d['src'],d['tgt'],G,s)
    if r=='Pro': return D('Pro',d['src'],d['tgt'],G,s,x=d['x'],alpha=d['alpha'],e=_weaken(d['e'],Gt,sx))
    if r=='App': return D('App',d['src'],d['tgt'],G,s,o=_weaken(d['o'],Gt,sx),p=_weaken(d['p'],Gt,()))
    if r=='Bet': return D('Bet',d['src'],d['tgt'],G,s,x=d['x'],F=_weaken(d['F'],Gt,sx),p=_weaken(d['p'],Gt,()),ann=d['ann'])
    if r=='Fun':
        if not sx: return D('Fun',d['src'],d['tgt'],G,s,x=d['x'],a=_weaken(d['a'],Gt,()),F=_weaken(d['F'],Gt,()))
        # becomes FOp binding x ≡ head; the body is relabelled sub -> eqv
        al,rest=sx[0],sx[1:]
        Fb=_relabel(d['F'],d['x'],'e',al)
        return D('FOp',d['src'],d['tgt'],G,s,x=d['x'],alpha=al,a=_weaken(d['a'],Gt,()),F=_weaken(Fb,((d['x'],'e',al),)+Gt,rest))
    if r=='FOp':
        return D('FOp',d['src'],d['tgt'],G,s,x=d['x'],alpha=d['alpha'],a=_weaken(d['a'],Gt,()),F=_weaken(d['F'],((d['x'],'e',d['alpha']),)+Gt,rest_of(sx)))
    raise ValueError(r)
def rest_of(sx): return sx
def _relabel(d,x,kind,t):
    """change the context entry for x to (x,kind,t) throughout"""
    e=dict(d); e['G']=tuple(((n,kind,t) if n==x else (n,k,u)) for (n,k,u) in d['G'])
    for key in ('e','o','p','F','a'):
        if key in d: e[key]=_relabel(d[key],x,kind,t)
    return e

# ---------------------------------------------------------------- context-reduction helpers
def extract(c,x):
    """the piece of c for variable x: a derivation at the tail context, empty stack"""
    if c[0]=='Refl':
        G=c[1]
        for i,(n,k,t) in enumerate(G):
            if n==x: return refl_deriv(G[i+1:],(),t)
        raise ValueError("unbound")
    if c[0]=='Stk': return extract(c[1],x)
    if c[2]==x: return c[6]
    return extract(c[1],x)
def empty(c):
    if c[0]=='Refl': return ('Refl',c[1],())
    if c[0]=='Ann': return ('Ann',empty(c[1]),c[2],c[3],c[4],c[5],c[6])
    return empty(c[1])
def pop(c):
    """c : G;(a::s) ↣ G';(a'::s')  ⇒  (c' : G;s ↣ G';s', piece for a)"""
    if c[0]=='Refl':
        G,s=c[1],c[2]; return ('Refl',G,s[1:]), refl_deriv(G,(),s[0])
    if c[0]=='Stk': return c[1], c[4]
    raise ValueError("Ann on a nonempty stack in the head position")   # only if s nonempty below Ann; handled by pushing through
def pop_any(c):
    """like pop but tolerates Ann layers above the Stk layer"""
    if c[0]=='Ann':
        c1,q=pop_any(c[1]); return ('Ann',c1,c[2],c[3],c[4],c[5],c[6]), q
    return pop(c)
def ann(c,x,kind,t,d): return ('Ann',c,x,kind,t,d['tgt'],d)
def stk(c,d): return ('Stk',c,d['src'],d['tgt'],d)

# ---------------------------------------------------------------- the recursion
class Budget(Exception): pass
stats={'calls':0,'depth':0,'copies':0,'trace':[]}
BUDGET=[200000]; TRACE=[False]

def size(d):
    return 1+sum(size(d[k]) for k in ('e','o','p','F','a') if k in d)
def pros(d):
    return (1 if d['rule']=='Pro' else 0)+sum(pros(d[k]) for k in ('e','o','p','F','a') if k in d)

def join(d1,d2,c1,c2,depth=0):
    stats['calls']+=1; stats['depth']=max(stats['depth'],depth)
    if stats['calls']>BUDGET[0]: raise Budget()
    r1,r2=d1['rule'],d2['rule']
    if TRACE[0]: stats['trace'].append((depth,r1,r2,size(d1),size(d2),pros(d1),pros(d2),show(d1['src'])))
    if (r1,r2) in (('Var','Var'),('Top','Top'),('TAp','TAp'),('TAp','App'),('App','TAp')): return
    if r1=='Pro' and r2=='Pro':
        join(d1['e'],d2['e'],c1,c2,depth+1); return
    if r1=='Var' and r2=='Pro':
        try: piece=extract(c1,d1['x'])
        except ValueError:
            print("EXTRACT FAILED for",d1['x'],"d1 at",showG(d1['G']),showS(d1['s']),"d2 at",showG(d2['G']),"c1 src",showG(cr_src(c1)[0]),showS(cr_src(c1)[1])); raise
        stats['copies']+=1
        piece=weaken(piece,d1['G'],d1['s'])
        join(piece,d2['e'],c1,c2,depth+1); return
    if r1=='Pro' and r2=='Var':
        try: piece=extract(c2,d2['x'])
        except ValueError:
            print("EXTRACT FAILED for",d2['x'],"d2 at",showG(d2['G']),showS(d2['s']),"d1 at",showG(d1['G']),"c2 src",showG(cr_src(c2)[0]),showS(cr_src(c2)[1])); raise
        stats['copies']+=1
        piece=weaken(piece,d2['G'],d2['s'])
        join(d1['e'],piece,c1,c2,depth+1); return
    if r1=='App' and r2=='App':
        join(d1['o'],d2['o'],stk(c1,d1['p']),stk(c2,d2['p']),depth+1)
        join(d1['p'],d2['p'],empty(c1),empty(c2),depth+1); return
    if r1=='App' and r2=='Bet':
        o1=d1['o']; assert o1['rule']=='FOp'
        x=o1['x']; F2=d2['F']
        # bring F2's binder to x, then weaken with x ≡ v at the head
        y=d2['x']
        if y!=x:
            if x in names_d(F2): F2=rename_d(F2,x,fresh_name(names_d(F2)|names_d(o1)))
            F2=rename_d(F2,y,x)
        F2w=_weaken(F2,((x,'e',d1['src'][2]),)+d1['G'],())
        join(o1['F'],F2w,ann(c1,x,'e',d1['src'][2],d1['p']),ann(c2,x,'e',d1['src'][2],d2['p']),depth+1)
        join(d1['p'],d2['p'],empty(c1),empty(c2),depth+1); return
    if r1=='Bet' and r2=='App':
        join(d2,d1,c2,c1,depth); return
    if r1=='Bet' and r2=='Bet':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in names_d(F2): F2=rename_d(F2,x,fresh_name(names_d(F2)|names_d(F1)))
            F2=rename_d(F2,y,x)
        join(F1,F2,c1,c2,depth+1)
        join(d1['p'],d2['p'],empty(c1),empty(c2),depth+1); return
    if r1=='Fun' and r2=='Fun':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in names_d(F2): F2=rename_d(F2,x,fresh_name(names_d(F2)|names_d(F1)))
            F2=rename_d(F2,y,x)
        join(d1['a'],d2['a'],c1,c2,depth+1)
        join(F1,F2,ann(c1,x,'s',d1['src'][1],d1['a']),ann(c2,x,'s',d1['src'][1],d2['a']),depth+1); return
    if r1=='FOp' and r2=='FOp':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in names_d(F2): F2=rename_d(F2,x,fresh_name(names_d(F2)|names_d(F1)))
            F2=rename_d(F2,y,x)
        c1p,q1=pop_any(c1); c2p,q2=pop_any(c2)
        join(d1['a'],d2['a'],empty(c1),empty(c2),depth+1)
        join(F1,F2,ann(c1p,x,'e',d1['alpha'],q1),ann(c2p,x,'e',d1['alpha'],q2),depth+1); return
    if r1=='Pro' or r2=='Var' or (r1,r2)==('Var','Pro'):
        pass
    raise ValueError("unexpected case %s/%s on %s"%(r1,r2,show(d1['src'])))

# ---------------------------------------------------------------- driver
MAXRUNS=[300000]
def run(G,s,t,k,kc,label=''):
    _dmemo.clear()
    ds=derivs(G,s,t,k); cs=ctx_derivs(G,s,kc)
    worst=(0,None); budget_hits=[]
    n=0
    total=len(ds)*len(ds)*len(cs)*len(cs)
    if total<=MAXRUNS[0]:
        quads=((d1,d2,c1,c2) for d1 in ds for d2 in ds for c1 in cs for c2 in cs)
    else:
        rng=random.Random(total)
        quads=((rng.choice(ds),rng.choice(ds),rng.choice(cs),rng.choice(cs)) for _ in range(MAXRUNS[0]))
        label+=f" (sampled {MAXRUNS[0]} of {total})"
    for (d1,d2,c1,c2) in quads:
                    n+=1
                    stats.update(calls=0,depth=0,copies=0,trace=[])
                    try:
                        join(d1,d2,c1,c2)
                        if stats['calls']>worst[0]: worst=(stats['calls'],(d1,d2,c1,c2,stats['depth'],stats['copies']))
                    except Budget:
                        budget_hits.append((d1,d2,c1,c2))
    print(f"{label} {show(t)} at {showG(G)}; {showS(s)}: {len(ds)} derivations, {len(cs)} ctx-reductions, {n} runs; "
          f"worst {worst[0]} calls (depth {worst[1][4] if worst[1] else 0}, copies {worst[1][5] if worst[1] else 0}); budget hits {len(budget_hits)}",flush=True)
    return worst,budget_hits

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--k',type=int,default=2); ap.add_argument('--kc',type=int,default=1)
    ap.add_argument('--budget',type=int,default=200000)
    ap.add_argument('--random',type=int,default=0); ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--trace',action='store_true')
    ap.add_argument('--maxruns',type=int,default=300000)
    ap.add_argument('--only',type=int,default=-1)
    a=ap.parse_args(); BUDGET[0]=a.budget; MAXRUNS[0]=a.maxruns
    rng=random.Random(a.seed)
    cfgs=S.families() if not a.random else [S.rand_cfg(rng) for _ in range(a.random)]
    cfgs=[c for c in cfgs if prevalid(c[0],c[1]) and lc(c[2]) and fv(c[2])<=dom(c[0])]
    if a.only>=0: cfgs=[cfgs[a.only]]
    allhits=[]; overall=(0,None)
    for i,(G,s,t) in enumerate(cfgs):
        try:
            worst,hits=run(G,s,t,a.k,a.kc,label=f"[{i+1}/{len(cfgs)}]")
        except RecursionError:
            print("  recursion limit"); continue
        if worst[0]>overall[0]: overall=worst
        allhits+=hits
    print(f"DONE: {len(cfgs)} configurations, {len(allhits)} budget hits, worst run {overall[0]} calls")
    if overall[1]:
        d1,d2,c1,c2,dep,cop=overall[1]
        print("worst input: t0 =",show(d1['src']),"at",showG(d1['G']),showS(d1['s']))
        print("  t1 =",show(d1['tgt']),"  t2 =",show(d2['tgt']))
        print("  c1 ->",showG(cr_tgt(c1)[0]),showS(cr_tgt(c1)[1]))
        print("  c2 ->",showG(cr_tgt(c2)[0]),showS(cr_tgt(c2)[1]))
        if a.trace:
            TRACE[0]=True; stats.update(calls=0,depth=0,copies=0,trace=[]); BUDGET[0]=10**9
            join(d1,d2,c1,c2)
            for (dep,r1,r2,s1,s2,p1,p2,src) in stats['trace']:
                print(f"    {'  '*min(dep,40)}{r1}/{r2} |d1|={s1} |d2|={s2} pro={p1},{p2} {src}")
    for (d1,d2,c1,c2) in allhits[:3]:
        print("BUDGET HIT: t0 =",show(d1['src']),"at",showG(d1['G']),showS(d1['s']),"t1 =",show(d1['tgt']),"t2 =",show(d2['tgt']))
