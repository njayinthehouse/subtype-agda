"""Path-local, origin-tagged recursion probe.
Every input node gets id=(tree, path). Copies keep ids. Along each root-to-leaf path we check:
 (A) no trigger id (the Me-Pro node consumed at a pull) is consumed twice        [distinct consumption]
 (B) no pair (id1,id2) of current materials recurs                                [no-repeat]
 (C) whether a stored piece (root id + storing time) is fetched twice
and classify pulls as ext/int relative to the OTHER side's anchor (the trigger's material)."""
import sys, collections, random, gc
sys.setrecursionlimit(100000)
from importlib.machinery import SourceFileLoader
R=SourceFileLoader('dr','/home/egret/gimmick/1/MPSS/diamond-recursion.py').load_module()
S=R.S
A,L,F,B,TOP=S.A,S.L,S.F,S.B,S.TOP
KEYS=('e','o','p','F','a')

def tag(d,tree,path=()):
    d['id']=(tree,path)
    for k in KEYS:
        if k in d: tag(d[k],tree,path+(k,))
def tag_c(c,tree,path=()):
    if c[0]=='Refl': return
    if c[0]=='Ann': tag(c[6],tree,path+('ann',c[2])); tag_c(c[1],tree,path+('tail',))
    else: tag(c[4],tree,path+('stk',)); tag_c(c[1],tree,path+('tail',))
def copy_ids(src,dst):
    if 'id' in src: dst['id']=src['id']
    for k in KEYS:
        if k in src and k in dst: copy_ids(src[k],dst[k])
_w=R._weaken
def _weaken2(d,Gt,sx):
    r=_w(d,Gt,sx); copy_ids(d,r); return r
R._weaken=_weaken2
def refl_tagged(G,s,t,tree):
    d=R.refl_deriv(G,s,t); tag(d,tree); return d

CLOCK=[0]
class Budget(Exception): pass
def tick():
    CLOCK[0]+=1
    if CLOCK[0]>100000: raise Budget()
    return CLOCK[0]
def stamp_of(c,x):
    if c[0]=='Refl': return None
    if c[0]=='Stk': return stamp_of(c[1],x)
    if c[2]==x: return c[7] if len(c)>7 else None
    return stamp_of(c[1],x)
def ann(c,x,kind,t,d,stamp): return ('Ann',c,x,kind,t,d['tgt'],d,stamp)
def stk(c,d,stamp): return ('Stk',c,d['src'],d['tgt'],d,stamp)
def pop_any(c):
    if c[0]=='Ann':
        c1,q,stp=pop_any(c[1]); return ('Ann',c1)+tuple(c[2:]), q, stp
    if c[0]=='Refl':
        G,s=c[1],c[2]; return ('Refl',G,s[1:]), refl_tagged(G,(),s[0],('refl',CLOCK[0])), None
    return c[1], c[4], (c[5] if len(c)>5 else None)
def empty(c):
    if c[0]=='Refl': return ('Refl',c[1],())
    if c[0]=='Ann': return ('Ann',empty(c[1]),)+tuple(c[2:])
    return empty(c[1])
def extract(c,x):
    if c[0]=='Refl':
        G=c[1]
        for i,(n,k,t) in enumerate(G):
            if n==x: return refl_tagged(G[i+1:],(),t,('refl',CLOCK[0]))
        raise ValueError
    if c[0]=='Stk': return extract(c[1],x)
    if c[2]==x: return c[6]
    return extract(c[1],x)
def bt(G,x):
    names=[e[0] for e in reversed(G)]
    return names.index(x) if x in names else -1

ST=collections.Counter(); EX={}
PATH=[]      # pull events along the current path
PAIRS=[]     # (id1,id2) along the current path
TRIG=[]      # trigger ids along the current path
def check_pull(ev):
    ST['pulls']+=1; ST[ev['kind']]+=1
    if ev['trigger'] in TRIG:
        ST['A_trigger_repeat']+=1; EX.setdefault('A',(list(PATH),ev))
    if ev['fetched'] is not None:
        if ev['fetched'] in [e['fetched'] for e in PATH]:
            ST['C_stored_piece_refetched']+=1; EX.setdefault('C',(list(PATH),ev))
        # fetched piece cut from which material? compare storing time with puller's last pull time
        last=max([e['time'] for e in PATH if e['side']==ev['side']] or [0])
        if ev['fetched'][1]<last: ST['fetched_stored_before_own_last_pull']+=1
        else: ST['fetched_stored_after_own_last_pull']+=1
        if ev['kind']=='ext': ST['ext_fetch_stored']+=1
    else:
        if ev['kind']=='int': ST['int_fetch_original']+=1; EX.setdefault('intorig',(list(PATH),ev))
VISITS=[]
def check_pair(d1,d2,m):
    p=(d1.get('id'),d2.get('id'))
    if p in PAIRS: ST['B_pair_repeat']+=1; EX.setdefault('B',(list(PATH),p))
    v0=(0,m[0]['frame'],d1.get('id')); v1=(1,m[1]['frame'],d2.get('id'))
    for v in (v0,v1):
        if any(v in pair for pair in VISITS): ST['V_frame_position_revisit']+=1; EX.setdefault('V',(list(PATH),v))
    VISITS.append((v0,v1))
    return p
def rec(d1,d2,c1,c2,meta,depth=0):
    t=tick()
    r1,r2=d1['rule'],d2['rule']
    pr=check_pair(d1,d2,meta); PAIRS.append(pr)
    try:
        if (r1,r2) in (('Var','Var'),('Top','Top'),('TAp','TAp'),('TAp','App'),('App','TAp')): return
        m=meta
        if r1=='Pro' and r2=='Pro':
            rec(d1['e'],d2['e'],c1,c2,m,depth+1); return
        if (r1,r2) in (('Var','Pro'),('Pro','Var')):
            side=0 if r1=='Var' else 1
            d,dd,c=(d1,d2,c1) if side==0 else (d2,d1,c2)
            x=d['x']; piece=R.weaken(extract(c,x),d['G'],d['s'])
            stp=stamp_of(c,x); v=bt(d['G'],x)
            kind='ext' if v<m[1-side]['anchor_bt'] else 'int'
            newframe = (stp[4] if stp is not None else ('frame',t,side))
            ev=dict(time=t,depth=depth,side=side,var=x,var_bt=v,kind=kind,fetched=stp,frame_from=m[side]['frame'],frame_to=newframe,
                    trigger=dd.get('id'),piece_root=piece.get('id'),puller_root=d.get('id'),
                    psize=R.size(piece),osize=R.size(dd),stack=len(d['s']),ctx=len(d['G']))
            check_pull(ev); PATH.append(ev); TRIG.append(ev['trigger'])
            m2=[dict(m[0]),dict(m[1])]; m2[side]['anchor_bt']=v; m2[side]['frame']=newframe
            try:
                if side==0: rec(piece,d2['e'],c1,c2,m2,depth+1)
                else: rec(d1['e'],piece,c1,c2,m2,depth+1)
            finally: PATH.pop(); TRIG.pop()
            return
        if r1=='App' and r2=='App':
            s1=('stk',t,0,d1['p'].get('id'),m[0]['frame']); s2=('stk',t,1,d2['p'].get('id'),m[1]['frame'])
            rec(d1['o'],d2['o'],stk(c1,d1['p'],s1),stk(c2,d2['p'],s2),m,depth+1)
            rec(d1['p'],d2['p'],empty(c1),empty(c2),m,depth+1); return
        if r1=='App' and r2=='Bet':
            o1=d1['o']; x=o1['x']; F2=d2['F']; y=d2['x']
            if y!=x:
                if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(o1)))
                F2=R.rename_d(F2,y,x)
            F2w=R._weaken(F2,((x,'e',d1['src'][2]),)+d1['G'],())
            s1=('bet',t,0,d1['p'].get('id'),m[0]['frame']); s2=('bet',t,1,d2['p'].get('id'),m[1]['frame'])
            rec(o1['F'],F2w,ann(c1,x,'e',d1['src'][2],d1['p'],s1),ann(c2,x,'e',d1['src'][2],d2['p'],s2),m,depth+1)
            rec(d1['p'],d2['p'],empty(c1),empty(c2),m,depth+1); return
        if r1=='Bet' and r2=='App':
            rec(d2,d1,c2,c1,[m[1],m[0]],depth); return
        if r1=='Bet' and r2=='Bet':
            F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
            if y!=x:
                if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
                F2=R.rename_d(F2,y,x)
            rec(F1,F2,c1,c2,m,depth+1)
            rec(d1['p'],d2['p'],empty(c1),empty(c2),m,depth+1); return
        if r1=='Fun' and r2=='Fun':
            F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
            if y!=x:
                if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
                F2=R.rename_d(F2,y,x)
            rec(d1['a'],d2['a'],c1,c2,m,depth+1)
            s1=('fun',t,0,d1['a'].get('id'),m[0]['frame']); s2=('fun',t,1,d2['a'].get('id'),m[1]['frame'])
            rec(F1,F2,ann(c1,x,'s',d1['src'][1],d1['a'],s1),ann(c2,x,'s',d1['src'][1],d2['a'],s2),m,depth+1); return
        if r1=='FOp' and r2=='FOp':
            F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
            if y!=x:
                if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
                F2=R.rename_d(F2,y,x)
            c1p,q1,st1=pop_any(c1); c2p,q2,st2=pop_any(c2)
            rec(d1['a'],d2['a'],empty(c1),empty(c2),m,depth+1)
            rec(F1,F2,ann(c1p,x,'e',d1['alpha'],q1,st1),ann(c2p,x,'e',d1['alpha'],q2,st2),m,depth+1); return
        raise ValueError((r1,r2))
    finally:
        PAIRS.pop(); VISITS.pop()

def main():
    k=int(sys.argv[1]); kc=int(sys.argv[2]); maxruns=int(sys.argv[3])
    cfgs=S.families()
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    y,v,x,w='y','v','x','w'
    cfgs.append((((v,'e',A(F(y),A(A(TOP,TOP),A(TOP,TOP)))),(y,'e',L(TOP,A(B(0),B(0))))),(),F(v)))
    cfgs.append((((x,'e',L(TOP,A(B(0),B(0)))),(v,'e',A(TOP,TOP))),(),A(F(x),L(TOP,A(B(0),F(v))))))
    cfgs.append((((x,'e',L(TOP,A(B(0),B(0)))),(v,'e',A(TOP,TOP))),(),A(F(x),L(TOP,A(A(B(0),B(0)),F(v))))))
    only=[int(a) for a in sys.argv[4].split(',')] if len(sys.argv)>4 else None
    for i,(G,s,t) in enumerate(cfgs):
        if only and i not in only: continue
        R._dmemo.clear(); gc.collect()
        try: ds=R.derivs(G,s,t,k); cs=R.ctx_derivs(G,s,kc)
        except MemoryError:
            R._dmemo.clear(); gc.collect(); print(f"[{i}] skipped (memory)",flush=True); continue
        if len(ds)>30000 or len(cs)>30000: print(f"[{i}] skipped ({len(ds)} d, {len(cs)} c)",flush=True); continue
        total=len(ds)**2*len(cs)**2
        rng=random.Random(i)
        quads=((rng.choice(ds),rng.choice(ds),rng.choice(cs),rng.choice(cs)) for _ in range(min(total,maxruns)))
        n=0
        for (d1,d2,c1,c2) in quads:
            import copy
            d1=copy.deepcopy(d1); d2=copy.deepcopy(d2); c1=copy.deepcopy(c1); c2=copy.deepcopy(c2)
            tag(d1,'d1'); tag(d2,'d2'); tag_c(c1,'c1'); tag_c(c2,'c2')
            CLOCK[0]=0; PATH.clear(); PAIRS.clear(); TRIG.clear(); VISITS.clear()
            meta=[dict(anchor_bt=10**9,frame=('orig',0)),dict(anchor_bt=10**9,frame=('orig',1))]
            try: rec(d1,d2,c1,c2,meta); n+=1
            except Budget: ST['budget']+=1
            except (MemoryError,RecursionError): ST['crash']+=1
        print(f"[{i}] {S.show(t)} @ {S.showG(G)};{S.showS(s)} — {n} runs",flush=True)
    for kk,vv in sorted(ST.items(),key=str): print(kk,vv)
    for name,(path,extra) in EX.items():
        print("EXAMPLE",name,extra)
        for ev in path: print("   ",ev)
main()
