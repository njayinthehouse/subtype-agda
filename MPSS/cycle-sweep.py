"""Cycle-detection sweep over the diamond recursion (based on hist4.py).

Every input node gets id=(tree, path); copies keep ids. Along each root-to-leaf path we check
 (A) no trigger id consumed twice                                   [counted only]
 (B) no pair of origin ids recurs                                   [counted only]
 (C) no stored premise stamp fetched twice
 (V) no (side, frame, origin id) visited twice
 (CYCLE) no exact repeat of the full state (d1,d2,c1,c2), canonical up to renaming of names
         (names -> indices by first occurrence in a fixed traversal).

Usage: python3 cycle-sweep.py SHARD NSHARDS [NRAND] [OUTDIR]
"""
import sys, collections, random, gc, json, copy, signal, time, os
sys.setrecursionlimit(300000)
from importlib.machinery import SourceFileLoader
R=SourceFileLoader('dr','/home/egret/gimmick/1/MPSS/diamond-recursion.py').load_module()
S=R.S
A,L,F,B,TOP=S.A,S.L,S.F,S.B,S.TOP
KEYS=('e','o','p','F','a')

# ---------------------------------------------------------------- origin tagging (hist4)
def unshare(d):
    """rebuild the tree with fresh nodes: derivs() memoizes, so an enumerated tree can hold the same
    dict object at two positions (e.g. a Me-Bet body and a deeper Me-Bet body over the same key);
    copy.deepcopy keeps that aliasing and tag() then gives both positions the last path's id."""
    e={k:v for k,v in d.items() if k not in KEYS}
    for k in KEYS:
        if k in d: e[k]=unshare(d[k])
    return e
def unshare_c(c):
    if c[0]=='Refl': return c
    if c[0]=='Ann': return ('Ann',unshare_c(c[1]),c[2],c[3],c[4],c[5],unshare(c[6]))
    return ('Stk',unshare_c(c[1]),c[2],c[3],unshare(c[4]))
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
TICKS=100000
class Budget(Exception): pass
class Timeout(Exception): pass
def tick():
    CLOCK[0]+=1
    if CLOCK[0]>TICKS: raise Budget()
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

# ---------------------------------------------------------------- canonical state
def canon_state(d1,d2,c1,c2):
    ren={}
    def nm(x):
        i=ren.get(x)
        if i is None: i=ren[x]=len(ren)
        return i
    def ct(t):
        c=t[0]
        if c=='f': return ('f',nm(t[1]))
        if c=='b' or c=='T': return t
        return (c,ct(t[1]),ct(t[2]))
    def cG(G): return tuple((nm(n),k,ct(t)) for (n,k,t) in G)
    def cs(s): return tuple(ct(a) for a in s)
    def cd(d):
        out=[d['rule'],ct(d['src']),ct(d['tgt']),cG(d['G']),cs(d['s'])]
        if 'x' in d: out.append(('x',nm(d['x'])))
        if 'alpha' in d: out.append(('alpha',ct(d['alpha'])))
        if 'ann' in d: out.append(('ann',ct(d['ann'])))
        for k in KEYS:
            if k in d: out.append((k,cd(d[k])))
        return tuple(out)
    def cc(c):
        if c[0]=='Refl': return ('Refl',cG(c[1]),cs(c[2]))
        if c[0]=='Ann': return ('Ann',cc(c[1]),nm(c[2]),c[3],ct(c[4]),ct(c[5]),cd(c[6]))
        return ('Stk',cc(c[1]),ct(c[2]),ct(c[3]),cd(c[4]))
    return (cd(d1),cd(d2),cc(c1),cc(c2))

# ---------------------------------------------------------------- path-local checks
ST=collections.Counter(); EX={}
PATH=[]      # pull events along the current path
PAIRS=[]     # (id1,id2) along the current path
TRIG=[]      # trigger ids along the current path
VISITS=[]
RULES=[]     # (depth, r1, r2, src) along the current path
STATES={}    # canonical state -> depth along the current path
SLIST=[]
CUR={}       # current configuration / quadruple description
def cfg_size(G,s,t):
    def sz(t): return 1 if t[0] in 'bfT' else 1+sz(t[1])+sz(t[2])
    return sz(t)+sum(sz(a) for (_,_,a) in G)+sum(sz(a) for a in s)
def record(name,extra):
    key=(CUR['size'],len(PATH),CLOCK[0])
    if name in EX and EX[name]['key']<=list(key): return
    EX[name]=dict(key=list(key),cfg=CUR['cfg'],k=CUR['k'],kc=CUR['kc'],quad=CUR['quad'],
                  inputs=CUR['inputs'],extra=extra,path=[dict(e) for e in PATH],
                  rules=list(RULES[-80:]))
def check_pull(ev):
    ST['pulls']+=1; ST[ev['kind']]+=1
    if ev['trigger'] in TRIG:
        ST['A_trigger_repeat']+=1
    if ev['fetched'] is not None:
        if ev['fetched'] in [e['fetched'] for e in PATH]:
            ST['C_stored_piece_refetched']+=1; record('C',ev)
        last=max([e['time'] for e in PATH if e['side']==ev['side']] or [0])
        if ev['fetched'][1]<last: ST['fetched_stored_before_own_last_pull']+=1
        else: ST['fetched_stored_after_own_last_pull']+=1
        if ev['kind']=='ext': ST['ext_fetch_stored']+=1
    else:
        if ev['kind']=='int': ST['int_fetch_original']+=1
def check_pair(d1,d2,m):
    p=(d1.get('id'),d2.get('id'))
    if p in PAIRS: ST['B_pair_repeat']+=1
    v0=(0,m[0]['frame'],d1.get('id')); v1=(1,m[1]['frame'],d2.get('id'))
    for v in (v0,v1):
        if any(v in pair for pair in VISITS): ST['V_frame_position_revisit']+=1; record('V',v)
    VISITS.append((v0,v1))
    return p
def rec(d1,d2,c1,c2,meta,depth=0):
    t=tick()
    r1,r2=d1['rule'],d2['rule']
    pr=check_pair(d1,d2,meta); PAIRS.append(pr)
    RULES.append((depth,r1,r2,S.show(d1['src'])))
    st=canon_state(d1,d2,c1,c2)
    first=STATES.get(st)
    if first is not None:
        ST['CYCLE']+=1
        record('CYCLE',dict(depth=depth,first_depth=first,rules=(r1,r2),src=S.show(d1['src']),
                            t1=S.show(d1['tgt']),t2=S.show(d2['tgt']),G=S.showG(d1['G']),s=S.showS(d1['s']),
                            loop=[r for r in RULES if r[0]>=first]))
        PAIRS.pop(); VISITS.pop(); RULES.pop()
        return          # prune: the recursion from here repeats forever
    STATES[st]=depth; SLIST.append(st)
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
        PAIRS.pop(); VISITS.pop(); RULES.pop()
        SLIST.pop(); del STATES[st]

def reset_path():
    CLOCK[0]=0; PATH.clear(); PAIRS.clear(); TRIG.clear(); VISITS.clear(); RULES.clear(); STATES.clear(); SLIST.clear()

# ---------------------------------------------------------------- configurations
def all_cfgs(nrand):
    cfgs=list(S.families())
    y,v,x,w,u='y','v','x','w','u'
    cfgs.append((((v,'e',A(F(y),A(A(TOP,TOP),A(TOP,TOP)))),(y,'e',L(TOP,A(B(0),B(0))))),(),F(v)))
    cfgs.append((((x,'e',L(TOP,A(B(0),B(0)))),(v,'e',A(TOP,TOP))),(),A(F(x),L(TOP,A(B(0),F(v))))))
    cfgs.append((((x,'e',L(TOP,A(B(0),B(0)))),(v,'e',A(TOP,TOP))),(),A(F(x),L(TOP,A(A(B(0),B(0)),F(v))))))
    # hist4cfg.py's configuration
    cfgs.append((((u,'e',L(TOP,A(F(w),B(0)))),(w,'e',L(TOP,B(0)))),(),A(F(u),F(u))))
    rng=random.Random(20260912)
    cfgs += [S.rand_cfg(rng) for _ in range(nrand)]
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    # dedupe, keeping order
    seen=set(); out=[]
    for c in cfgs:
        if c in seen: continue
        seen.add(c); out.append(c)
    return out

def _alarm(signum,frame): raise Timeout()

def main():
    shard=int(sys.argv[1]); nsh=int(sys.argv[2])
    nrand=int(sys.argv[3]) if len(sys.argv)>3 else 200
    outdir=sys.argv[4] if len(sys.argv)>4 else os.path.dirname(os.path.abspath(__file__))
    cfgs=all_cfgs(nrand)
    items=[(ci,k,kc) for (k,kc) in ((2,1),(2,2),(3,1),(3,2)) for ci in range(len(cfgs))]
    mine=[it for (i,it) in enumerate(items) if i%nsh==shard]
    print(f"shard {shard}/{nsh}: {len(cfgs)} configurations, {len(mine)} items",flush=True)
    signal.signal(signal.SIGALRM,_alarm)
    t0=time.time(); nruns=0
    for (ci,k,kc) in mine:
        G,s,t=cfgs[ci]
        label=f"[{ci} k={k} kc={kc}] {S.show(t)} @ {S.showG(G)};{S.showS(s)}"
        R._dmemo.clear(); gc.collect()
        signal.alarm(600)
        try: ds=R.derivs(G,s,t,k); cs=R.ctx_derivs(G,s,kc)
        except MemoryError:
            signal.alarm(0); R._dmemo.clear(); gc.collect(); ST['skipped_memory']+=1; print(f"{label} skipped (memory)",flush=True); continue
        except RecursionError:
            signal.alarm(0); R._dmemo.clear(); gc.collect(); ST['skipped_recursion']+=1; print(f"{label} skipped (recursion)",flush=True); continue
        except Timeout:
            R._dmemo.clear(); gc.collect(); ST['skipped_timeout']+=1; print(f"{label} skipped (enumeration timeout)",flush=True); continue
        signal.alarm(0)
        if len(ds)>30000 or len(cs)>30000:
            ST['skipped_size']+=1; print(f"{label} skipped ({len(ds)} d, {len(cs)} c)",flush=True); R._dmemo.clear(); gc.collect(); continue
        maxruns=300 if k==3 else 1000
        total=len(ds)**2*len(cs)**2
        rng=random.Random(ci*1000+k*10+kc)
        if total<=maxruns:
            quads=[(i1,i2,j1,j2) for i1 in range(len(ds)) for i2 in range(len(ds)) for j1 in range(len(cs)) for j2 in range(len(cs))]
        else:
            quads=[(rng.randrange(len(ds)),rng.randrange(len(ds)),rng.randrange(len(cs)),rng.randrange(len(cs))) for _ in range(maxruns)]
        CUR.update(size=cfg_size(G,s,t),cfg=f"{S.show(t)} @ {S.showG(G)};{S.showS(s)}",k=k,kc=kc)
        n=0; calls=0; cyc0=ST['CYCLE']; c0=ST['C_stored_piece_refetched']; v0=ST['V_frame_position_revisit']
        for (i1,i2,j1,j2) in quads:
            d1,d2,c1,c2=ds[i1],ds[i2],cs[j1],cs[j2]
            try:
                d1=unshare(d1); d2=unshare(d2); c1=unshare_c(c1); c2=unshare_c(c2)
            except (MemoryError,RecursionError):
                ST['crash']+=1; gc.collect(); continue
            tag(d1,'d1'); tag(d2,'d2'); tag_c(c1,'c1'); tag_c(c2,'c2')
            CUR['quad']=(i1,i2,j1,j2)
            CUR['inputs']=dict(t1=S.show(d1['tgt']),t2=S.show(d2['tgt']),
                               c1=f"{S.showG(R.cr_tgt(c1)[0])};{S.showS(R.cr_tgt(c1)[1])}",
                               c2=f"{S.showG(R.cr_tgt(c2)[0])};{S.showS(R.cr_tgt(c2)[1])}")
            reset_path()
            meta=[dict(anchor_bt=10**9,frame=('orig',0)),dict(anchor_bt=10**9,frame=('orig',1))]
            try: rec(d1,d2,c1,c2,meta); n+=1
            except Budget: ST['budget']+=1
            except (MemoryError,RecursionError): ST['crash']+=1; gc.collect()
            calls+=CLOCK[0]
            nruns+=1
        ST['calls']+=calls; ST['runs']+=n
        print(f"{label} — {len(ds)} d, {len(cs)} c, {n} runs, {calls} calls, "
              f"CYCLE +{ST['CYCLE']-cyc0}, C +{ST['C_stored_piece_refetched']-c0}, V +{ST['V_frame_position_revisit']-v0}  [{time.time()-t0:.0f}s]",flush=True)
        R._dmemo.clear(); gc.collect()
        # checkpoint results after every item
        dump(outdir,shard)
    dump(outdir,shard)
    print("DONE",flush=True)
    for kk,vv in sorted(ST.items(),key=str): print(kk,vv)
    for name,ex in EX.items():
        print("EXAMPLE",name,ex['extra'])
        print("    cfg:",ex['cfg'],"k=",ex['k'],"kc=",ex['kc'],"quad=",ex['quad'],ex['inputs'])
        for ev in ex['path']: print("   ",ev)

def dump(outdir,shard):
    with open(os.path.join(outdir,f"cycle_{shard}.json"),'w') as f:
        json.dump(dict(stats=dict(ST),examples=EX),f,default=str)

main()
