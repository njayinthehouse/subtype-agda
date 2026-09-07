"""Do input positions recur along a path of the diamond recursion?

Every derivation the recursion handles is a copy (weakened, pushed, renamed) of a subtree of one
of the four inputs, or a reflexivity derivation. Tag every input node with its position and carry
the tag through the copies. Then, along each path of the recursion, record the pair of positions
of the two current materials and check whether a pair ever recurs. If it never does, the recursion
is bounded by the square of the number of input positions, and the proof obligation becomes an
invariant on paths rather than a measure on states.
"""
import sys, copy, collections, random
from importlib.machinery import SourceFileLoader
R = SourceFileLoader('dr','/home/egret/gimmick/1/MPSS/diamond-recursion.py').load_module()
S = R.S
KEYS=('e','o','p','F','a')
LEAF={('Var','Var'),('Top','Top'),('TAp','TAp'),('TAp','App'),('App','TAp')}

def tag(d,base,path=()):
    d['pos']=(base,path)
    for k in KEYS:
        if k in d: tag(d[k],base,path+(k,))
def tag_ctx(c,base,idx=0):
    if c[0]=='Refl': return
    if c[0]=='Ann': tag(c[6],(base,'ann',c[2])); tag_ctx(c[1],base)
    if c[0]=='Stk': tag(c[4],(base,'stk',S.show(c[2]))); tag_ctx(c[1],base)

# carry positions through weakening (which rebuilds nodes)
_orig_weaken=R._weaken
def copy_pos(src,dst):
    if 'pos' in src: dst['pos']=src['pos']
    for k in KEYS:
        if k in src and k in dst: copy_pos(src[k],dst[k])
def _weaken_pos(d,Gt,sx):
    r=_orig_weaken(d,Gt,sx); copy_pos(d,r); return r
R._weaken=_weaken_pos
_orig_refl=R.refl_deriv
def refl_pos(G,s,t):
    r=_orig_refl(G,s,t); tag(r,('refl',S.show(t))); return r
R.refl_deriv=refl_pos

CALLS=[0]; REPEATS=[]; PULLS=[]; EDGES=set()
class Budget(Exception): pass

def pos(d): return d.get('pos',('?',))

def rec(d1,d2,c1,c2,path):
    CALLS[0]+=1
    if CALLS[0]>200000: raise Budget()
    st=(pos(d1),pos(d2))
    r1,r2=d1['rule'],d2['rule']
    if (r1,r2) not in LEAF and st in path:
        REPEATS.append((path,st,d1,d2))
    if path and (r1,r2) not in LEAF: EDGES.add((path[-1],st))
    path=path+(st,)
    if (r1,r2) in LEAF: return
    if r1=='Pro' and r2=='Pro': rec(d1['e'],d2['e'],c1,c2,path); return
    if r1=='Var' and r2=='Pro':
        piece=R.weaken(R.extract(c1,d1['x']),d1['G'],d1['s']); PULLS.append((0,d1['x'],pos(piece)))
        rec(piece,d2['e'],c1,c2,path); return
    if r1=='Pro' and r2=='Var':
        piece=R.weaken(R.extract(c2,d2['x']),d2['G'],d2['s']); PULLS.append((1,d2['x'],pos(piece)))
        rec(d1['e'],piece,c1,c2,path); return
    if r1=='App' and r2=='App':
        rec(d1['o'],d2['o'],R.stk(c1,d1['p']),R.stk(c2,d2['p']),path)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),path); return
    if r1=='App' and r2=='Bet':
        o1=d1['o']; x=o1['x']; F2=d2['F']; y=d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(o1)))
            F2=R.rename_d(F2,y,x)
        F2w=R._weaken(F2,((x,'e',d1['src'][2]),)+d1['G'],())
        rec(o1['F'],F2w,R.ann(c1,x,'e',d1['src'][2],d1['p']),R.ann(c2,x,'e',d1['src'][2],d2['p']),path)
        rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),path); return
    if r1=='Bet' and r2=='App':
        # swap sides; positions are side-tagged so the pair is recorded swapped, which is harmless
        rec(d2,d1,c2,c1,tuple((e if (not isinstance(e,tuple) or (e and e[0] in ('TABLE','EV'))) else (e[1],e[0]) if len(e)==2 else (e[2],e[3],e[0],e[1])) for e in path[:-1])); return
    if r1=='Bet' and r2=='Bet':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        rec(F1,F2,c1,c2,path); rec(d1['p'],d2['p'],R.empty(c1),R.empty(c2),path); return
    if r1=='Fun' and r2=='Fun':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        rec(d1['a'],d2['a'],c1,c2,path)
        rec(F1,F2,R.ann(c1,x,'s',d1['src'][1],d1['a']),R.ann(c2,x,'s',d1['src'][1],d2['a']),path); return
    if r1=='FOp' and r2=='FOp':
        F1,F2=d1['F'],d2['F']; x,y=d1['x'],d2['x']
        if y!=x:
            if x in R.names_d(F2): F2=R.rename_d(F2,x,R.fresh_name(R.names_d(F2)|R.names_d(F1)))
            F2=R.rename_d(F2,y,x)
        c1p,q1=R.pop_any(c1); c2p,q2=R.pop_any(c2)
        rec(d1['a'],d2['a'],R.empty(c1),R.empty(c2),path)
        rec(F1,F2,R.ann(c1p,x,'e',d1['alpha'],q1),R.ann(c2p,x,'e',d1['alpha'],q2),path); return
    raise ValueError("unexpected %s/%s"%(r1,r2))

def acyclic(edges):
    g=collections.defaultdict(list)
    for a,b in edges: g[a].append(b)
    state={}
    for start in list(g):
        if start in state: continue
        stack=[(start,iter(g[start]))]; state[start]=1
        while stack:
            node,it=stack[-1]
            for nxt in it:
                if state.get(nxt)==1: return False
                if nxt not in state:
                    state[nxt]=1; stack.append((nxt,iter(g[nxt]))); break
            else:
                state[node]=2; stack.pop()
    return True

def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    try:
        from importlib.machinery import SourceFileLoader as L2
        AP=L2('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    except Exception as ex: print("no adversarial configs:",ex)
    # loading anchor-probe re-executes diamond-recursion under the same module name, undoing the
    # patches above; re-apply them
    R._weaken=_weaken_pos; R.refl_deriv=refl_pos
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    total_runs=0; total_rep=0; worst_len=0; shown=0
    for i,(G,s,t) in enumerate(cfgs):
        R._dmemo.clear()
        try: ds=R.derivs(G,s,t,k); cs=R.ctx_derivs(G,s,kc)
        except MemoryError: R._dmemo.clear(); print(f"[{i+1}/{len(cfgs)}] SKIPPED (MemoryError)",flush=True); continue
        if len(cs)>300: rng0=random.Random(len(cs)); cs=[rng0.choice(cs) for _ in range(300)]
        if len(ds)>400: rng0=random.Random(len(ds)); ds=[rng0.choice(ds) for _ in range(400)]
        tq=len(ds)**2*len(cs)**2
        if tq>maxruns:
            rng=random.Random(tq); quads=((rng.choice(ds),rng.choice(ds),rng.choice(cs),rng.choice(cs)) for _ in range(maxruns)); nq=maxruns
        else:
            quads=((a,b,c,d) for a in ds for b in ds for c in cs for d in cs); nq=tq
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {nq} runs",flush=True)
        rep_here=0; cyc_here=0; cfg_edges=set()
        for (d1,d2,c1,c2) in quads:
            d1=copy.deepcopy(d1); d2=copy.deepcopy(d2); c1=copy.deepcopy(c1); c2=copy.deepcopy(c2)
            tag(d1,'d1'); tag(d2,'d2'); tag_ctx(c1,'c1'); tag_ctx(c2,'c2')
            REPEATS.clear(); PULLS.clear(); CALLS[0]=0; EDGES.clear()
            try: rec(d1,d2,c1,c2,())
            except Budget: print("  budget hit",flush=True); continue
            except RecursionError: print("  recursion limit",flush=True); continue
            total_runs+=1
            if not acyclic(EDGES):
                cyc_here+=1
                if cyc_here<=2: print(f"  CYCLE in the union call graph of one run: {S.show(d1['src'])} t1={S.show(d1['tgt'])} t2={S.show(d2['tgt'])}",flush=True)
            cfg_edges|=EDGES
            if REPEATS:
                rep_here+=len(REPEATS); total_rep+=len(REPEATS)
                if shown<3:
                    shown+=1
                    path,st,a,b=REPEATS[0]
                    print(f"  REPEAT of {st} after {len(path)} steps; material {S.show(a['src'])} | {S.show(b['src'])} at {S.showG(a['G'])};{S.showS(a['s'])}",flush=True)
                    print("     path positions:",[ (p[0][0],p[1][0]) for p in path][:12],flush=True)
        print(f"   repeats: {rep_here}; runs whose union call graph has a cycle: {cyc_here}; all runs' graphs together acyclic: {acyclic(cfg_edges)}",flush=True)
    print(f"\n{total_runs} runs, {total_rep} repeated position pairs along a path",flush=True)

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 5000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
