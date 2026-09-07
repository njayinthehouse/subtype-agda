"""Search for a lexicographic order on pairs of input positions that decreases on every call of
the diamond recursion. Uses position-probe's tagging; collects the union call graph of all runs
of each configuration; evaluates candidate keys built from per-position features."""
import sys, copy, itertools, collections, random
from importlib.machinery import SourceFileLoader
P=SourceFileLoader('P','/home/egret/gimmick/1/MPSS/position-probe.py').load_module()
R,S=P.R,P.S
BIG=10**6

# refine tagging of reflexivity pieces: which variable / stack entry they are for
_orig_extract=R.extract
def extract_tagged(c,x):
    d=_orig_extract(c,x)
    if d.get('pos',('?',))[0][0]=='refl': P.tag(d,('refl-ann',x))
    return d
R.extract=extract_tagged
_orig_pop=R.pop
def pop_tagged(c):
    c1,q=_orig_pop(c)
    if q.get('pos',('?',))[0][0]=='refl': P.tag(q,('refl-stk',S.show(c[2][0]) if c[0]=='Refl' else '?'))
    return c1,q
R.pop=pop_tagged

def features(posn,G0,d):
    """posn=(base,path); G0 = original context (head first); d = the node (for sizes)"""
    base,path=posn
    names=[e[0] for e in reversed(G0)]
    if base in ('d1','d2'): tr=BIG
    elif isinstance(base,tuple):
        kind=base[0]
        if kind in ('c1','c2'):
            if base[1]=='ann': tr=names.index(base[2]) if base[2] in names else BIG-1
            else: tr=BIG-2
        elif kind=='refl-ann': tr=names.index(base[1]) if base[1] in names else BIG-1
        elif kind=='refl-stk': tr=BIG-2
        else: tr=BIG-3
    else: tr=BIG-3
    return dict(tr=tr, dp=len(path), sz=R.size(d), pr=R.pros(d))

NODEF={}
def rec_collect(d1,d2,c1,c2,G0,edges,parent):
    st=(P.pos(d1),P.pos(d2))
    NODEF[st]=(features(st[0],G0,d1),features(st[1],G0,d2))
    r1,r2=d1['rule'],d2['rule']
    leaf=(r1,r2) in P.LEAF
    if parent is not None and not leaf: edges.add((parent,st))
    return st

# monkeypatch P.rec to record features: reuse P.rec by wrapping
def make_rec(G0,edges):
    orig=P.rec
    def rec(d1,d2,c1,c2,path):
        parent=path[-1] if path else None
        rec_collect(d1,d2,c1,c2,G0,edges,parent)
        return orig(d1,d2,c1,c2,path)
    return rec

def candidate_keys():
    # per-side features: tr, dp(neg), sz, pr ; combos
    feats={}
    for side in (0,1):
        feats[f'tr{side}']=lambda f,s=side: f[s]['tr']
        feats[f'ndp{side}']=lambda f,s=side: -f[s]['dp']
        feats[f'sz{side}']=lambda f,s=side: f[s]['sz']
        feats[f'pr{side}']=lambda f,s=side: f[s]['pr']
    feats['trmax']=lambda f: max(f[0]['tr'],f[1]['tr'])
    feats['trmin']=lambda f: min(f[0]['tr'],f[1]['tr'])
    feats['trsum']=lambda f: f[0]['tr']+f[1]['tr']
    feats['szsum']=lambda f: f[0]['sz']+f[1]['sz']
    feats['szmax']=lambda f: max(f[0]['sz'],f[1]['sz'])
    feats['szmin']=lambda f: min(f[0]['sz'],f[1]['sz'])
    feats['prsum']=lambda f: f[0]['pr']+f[1]['pr']
    feats['prmax']=lambda f: max(f[0]['pr'],f[1]['pr'])
    feats['ndpsum']=lambda f: -(f[0]['dp']+f[1]['dp'])
    feats['ndpmax']=lambda f: -max(f[0]['dp'],f[1]['dp'])
    feats['ndpmin']=lambda f: -min(f[0]['dp'],f[1]['dp'])
    feats['ms_tr_sz']=lambda f: tuple(sorted([(f[0]['tr'],f[0]['sz']),(f[1]['tr'],f[1]['sz'])],reverse=True))
    feats['ms_tr_pr_sz']=lambda f: tuple(sorted([(f[0]['tr'],f[0]['pr'],f[0]['sz']),(f[1]['tr'],f[1]['pr'],f[1]['sz'])],reverse=True))
    feats['ms_pr_sz']=lambda f: tuple(sorted([(f[0]['pr'],f[0]['sz']),(f[1]['pr'],f[1]['sz'])],reverse=True))
    feats['ms_sz']=lambda f: tuple(sorted([f[0]['sz'],f[1]['sz']],reverse=True))
    feats['ms_tr']=lambda f: tuple(sorted([f[0]['tr'],f[1]['tr']],reverse=True))
    feats['trsz_prod']=lambda f: (f[0]['tr']+1)*(f[1]['sz'])+(f[1]['tr']+1)*(f[0]['sz'])
    feats['szprod']=lambda f: f[0]['sz']*f[1]['sz']
    feats['prsz_prod']=lambda f: (f[0]['pr']+1)*f[1]['sz']+(f[1]['pr']+1)*f[0]['sz']
    names=list(feats)
    cands={}
    for n in range(1,4):
        for combo in itertools.permutations(names,n):
            cands[','.join(combo)]=[feats[c] for c in combo]
    return cands

def evaluate(edges,cands):
    alive=dict(cands); bad=collections.Counter()
    for (a,b) in edges:
        fa,fb=NODEF[a],NODEF[b]
        for name in list(alive):
            ka=tuple(f(fa) for f in alive[name]); kb=tuple(f(fb) for f in alive[name])
            if not kb<ka: del alive[name]; bad[name]+=1
    return alive

def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    AP=SourceFileLoader('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    R._weaken=P._weaken_pos; R.refl_deriv=P.refl_pos; R.extract=extract_tagged; R.pop=pop_tagged
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    cands=candidate_keys(); print(len(cands),"candidate keys",flush=True)
    alive=dict(cands)
    for i,(G,s,t) in enumerate(cfgs):
        R._dmemo.clear()
        try: ds=R.derivs(G,s,t,k); cs=R.ctx_derivs(G,s,kc)
        except MemoryError: R._dmemo.clear(); print("skip (memory)",flush=True); continue
        if len(cs)>300: rng0=random.Random(len(cs)); cs=[rng0.choice(cs) for _ in range(300)]
        if len(ds)>400: rng0=random.Random(len(ds)); ds=[rng0.choice(ds) for _ in range(400)]
        tq=len(ds)**2*len(cs)**2
        if tq>maxruns:
            rng=random.Random(tq); quads=((rng.choice(ds),rng.choice(ds),rng.choice(cs),rng.choice(cs)) for _ in range(maxruns))
        else: quads=((a,b,c,d) for a in ds for b in ds for c in cs for d in cs)
        edges=set(); NODEF.clear()
        saved=P.rec; P.rec=make_rec(G,edges)
        n=0
        for (d1,d2,c1,c2) in quads:
            d1=copy.deepcopy(d1); d2=copy.deepcopy(d2); c1=copy.deepcopy(c1); c2=copy.deepcopy(c2)
            P.tag(d1,'d1'); P.tag(d2,'d2'); P.tag_ctx(c1,'c1'); P.tag_ctx(c2,'c2')
            P.CALLS[0]=0
            try: P.rec(d1,d2,c1,c2,()); n+=1
            except (P.Budget,RecursionError): continue
            except MemoryError: continue
        P.rec=saved
        alive=evaluate(edges,alive)
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {n} runs, {len(edges)} edges, {len(alive)} keys survive",flush=True)
        if len(alive)<=30: print("   ",sorted(alive),flush=True)
        if not alive: break
    print("\nSURVIVORS:",sorted(alive),flush=True)

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
