"""Trigger forest. Every pull copies a piece; every node of the copy is stamped with the pull's
index. A pull's trigger is the partner's promotion node at the focus; its parent in the forest is
the pull that made the copy containing the trigger (0 for the original derivations). Along each
path this probe extracts the chains of the forest and reports their depth and the sequence of
(side, kind, variable, binding position) along the deepest ones."""
import sys, copy, collections, random
from importlib.machinery import SourceFileLoader
P=SourceFileLoader('P','/home/egret/gimmick/1/MPSS/position-probe.py').load_module()
R,S=P.R,P.S
KEYS=('e','o','p','F','a')
def stamp(d,c):
    d['copy']=c
    for k in KEYS:
        if k in d: stamp(d[k],c)
def copystamp(src,dst):
    if 'copy' in src: dst['copy']=src['copy']
    for k in KEYS:
        if k in src and k in dst: copystamp(src[k],dst[k])
_orig_weaken=R._weaken
def weaken_s(d,Gt,sx):
    r=_orig_weaken(d,Gt,sx); P.copy_pos(d,r); copystamp(d,r); return r
MAX=collections.Counter(); HIST=collections.Counter(); WORST={}
def bt(G,x):
    names=[e[0] for e in reversed(G)]
    return names.index(x) if x in names else -1

def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    AP=SourceFileLoader('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    R._weaken=weaken_s; R.refl_deriv=P.refl_pos
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    orig=P.rec; CUR=[None]; PULLS=[]   # PULLS[i] = dict(side,kind,var,bt,parent)
    def rec(d1,d2,c1,c2,path):
        r1,r2=d1['rule'],d2['rule']; G0=CUR[0]
        if (r1,r2) in P.LEAF:
            # analyse chains reachable from the pulls on this path
            mine=[e for e in path if isinstance(e,int)]
            if mine:
                depth={}
                def dep(i):
                    if i in depth: return depth[i]
                    par=PULLS[i]['parent']; depth[i]=1+(dep(par) if par>=0 else 0); return depth[i]
                dmax=max(dep(i) for i in mine); HIST[dmax]+=1
                if dmax>MAX['chain']:
                    MAX['chain']=dmax
                    # reconstruct the deepest chain
                    i=max(mine,key=dep); ch=[]
                    while i>=0:
                        p=PULLS[i]; ch.append((p['side'],p['kind'],p['var'],p['bt'])); i=p['parent']
                    WORST['chain']=(list(reversed(ch)),S.show(d1['G'] and d1['G'][-1][2]) if False else S.showG(d1['G']))
            return orig(d1,d2,c1,c2,path)
        if r1=='Var' and r2=='Pro' or r1=='Pro' and r2=='Var':
            side=1 if r1=='Var' else 2
            puller,partner=(d1,d2) if side==1 else (d2,d1)
            x=puller['x']; kind='ext' if x in S.dom(G0) else 'int'
            idx=len(PULLS)
            PULLS.append(dict(side=side,kind=kind,var=x,bt=bt(puller['G'],x),parent=partner.get('copy',-1)))
            # stamp the piece: wrap R.weaken/extract for this call by stamping after the fact
            saved=R.weaken
            def weaken_stamped(d,Gt,sx,_idx=idx,_saved=saved):
                r=_saved(d,Gt,sx); stamp(r,_idx); return r
            R.weaken=weaken_stamped
            try: return orig(d1,d2,c1,c2,path+(idx,))
            finally: R.weaken=saved
        return orig(d1,d2,c1,c2,path)
    P.rec=rec
    for i,(G,s,t) in enumerate(cfgs):
        CUR[0]=G; R._dmemo.clear()
        try: ds=R.derivs(G,s,t,k); cs=R.ctx_derivs(G,s,kc)
        except MemoryError: R._dmemo.clear(); print("skip",flush=True); continue
        if len(cs)>300: rng0=random.Random(len(cs)); cs=[rng0.choice(cs) for _ in range(300)]
        if len(ds)>400: rng0=random.Random(len(ds)); ds=[rng0.choice(ds) for _ in range(400)]
        tq=len(ds)**2*len(cs)**2
        if tq>maxruns:
            rng=random.Random(tq); quads=((rng.choice(ds),rng.choice(ds),rng.choice(cs),rng.choice(cs)) for _ in range(maxruns))
        else: quads=((a,b,c,d) for a in ds for b in ds for c in cs for d in cs)
        n=0
        for (d1,d2,c1,c2) in quads:
            d1=copy.deepcopy(d1); d2=copy.deepcopy(d2); c1=copy.deepcopy(c1); c2=copy.deepcopy(c2)
            P.tag(d1,'d1'); P.tag(d2,'d2'); P.tag_ctx(c1,'c1'); P.tag_ctx(c2,'c2'); stamp(d1,-1); stamp(d2,-1)
            PULLS.clear(); P.CALLS[0]=0
            try: P.rec(d1,d2,c1,c2,()); n+=1
            except (P.Budget,MemoryError): continue
            except RecursionError: import traceback; traceback.print_exc(limit=3); continue
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {n} runs; max chain {MAX['chain']}; depth histogram {dict(sorted(HIST.items()))}",flush=True)
    print("\nFINAL max chain",MAX['chain'],"histogram",dict(sorted(HIST.items())),flush=True)
    print("DEEPEST CHAIN (root first: side, kind, var, bt):",WORST.get('chain'),flush=True)

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
