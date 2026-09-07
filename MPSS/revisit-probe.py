"""When one side revisits an input position along a path, where is the other side relative to
where it was at the earlier visit? Classifies the partner's position at a revisit as: strictly
deeper in the same tree ('desc'), an ancestor ('anc'), the same node ('same'), elsewhere in the
same tree ('other-same-tree'), or in a different tree ('other-tree')."""
import sys, copy, collections, random
from importlib.machinery import SourceFileLoader
P=SourceFileLoader('P','/home/egret/gimmick/1/MPSS/position-probe.py').load_module()
R,S=P.R,P.S
STATS=collections.Counter(); EX={}

def rel(old,new):
    (b1,p1),(b2,p2)=old,new
    if b1!=b2: return 'other-tree'
    if p1==p2: return 'same'
    if p2[:len(p1)]==p1: return 'desc'
    if p1[:len(p2)]==p2: return 'anc'
    return 'other-same-tree'

def make_rec():
    orig=P.rec
    def rec(d1,d2,c1,c2,path):
        st=(P.pos(d1),P.pos(d2))
        if (d1['rule'],d2['rule']) not in P.LEAF:
            for (q1,q2) in path:
                if q1==st[0]:
                    r=rel(q2,st[1]); STATS['side1-revisit:'+r]+=1
                    if r not in ('desc','other-tree') and ('1',r) not in EX: EX[('1',r)]=(S.show(d1['src']),S.showG(d1['G']),S.showS(d1['s']),q2,st[1])
                if q2==st[1]:
                    r=rel(q1,st[0]); STATS['side2-revisit:'+r]+=1
                    if r not in ('desc','other-tree') and ('2',r) not in EX: EX[('2',r)]=(S.show(d2['src']),S.showG(d2['G']),S.showS(d2['s']),q1,st[0])
        return orig(d1,d2,c1,c2,path)
    return rec

def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    AP=SourceFileLoader('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    R._weaken=P._weaken_pos; R.refl_deriv=P.refl_pos
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    P.rec=make_rec()
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
        n=0
        for (d1,d2,c1,c2) in quads:
            d1=copy.deepcopy(d1); d2=copy.deepcopy(d2); c1=copy.deepcopy(c1); c2=copy.deepcopy(c2)
            P.tag(d1,'d1'); P.tag(d2,'d2'); P.tag_ctx(c1,'c1'); P.tag_ctx(c2,'c2')
            P.CALLS[0]=0
            try: P.rec(d1,d2,c1,c2,()); n+=1
            except (P.Budget,RecursionError,MemoryError): continue
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {n} runs; {dict(STATS)}",flush=True)
    print("\nFINAL",dict(STATS),flush=True)
    for key,ex in EX.items(): print("EXAMPLE",key,ex,flush=True)

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
