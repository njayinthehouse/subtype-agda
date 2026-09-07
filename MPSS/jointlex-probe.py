"""The joint frame list. Frames (copies of input trees, both sides) in creation order, each with the
position of the material last seen in it. At every call, find the oldest frame whose position
changed; record whether it moved later in pre-order (an advance), stayed, or moved earlier (a
regression). A potential that is lexicographic over the creation-ordered list decreases at every
call iff regressions never occur."""
import sys, copy, collections, random
from importlib.machinery import SourceFileLoader
FP=SourceFileLoader('FP','/home/egret/gimmick/1/MPSS/frame-probe.py').load_module()
P,R,S=FP.P,FP.R,FP.S
STATS=collections.Counter(); EX=[]
def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    AP=SourceFileLoader('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    R._weaken=FP.weaken_f; R.refl_deriv=P.refl_pos; R.extract=FP.extract_f; R.pop=FP.pop_f
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    orig=P.rec
    def rec(d1,d2,c1,c2,path):
        # path carries the frame table as its last dict entry
        table=None
        for e in reversed(path):
            if isinstance(e,tuple) and e and e[0]=='TABLE': table=e; break
        table=dict(table[1]) if table else {}
        f1,p1=d1.get('frame'),P.pos(d1); f2,p2=d2.get('frame'),P.pos(d2)
        if (d1['rule'],d2['rule']) not in P.LEAF:
            changes=[]
            for f,p in ((f1,p1),(f2,p2)):
                if f in table:
                    old=table[f]
                    if old[0]!=p[0]: changes.append((f,'base'))
                    elif old[1]==p[1]: pass
                    elif FP.later(old[1],p[1]): changes.append((f,'adv'))
                    else: changes.append((f,'REG'))
                else: changes.append((f,'new'))
            if changes:
                f,kind=min(changes)   # oldest frame that changed
                STATS[kind]+=1
                if kind=='REG' and len(EX)<5:
                    EX.append((S.show(d1['src']),S.showG(d1['G']),S.showS(d1['s']),table.get(f1),p1,table.get(f2),p2,f1,f2))
            table[f1]=p1; table[f2]=p2
        return orig(d1,d2,c1,c2,path+(('TABLE',tuple(sorted(table.items()))),))
    P.rec=rec
    for i,(G,s,t) in enumerate(cfgs):
        R._dmemo.clear()
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
            P.tag(d1,'d1'); P.tag(d2,'d2'); P.tag_ctx(c1,'c1'); P.tag_ctx(c2,'c2')
            FP.FRAME[0]=0; FP.setframe(d1,FP.newframe()); FP.setframe(d2,FP.newframe()); P.CALLS[0]=0
            try: P.rec(d1,d2,c1,c2,()); n+=1
            except (P.Budget,RecursionError,MemoryError): continue
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {n} runs; {dict(STATS)}",flush=True)
    print("\nFINAL",dict(STATS),flush=True)
    for ex in EX: print("REGRESSION",ex,flush=True)
if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
