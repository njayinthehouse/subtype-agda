"""Between two binder steps (Me-FOp/Me-FOp, Me-Fun/Me-Fun, Me-App/Me-Bet, Me-Bet/Me-Bet) along a
path, do the pulled bindings strictly descend in binding order? Records violations."""
import sys, copy, collections, random
from importlib.machinery import SourceFileLoader
P=SourceFileLoader('P','/home/egret/gimmick/1/MPSS/position-probe.py').load_module()
R,S=P.R,P.S
STATS=collections.Counter(); EX=[]
def bt(G,x):
    names=[e[0] for e in reversed(G)]
    return names.index(x) if x in names else -1
def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    AP=SourceFileLoader('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    R._weaken=P._weaken_pos; R.refl_deriv=P.refl_pos
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    orig=P.rec
    BIND={('FOp','FOp'),('Fun','Fun'),('App','Bet'),('Bet','App'),('Bet','Bet')}
    def rec(d1,d2,c1,c2,path):
        r1,r2=d1['rule'],d2['rule']
        ev=tuple(e for e in path if isinstance(e,tuple) and e and e[0]=='EV')
        last=ev[-1] if ev else None
        if (r1,r2) in BIND:
            return orig(d1,d2,c1,c2,path+(('EV','B'),))
        if (r1,r2) in (('Var','Pro'),('Pro','Var')):
            side=1 if r1=='Var' else 2
            d=d1 if side==1 else d2
            b=bt(d['G'],d['x'])
            if last is not None and last[1]=='P':
                if b<last[2]: STATS['descending']+=1
                else:
                    STATS['NOT-descending']+=1
                    if len(EX)<6: EX.append((S.show(d['src']),S.showG(d['G']),S.showS(d['s']),'prev',last[3],last[2],'now',d['x'],b))
            else: STATS['first-in-run']+=1
            return orig(d1,d2,c1,c2,path+(('EV','P',b,d['x']),))
        return orig(d1,d2,c1,c2,path)
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
            P.tag(d1,'d1'); P.tag(d2,'d2'); P.tag_ctx(c1,'c1'); P.tag_ctx(c2,'c2'); P.CALLS[0]=0
            try: P.rec(d1,d2,c1,c2,()); n+=1
            except (P.Budget,RecursionError,MemoryError): continue
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {n} runs; {dict(STATS)}",flush=True)
    print("\nFINAL",dict(STATS),flush=True)
    for ex in EX: print("VIOLATION",ex,flush=True)
if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
