"""Statistics of pull sequences along paths: side switches, external pulls, repeated variables."""
import sys, copy, collections, random
from importlib.machinery import SourceFileLoader
P=SourceFileLoader('P','/home/egret/gimmick/1/MPSS/position-probe.py').load_module()
R,S=P.R,P.S
STATS=collections.Counter(); MAXES=collections.Counter(); WORST={}
def bt(G,x):
    names=[e[0] for e in reversed(G)]
    return names.index(x) if x in names else -1
def analyse(pulls,d1,d2):
    if not pulls: return
    sides=[p[0] for p in pulls]
    sw=sum(1 for a,b in zip(sides,sides[1:]) if a!=b)
    ext=[p for p in pulls if p[1]=='ext']
    MAXES['switches']=max(MAXES['switches'],sw)
    MAXES['pulls']=max(MAXES['pulls'],len(pulls))
    MAXES['ext']=max(MAXES['ext'],len(ext))
    c=collections.Counter(p[2] for p in ext)
    MAXES['ext-same-var']=max(MAXES['ext-same-var'],max(c.values()) if c else 0)
    ci=collections.Counter(p[2] for p in pulls if p[1]=='int')
    MAXES['int-same-param']=max(MAXES['int-same-param'],max(ci.values()) if ci else 0)
    # runs: consecutive pulls by one side
    run=1; mx=1
    for a,b in zip(sides,sides[1:]):
        run=run+1 if a==b else 1; mx=max(mx,run)
    MAXES['max-run']=max(MAXES['max-run'],mx)
    # ext bt sequence monotone? count violations of strict decrease between consecutive ext pulls
    viol=sum(1 for a,b in zip(ext,ext[1:]) if b[3]>=a[3])
    STATS['paths']+=1
    if viol: STATS['ext-bt-nondecreasing-paths']+=1
    if sw>=4 and 'sw4' not in WORST: WORST['sw4']=(pulls,S.show(d1['src']),S.showG(d1['G']),S.show(d1['tgt']),S.show(d2['tgt']))
    if sw>MAXES.get('_swrec',-1): MAXES['_swrec']=sw; WORST['maxsw']=(pulls,S.show(d1['src']),S.showG(d1['G']),S.show(d1['tgt']),S.show(d2['tgt']))

def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    AP=SourceFileLoader('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    R._weaken=P._weaken_pos; R.refl_deriv=P.refl_pos
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    orig=P.rec; CUR=[None]
    def rec(d1,d2,c1,c2,path):
        # path: list of pull records so far (we ignore position-probe's own entries by filtering length)
        pulls=tuple(e for e in path if len(e)==5)
        r1,r2=d1['rule'],d2['rule']
        G0=CUR[0]
        if (r1,r2) in P.LEAF or r1=='Pro' and r2=='Pro' or (r1,r2) in (('App','App'),('App','Bet'),('Bet','App'),('Bet','Bet'),('Fun','Fun'),('FOp','FOp')):
            if (r1,r2) in P.LEAF: analyse(pulls,d1,d2)
            return orig(d1,d2,c1,c2,path)
        if r1=='Var' and r2=='Pro':
            x=d1['x']; kind='ext' if x in S.dom(G0) else 'int'
            return orig(d1,d2,c1,c2,path+((1,kind,x,bt(d1['G'],x),len(pulls)),))
        if r1=='Pro' and r2=='Var':
            x=d2['x']; kind='ext' if x in S.dom(G0) else 'int'
            return orig(d1,d2,c1,c2,path+((2,kind,x,bt(d2['G'],x),len(pulls)),))
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
            P.tag(d1,'d1'); P.tag(d2,'d2'); P.tag_ctx(c1,'c1'); P.tag_ctx(c2,'c2'); P.CALLS[0]=0
            try: P.rec(d1,d2,c1,c2,()); n+=1
            except (P.Budget,RecursionError,MemoryError): continue
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {n} runs; maxes {dict((k,v) for k,v in MAXES.items() if not k.startswith('_'))}; {dict(STATS)}",flush=True)
    print("\nFINAL",dict((k,v) for k,v in MAXES.items() if not k.startswith('_')),dict(STATS),flush=True)
    for key,w in WORST.items():
        pulls,src,G,t1,t2=w
        print("WORST",key,"t0 =",src,"at",G,"t1 =",t1,"t2 =",t2,flush=True)
        print("   pulls:",[(p[0],p[1],p[2],p[3]) for p in pulls],flush=True)

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
