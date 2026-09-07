"""Frames. A frame is one copy of an input tree: the two original derivations, and each copy of a
context piece made by an external pull. Internal pulls (of a stored premise) return to the frame
the premise was cut from. Along each path this probe checks, per frame, whether the material's
position in the frame's tree moves strictly later in pre-order (operator before operand, annotation
before body, body before operand) at every visit, and counts how often a frame is re-entered at a
position not later than where it was left."""
import sys, copy, collections, random
from importlib.machinery import SourceFileLoader
P=SourceFileLoader('P','/home/egret/gimmick/1/MPSS/position-probe.py').load_module()
R,S=P.R,P.S
KEYS=('e','o','p','F','a')
RANK={'e':0,'o':0,'a':0,'F':1,'p':2}
FRAME=[0]
def newframe(): FRAME[0]+=1; return FRAME[0]
def setframe(d,f):
    d['frame']=f
    for k in KEYS:
        if k in d: setframe(d[k],f)
# external pulls: extract from the context reduction; give the piece a fresh frame
_orig_extract=R.extract
def extract_f(c,x):
    d=_orig_extract(c,x)
    if d.get('frame') is None or d.get('ext'):   # a c-piece (never cut from a material) or refl
        d=copy.deepcopy(d); setframe(d,newframe())
    return d
_orig_pop=R.pop
def pop_f(c):
    c1,q=_orig_pop(c)
    if q.get('frame') is None: q=copy.deepcopy(q); setframe(q,newframe())
    return c1,q
_orig_weaken=R._weaken
def weaken_f(d,Gt,sx):
    r=_orig_weaken(d,Gt,sx); P.copy_pos(d,r); copyframe(d,r); return r
def copyframe(src,dst):
    if 'frame' in src: dst['frame']=src['frame']
    for k in KEYS:
        if k in src and k in dst: copyframe(src[k],dst[k])

def later(p,q):
    """is position q strictly later than p in pre-order?"""
    if p==q: return False
    n=min(len(p),len(q))
    for i in range(n):
        if p[i]!=q[i]: return RANK[q[i]]>RANK[p[i]]
    return len(q)>len(p)   # q is a descendant of p

STATS=collections.Counter(); EX=[]
def make_rec():
    orig=P.rec
    def rec(d1,d2,c1,c2,path):
        # path entries: (frame1,pos1,frame2,pos2)
        st=(d1.get('frame'),P.pos(d1)[1],d2.get('frame'),P.pos(d2)[1])
        if (d1['rule'],d2['rule']) not in P.LEAF:
            for side,(f,pos) in ((1,(st[0],st[1])),(2,(st[2],st[3]))):
                # last visit of this frame on this side along the path
                last=None
                for e in reversed(path):
                    ef,ep=(e[0],e[1]) if side==1 else (e[2],e[3])
                    if ef==f: last=ep; break
                if last is not None:
                    if later(last,pos): STATS[f'side{side}:later']+=1
                    elif last==pos: STATS[f'side{side}:same']+=1; EX.append(('same',side,S.show(d1['src']),S.showG(d1['G']),S.showS(d1['s']),pos))
                    else: STATS[f'side{side}:EARLIER']+=1; EX.append(('earlier',side,S.show(d1['src']),S.showG(d1['G']),S.showS(d1['s']),last,pos))
        return orig(d1,d2,c1,c2,path+(st,))
    return rec

def run(k,kc,maxruns,sel=None):
    cfgs=S.families()
    AP=SourceFileLoader('ap','/home/egret/gimmick/1/MPSS/anchor-probe.py').load_module(); cfgs+=AP.adversarial()
    R._weaken=weaken_f; R.refl_deriv=P.refl_pos; R.extract=extract_f; R.pop=pop_f
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    if sel: cfgs=[cfgs[i] for i in sel]
    # the wrapped rec passes an extended path; the original rec appends its own entries — so
    # replace the original's path use: we call orig with our path (it appends (pos,pos) tuples of
    # length 2 which our reader ignores by length check)
    orig=P.rec
    def rec(d1,d2,c1,c2,path):
        path=tuple(e for e in path if len(e)==4)
        st=(d1.get('frame'),P.pos(d1),d2.get('frame'),P.pos(d2))
        if (d1['rule'],d2['rule']) not in P.LEAF:
            for side,(f,pos) in ((1,(st[0],st[1])),(2,(st[2],st[3]))):
                last=None
                for e in reversed(path):
                    ef,ep=(e[0],e[1]) if side==1 else (e[2],e[3])
                    if ef==f: last=ep; break
                if last is not None:
                    if last[0]!=pos[0]:
                        STATS[f'side{side}:FRAME-BASE-MISMATCH']+=1
                        if len(EX)<6: EX.append(('mismatch',side,f,last,pos))
                    elif later(last[1],pos[1]): STATS[f'side{side}:later']+=1
                    elif last==pos:
                        STATS[f'side{side}:same']+=1
                        if len(EX)<6: EX.append(('same',side,S.show(d1['src']),S.showG(d1['G']),S.showS(d1['s']),pos))
                    else:
                        STATS[f'side{side}:EARLIER']+=1
                        if len(EX)<6: EX.append(('earlier',side,S.show(d1['src']),S.showG(d1['G']),S.showS(d1['s']),last,pos))
        return orig(d1,d2,c1,c2,path+(st,))
    P.rec=rec
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
            FRAME[0]=0; setframe(d1,newframe()); setframe(d2,newframe())
            P.CALLS[0]=0
            try: P.rec(d1,d2,c1,c2,()); n+=1
            except (P.Budget,RecursionError,MemoryError): continue
        print(f"[{i+1}/{len(cfgs)}] {S.show(t)} at {S.showG(G)};{S.showS(s)}: {n} runs; {dict(STATS)}",flush=True)
    print("\nFINAL",dict(STATS),flush=True)
    for ex in EX: print("EXAMPLE",ex,flush=True)

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    mr=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    sel=list(range(int(sys.argv[3]),int(sys.argv[4]))) if len(sys.argv)>4 else None
    kc=int(sys.argv[5]) if len(sys.argv)>5 else 1
    run(k,kc,mr,sel)
