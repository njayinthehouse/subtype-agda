"""Search for a counterexample to MPSS Lemma 2 (the diamond) with a cap on promotion depth.

diamond-search.py enumerates all one-step reducts and so cannot reach self-application,
where ⟶≡ is not finitely branching (MPSS/InfiniteBranching). This script bounds the
*nesting depth of Me-Pro* in every derivation it enumerates: reducts(G,s,t,k) is the set
of reducts of t at G;s whose derivations nest Me-Pro at most k deep. Every such set is
finite. Every one-step reduct lies in some reducts(...,k), so the search is complete
relative to the caps: a pair of reducts at cap k that has no join at cap K is a candidate
counterexample, to be re-examined at a larger K, and a pair with a join is settled.

The rules are implemented as printed (MPSS/Reduction, MPSS/CtxReduction), including
Me-Bet's unbound body premise; cofinite premises are instantiated at one fresh name.

Usage:
    python3 diamond-search-capped.py --family omega --k 2 --K 5
    python3 diamond-search-capped.py --random 200 --k 1 --K 4
"""
import sys, itertools, random, argparse
sys.setrecursionlimit(100000)

TOP = ('T',)

def openRec(k,u,t):
    c=t[0]
    if c=='b': return u if t[1]==k else t
    if c in 'fT': return t
    if c=='l': return ('l',openRec(k,u,t[1]),openRec(k+1,u,t[2]))
    return ('a',openRec(k,u,t[1]),openRec(k,u,t[2]))

def closeRec(k,x,t):
    c=t[0]
    if c=='b': return t
    if c=='f': return ('b',k) if t[1]==x else t
    if c=='T': return t
    if c=='l': return ('l',closeRec(k,x,t[1]),closeRec(k+1,x,t[2]))
    return ('a',closeRec(k,x,t[1]),closeRec(k,x,t[2]))

def fv(t):
    c=t[0]
    if c=='f': return frozenset([t[1]])
    if c in 'bT': return frozenset()
    return fv(t[1])|fv(t[2])

def lc(t,k=0):
    c=t[0]
    if c=='b': return t[1]<k
    if c in 'fT': return True
    if c=='l': return lc(t[1],k) and lc(t[2],k+1)
    return lc(t[1],k) and lc(t[2],k)

def dom(G): return frozenset(e[0] for e in G)

def ctx_prevalid(G):
    if not G: return True
    x,c,t = G[0]; tail = G[1:]
    return ctx_prevalid(tail) and x not in dom(tail) and lc(t) and fv(t)<=dom(tail)

def prevalid(G,s):
    if not ctx_prevalid(G): return False
    return all(lc(a) and fv(a)<=dom(G) for a in s)

FRESH = 'z%d'
def fresh(G,*ts):
    used=set(dom(G))
    for t in ts:
        if isinstance(t,tuple) and t and isinstance(t[0],str) and t[0] in 'bfTla': used|=fv(t)
        else:
            for u in t: used|=fv(u)
    i=0
    while FRESH%i in used: i+=1
    return FRESH%i

def lookup_eqv(G,x):
    for (y,c,t) in G:
        if y==x: return t if c=='e' else None
    return None

def show(t):
    c=t[0]
    if c=='b': return str(t[1])
    if c=='f': return t[1]
    if c=='T': return '⊤'
    if c=='l': return '(λ%s.%s)'%(show(t[1]),show(t[2]))
    return '(%s %s)'%(show(t[1]),show(t[2]))

def showG(G): return ', '.join('%s%s%s'%(x,'≡' if c=='e' else '≤',show(t)) for (x,c,t) in reversed(G)) or 'ε'
def showS(s): return '['+', '.join(show(a) for a in s)+']'

# ---- reducts with a cap on Me-Pro nesting ----
_memo={}
_elems=[0]
MEMO_ELEMS=1500000
def reducts(G,s,t,k):
    """all u with G;s ⊢ t ⟶≡ u by a derivation nesting Me-Pro at most k deep"""
    key=(G,s,t,k)
    if key in _memo: return _memo[key]
    out=set()
    pv = prevalid(G,s)
    c=t[0]
    if c=='f':
        if pv: out.add(t)                                          # Me-Var
        a=lookup_eqv(G,t[1])
        if pv and a is not None and k>0: out |= reducts(G,s,a,k-1)   # Me-Pro
    elif c=='T':
        if pv: out.add(TOP)                                        # Me-Top
    elif c=='a':
        u,v=t[1],t[2]
        if u==TOP and pv: out.add(TOP)                             # Me-TAp
        for up in reducts(G,(v,)+s,u,k):                           # Me-App
            for vp in reducts(G,(),v,k):
                out.add(('a',up,vp))
        if u[0]=='l':                                              # Me-Bet
            body=u[2]
            x=fresh(G,t,s)
            for r in reducts(G,s,openRec(0,('f',x),body),k):
                up2=closeRec(0,x,r)
                for vp in reducts(G,(),v,k):
                    out.add(openRec(0,vp,up2))
    elif c=='l':
        w,b=t[1],t[2]
        if not s:                                                  # Me-Fun
            x=fresh(G,t)
            for wp in reducts(G,(),w,k):
                for r in reducts(((x,'s',w),)+G,(),openRec(0,('f',x),b),k):
                    out.add(('l',wp,closeRec(0,x,r)))
        else:                                                      # Me-FOp
            al,rest=s[0],s[1:]
            x=fresh(G,t,s)
            for wp in reducts(G,(),w,k):
                for r in reducts(((x,'e',al),)+G,rest,openRec(0,('f',x),b),k):
                    out.add(('l',wp,closeRec(0,x,r)))
    r=frozenset(out)
    if _elems[0]>MEMO_ELEMS: _memo.clear(); _elems[0]=0
    _memo[key]=r; _elems[0]+=len(r)+1; return r

def ctx_reducts(G,s,k):
    out={(G,s)}                                                    # Ct-Refl
    if G:
        x,c,t=G[0]; tail=G[1:]
        for (Gp,sp) in ctx_reducts(tail,s,k):
            for tp in reducts(tail,(),t,k):
                out.add((((x,c,tp),)+Gp,sp))                       # Ct-Ann
    if s:
        al,rest=s[0],s[1:]
        for (Gp,sp) in ctx_reducts(G,rest,k):
            for ap in reducts(G,(),al,k):
                out.add((Gp,(ap,)+sp))                             # Ct-Stk
    return out

# ---- the check ----
import time
_t0=[time.time()]
def progress(msg):
    print(f"[{time.strftime('%H:%M:%S')} +{time.time()-_t0[0]:.0f}s] {msg}",flush=True)

def check(G,s,t,k,kc,K,label=''):
    """returns list of (t1,t2,c1,c2) with no join at cap K; prints progress"""
    R=sorted(reducts(G,s,t,k),key=repr)
    crs=sorted(ctx_reducts(G,s,kc),key=repr)
    total=len(R)*(len(R)+1)//2*len(crs)*len(crs)
    progress(f"{label} {show(t)} at {showG(G)}; {showS(s)}: {len(R)} reducts (k={k}), {len(crs)} ctx-reducts (kc={kc}), {total} checks at K={K}")
    bad=[]; n=0; last=time.time()
    for i,t1 in enumerate(R):
        for t2 in R[i:]:
            for c1 in crs:
                A1=reducts(c1[0],c1[1],t1,K)
                for c2 in crs:
                    n+=1
                    if not (A1 & reducts(c2[0],c2[1],t2,K)):
                        bad.append((t1,t2,c1,c2))
                    if time.time()-last>20:
                        last=time.time(); progress(f"    {100*n/total:5.1f}% of this configuration, {len(bad)} unjoined so far")
    progress(f"    done: {len(bad)} unjoined at K={K}")
    return bad,R,crs

def escalate(G,s,t,bad,K,Kmax):
    still=bad
    while still and K<Kmax:
        K+=1
        nxt=[]
        for j,(t1,t2,c1,c2) in enumerate(still):
            if not (reducts(c1[0],c1[1],t1,K) & reducts(c2[0],c2[1],t2,K)):
                nxt.append((t1,t2,c1,c2))
        progress(f"    K={K}: {len(nxt)} of {len(still)} still unjoined")
        still=nxt
    return still

# ---- families ----
def B(i): return ('b',i)
def F(x): return ('f',x)
def L(w,b): return ('l',w,b)
def A(u,v): return ('a',u,v)
omega   = L(TOP,A(B(0),B(0)))                       # λ⊤. 0 0
def omega_w(w): return L(TOP,A(A(B(0),B(0)),F(w)))  # λ⊤. (0 0) w
def omega_w2(w): return L(TOP,A(B(0),A(B(0),F(w)))) # λ⊤. 0 (0 w)
delta_in = L(TOP,A(L(TOP,B(0)),A(B(1),B(1))))       # λ⊤. (λ⊤.0)(1 1)

def families():
    x,y,w='x','y','w'
    cfgs=[]
    # Ω at the empty context
    cfgs.append(((),(),A(omega,omega)))
    # x ≡ ω, subject x x, and with x on the stack
    G=((x,'e',omega),)
    cfgs += [(G,(),A(F(x),F(x))), (G,(F(x),),F(x)), (G,(F(x),),omega), (G,(),A(F(x),omega))]
    # w ≡ ⊤⊤ : a promotable annotation with a redex; x ≡ ω_w mentions it
    for ann in [A(TOP,TOP), A(L(TOP,B(0)),TOP)]:
        G=((x,'e',omega_w(w)),(w,'e',ann))
        cfgs += [(G,(),A(F(x),F(x))), (G,(),A(A(F(x),F(x)),F(w))), (G,(F(x),),F(x)),
                 (G,(F(w),),A(F(x),F(x))), (G,(F(x),F(w)),F(x))]
        G=((x,'e',omega_w2(w)),(w,'e',ann))
        cfgs += [(G,(),A(F(x),F(x))), (G,(F(x),),F(x))]
        # y ≡ x, a chain
        G=((y,'e',F(x)),(x,'e',omega_w(w)),(w,'e',ann))
        cfgs += [(G,(),A(F(y),F(y))), (G,(),A(F(y),F(x))), (G,(F(y),),F(x)), (G,(F(x),),F(y))]
        # an annotation with an internal redex whose operand is a self-application
        G=((x,'e',delta_in),(w,'e',ann))
        cfgs += [(G,(),A(F(x),F(x))), (G,(),A(F(x),F(w))), (G,(F(w),),F(x))]
    # subtype-bound variable feeding a self-application
    G=((x,'e',omega),(w,'s',TOP))
    cfgs += [(G,(),A(F(x),F(w))), (G,(F(w),),F(x))]
    # compounding unfoldings: a redex annotation whose parameter is used in a self-application,
    # with an operand whose unfolding is large
    big = A(A(A(TOP,TOP),A(TOP,TOP)),A(A(TOP,TOP),A(TOP,TOP)))
    dbl = A(L(TOP,A(L(TOP,B(0)),A(B(0),B(0)))),F(w))        # (λ⊤.(λ⊤.0)(0 0)) w
    G=((x,'e',dbl),(w,'e',big))
    cfgs += [(G,(),F(x)), (G,(),A(F(x),F(x))), (G,(F(x),),F(x)), (G,(F(w),),F(x)), (G,(),A(F(x),F(w)))]
    # a redex operand whose piece binds a parameter to x: (λ⊤.0)((λ⊤.0) x)
    G=((x,'e',A(TOP,TOP)),)
    cfgs += [(G,(),A(L(TOP,B(0)),A(L(TOP,B(0)),F(x)))), (G,(),A(L(TOP,A(B(0),B(0))),A(L(TOP,B(0)),F(x))))]
    G=((x,'e',omega),)
    cfgs += [(G,(),A(L(TOP,B(0)),A(L(TOP,B(0)),F(x)))), (G,(),A(L(TOP,A(B(0),B(0))),A(L(TOP,B(0)),F(x))))]
    # a stack entry whose piece compounds x: (λ⊤.0) ((λ⊤.(λ⊤.0)(0 0)) x) with a large x
    dblx = A(L(TOP,A(L(TOP,B(0)),A(B(0),B(0)))),F(x))
    G=((x,'e',big),)
    cfgs += [(G,(),A(L(TOP,B(0)),dblx)), (G,(),A(L(TOP,A(B(0),B(0))),dblx)), (G,(dblx,),L(TOP,B(0))), (G,(dblx,),L(TOP,A(B(0),B(0))))]
    G=((x,'e',omega),)
    cfgs += [(G,(),A(L(TOP,B(0)),dblx)), (G,(dblx,),L(TOP,A(B(0),B(0))))]
    return cfgs

def rand_term(size,names,rng,k=0):
    if size<=1:
        opts=[TOP]+[F(n) for n in names]+[B(i) for i in range(k)]
        return rng.choice(opts)
    if rng.random()<0.45:
        return L(rand_term(rng.randint(1,max(1,size//3)),names,rng,k), rand_term(size-1,names,rng,k+1))
    a=rng.randint(1,size-1)
    return A(rand_term(a,names,rng,k), rand_term(size-a,names,rng,k))

def rand_cfg(rng):
    names=[]
    G=()
    for i in range(rng.randint(1,3)):
        n='v%d'%i
        ann=rand_term(rng.randint(1,6),names,rng)
        kind='e' if rng.random()<0.8 else 's'
        G=((n,kind,ann),)+G
        names.append(n)
    s=tuple(rand_term(rng.randint(1,3),names,rng) for _ in range(rng.randint(0,2)))
    t=rand_term(rng.randint(2,7),names,rng)
    return G,s,t

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--family',default='omega')
    ap.add_argument('--random',type=int,default=0)
    ap.add_argument('--seed',type=int,default=1)
    ap.add_argument('--k',type=int,default=1)     # cap for the two edges
    ap.add_argument('--kc',type=int,default=1)    # cap for context-reduction pieces
    ap.add_argument('--K',type=int,default=3)     # cap for the joins
    ap.add_argument('--Kmax',type=int,default=5)  # escalation limit
    ap.add_argument('--memo',type=int,default=MEMO_ELEMS)
    a=ap.parse_args()
    MEMO_ELEMS=a.memo
    rng=random.Random(a.seed)
    cfgs = families() if a.random==0 else [rand_cfg(rng) for _ in range(a.random)]
    cfgs=[c for c in cfgs if prevalid(c[0],c[1]) and lc(c[2]) and fv(c[2])<=dom(c[0])]
    progress(f"{len(cfgs)} configurations, k={a.k} kc={a.kc} K={a.K} Kmax={a.Kmax}")
    total_bad=0; done=0; report=[]
    for i,(G,s,t) in enumerate(cfgs):
        _memo.clear(); _elems[0]=0
        try:
            bad,R,crs=check(G,s,t,a.k,a.kc,a.K,label=f"[{i+1}/{len(cfgs)} = {100*i/len(cfgs):.0f}%]")
        except RecursionError:
            progress("  recursion limit; skipped"); continue
        done+=1
        if bad:
            still=escalate(G,s,t,bad,a.K,a.Kmax)
            if still:
                total_bad+=len(still)
                progress(f"  UNJOINED at Kmax={a.Kmax}: {len(still)} pairs")
                for (t1,t2,c1,c2) in still[:3]:
                    line=f"    t0={show(t)} at {showG(G)};{showS(s)}\n      t1={show(t1)}\n      t2={show(t2)}\n      c1={showG(c1[0])};{showS(c1[1])}\n      c2={showG(c2[0])};{showS(c2[1])}"
                    print(line,flush=True); report.append(line)
    progress(f"DONE: {done} configurations, {total_bad} pairs unjoined at Kmax={a.Kmax}")
    if report:
        print("SUMMARY OF UNJOINED PAIRS"); print("\n".join(report))
