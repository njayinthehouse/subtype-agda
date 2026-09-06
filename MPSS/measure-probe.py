"""Probe candidate termination measures for the diamond's recursion.

Runs diamond-recursion.join on the family configurations, records every parent->child
edge of the recursion with a feature vector of both derivations and both context
reductions, then reports, for each candidate measure, how many edges fail to
strictly decrease (and which cases they are). A candidate that never fails is a
well-founded measure candidate worth proving.
"""
import sys, collections
from importlib.machinery import SourceFileLoader
R = SourceFileLoader('dr','/home/egret/gimmick/1/MPSS/diamond-recursion.py').load_module()
S = R.S

def nodes(d):
    yield d
    for k in ('e','o','p','F','a'):
        if k in d: yield from nodes(d[k])

def pro_vars(d):
    return [n['x'] for n in nodes(d) if n['rule']=='Pro']

def nesting(d):
    best=0
    for k in ('e','o','p','F','a'):
        if k in d: best=max(best,nesting(d[k]))
    return best+(1 if d['rule']=='Pro' else 0)

def pieces(c):
    if c[0]=='Refl': return []
    if c[0]=='Ann': return pieces(c[1])+[c[6]]
    return pieces(c[1])+[c[4]]

# position of a variable in the ORIGINAL context: original names are non-'n'/'z' names
def pos_in(G0,x):
    names=[e[0] for e in reversed(G0)]   # bottom first
    return names.index(x) if x in names else None

EDGES=[]
_orig=[None]
def instrument():
    old=R.join
    def join(d1,d2,c1,c2,depth=0,parent=None):
        me=(d1,d2,c1,c2)
        if parent is not None: EDGES.append((parent,me,d1['rule']+'/'+d2['rule']))
        # replicate old join but with parent tracking: easiest is to monkeypatch recursion
        return old(d1,d2,c1,c2,depth)
    return join

# Instead of monkeypatching deeply, re-implement the traversal: wrap join to push a stack.
STACK=[]
orig_join=R.join
def join_wrapped(d1,d2,c1,c2,depth=0):
    me=(d1,d2,c1,c2)
    if STACK: EDGES.append((STACK[-1],me,d1['rule']+'/'+d2['rule']))
    STACK.append(me)
    try:
        return orig_join(d1,d2,c1,c2,depth)
    finally:
        STACK.pop()
R.join=join_wrapped
# orig_join calls R.join? No — it calls the module-global name `join` inside its own module namespace.
# So rebind the module global:
R.__dict__['join']=join_wrapped

def lookup(G,x):
    for (y,c,t) in G:
        if y==x: return (c,t)
    return None

def root(G,G0,x,seen=None):
    """position of the latest original variable x's ≡-chain depends on; -1 if none"""
    p=pos_in(G0,x)
    if p is not None: return p
    e=lookup(G,x)
    if e is None or e[0]!='e': return -1
    seen=seen or set()
    if x in seen: return -1
    seen=seen|{x}
    return max([root(G,G0,y,seen) for y in S.fv(e[1])]+[-1])

def level(G,G0,x,seen=None):
    if pos_in(G0,x) is not None: return 0
    e=lookup(G,x)
    if e is None or e[0]!='e': return 0
    seen=seen or set()
    if x in seen: return 0
    seen=seen|{x}
    return 1+max([level(G,G0,y,seen) for y in S.fv(e[1])]+[0])

def usize(G,x,seen=None):
    """size of the full ≡-unfolding of x"""
    e=lookup(G,x)
    if e is None or e[0]!='e': return 1
    seen=seen or set()
    if x in seen: return 1
    seen=seen|{x}
    def sz(t):
        c=t[0]
        if c=='f': return usize(G,t[1],seen)
        if c in 'bT': return 1
        return 1+sz(t[1])+sz(t[2])
    return 1+sz(e[1])

def pro_nodes(d):
    return [n for n in nodes(d) if n['rule']=='Pro']

def features(state,G0):
    d1,d2,c1,c2=state
    f={}
    f['root']=([root(n['G'],G0,n['x'])+1 for n in pro_nodes(d1)],[root(n['G'],G0,n['x'])+1 for n in pro_nodes(d2)])
    f['rootlevel']=([(root(n['G'],G0,n['x'])+1,level(n['G'],G0,n['x'])) for n in pro_nodes(d1)],
                    [(root(n['G'],G0,n['x'])+1,level(n['G'],G0,n['x'])) for n in pro_nodes(d2)])
    f['rootU']=([(root(n['G'],G0,n['x'])+1,usize(n['G'],n['x'])) for n in pro_nodes(d1)],
                [(root(n['G'],G0,n['x'])+1,usize(n['G'],n['x'])) for n in pro_nodes(d2)])
    f['U']=([usize(n['G'],n['x']) for n in pro_nodes(d1)],[usize(n['G'],n['x']) for n in pro_nodes(d2)])
    f['size']=(R.size(d1),R.size(d2))
    f['pro']=(R.pros(d1),R.pros(d2))
    f['nest']=(nesting(d1),nesting(d2))
    pv1=[pos_in(G0,x) for x in pro_vars(d1)]
    pv2=[pos_in(G0,x) for x in pro_vars(d2)]
    f['provars']=(pv1,pv2)
    f['cpro']=(sum(R.pros(p) for p in pieces(c1)),sum(R.pros(p) for p in pieces(c2)))
    return f

def ms_key(ws):
    # multiset of weights compared as sorted-descending tuple (Dershowitz-Manna on finite totals)
    return tuple(sorted(ws,reverse=True))

def candidates(f):
    c={}
    c['size-sum']=f['size'][0]+f['size'][1]
    c['pro-sum']=f['pro'][0]+f['pro'][1]
    c['pro-sum+size']=(f['pro'][0]+f['pro'][1], f['size'][0]+f['size'][1])
    c['nest-sum,size']=(f['nest'][0]+f['nest'][1], f['size'][0]+f['size'][1])
    c['maxpro,minpro,size']=(max(f['pro']),min(f['pro']),f['size'][0]+f['size'][1])
    # multiset of original positions (internal Pro -> weight 0), then size
    w=[ (p if p is not None else -1)+1 for p in f['provars'][0]+f['provars'][1] ]
    c['ms-pos,size']=(ms_key(w), f['size'][0]+f['size'][1])
    # pro-sum including pieces held in c's
    c['pro-sum+cpro,size']=(f['pro'][0]+f['pro'][1]+f['cpro'][0]+f['cpro'][1], f['size'][0]+f['size'][1])
    c['ms-root,size']=(ms_key(f['root'][0]+f['root'][1]), f['size'][0]+f['size'][1])
    c['ms-rootlevel,size']=(ms_key(f['rootlevel'][0]+f['rootlevel'][1]), f['size'][0]+f['size'][1])
    c['ms-rootU,size']=(ms_key(f['rootU'][0]+f['rootU'][1]), f['size'][0]+f['size'][1])
    c['ms-U,size']=(ms_key(f['U'][0]+f['U'][1]), f['size'][0]+f['size'][1])
    return c

def run(k,kc,maxruns):
    cfgs=S.families()
    cfgs=[c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]
    R.MAXRUNS[0]=maxruns; R.BUDGET[0]=200000
    viol=collections.defaultdict(lambda: collections.Counter())
    global SHOW; SHOW=collections.defaultdict(lambda: collections.Counter())
    total=0
    for i,(G,s,t) in enumerate(cfgs):
        EDGES.clear()
        R._dmemo.clear()
        R.run(G,s,t,k,kc,label=f"[{i+1}/{len(cfgs)}]")
        for (par,ch,case) in EDGES:
            if par[0] is ch[1] and par[1] is ch[0]: continue      # the swap edge, not a real call
            total+=1
            fp=candidates(features(par,G)); fc=candidates(features(ch,G))
            for name in fp:
                if not (fc[name] < fp[name]):
                    viol[name][case]+=1
                    if SHOW[name][case]<2:
                        SHOW[name][case]+=1
                        print(f"  VIOL {name} {case}: parent {fp[name]} child {fc[name]}")
                        print(f"       parent subj {S.show(par[0]['src'])} at {S.showG(par[0]['G'])};{S.showS(par[0]['s'])}")
                        print(f"       child  subj {S.show(ch[0]['src'])} at {S.showG(ch[0]['G'])};{S.showS(ch[0]['s'])}")
                        print(f"       parent provars {features(par,G)['provars']} sizes {features(par,G)['size']}")
                        print(f"       child  provars {features(ch,G)['provars']} sizes {features(ch,G)['size']}")
    print(f"\n{total} edges")
    for name in sorted(viol.keys()|set(candidates(features(EDGES[0][0],G)).keys())):
        v=viol.get(name,{})
        print(f"  {name:28s} violations: {sum(v.values()):6d}  {dict(v)}")

if __name__=='__main__':
    k=int(sys.argv[1]) if len(sys.argv)>1 else 1
    run(k,1,int(sys.argv[2]) if len(sys.argv)>2 else 20000)
