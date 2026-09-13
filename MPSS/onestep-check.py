"""Goal-directed check of Γ;s ⊢ t ⟶ᵉ m (one original step), with a bound on promotion nesting."""
import sys, json
sys.setrecursionlimit(100000)
from importlib.machinery import SourceFileLoader
S=SourceFileLoader('dsc','/home/egret/gimmick/1/MPSS/diamond-search-capped.py').load_module()
TOP=S.TOP; openRec=S.openRec; closeRec=S.closeRec
def tup(x):
    if isinstance(x,list): return tuple(tup(y) for y in x)
    return x
def onestep(G,s,t,m,depth,cap=3,memo=None):
    if memo is None: memo={}
    key=(G,s,t,m,depth)
    if key in memo: return memo[key]
    memo[key]=False
    res=False
    c=t[0]
    if not S.prevalid(G,s): res=False
    elif c=='f':
        if m==t: res=True
        else:
            a=S.lookup_eqv(G,t[1])
            if a is not None and depth>0: res=onestep(G,s,a,m,depth-1,cap,memo)
    elif c=='T': res=(m==TOP)
    elif c=='a':
        u,v=t[1],t[2]
        if u==TOP and m==TOP: res=True
        if not res and m[0]=='a' and onestep(G,(v,)+s,u,m[1],depth,cap,memo) and onestep(G,(),v,m[2],depth,cap,memo): res=True
        if not res and u[0]=='l':
            x=S.fresh(G,t,s); body=openRec(0,('f',x),u[2])
            for vp in S.reducts(G,(),v,cap):
                for r in S.reducts(G,s,body,cap):
                    if openRec(0,vp,closeRec(0,x,r))==m: res=True; break
                if res: break
    elif c=='l':
        w,b=t[1],t[2]
        if m[0]=='l':
            if not s:
                x=S.fresh(G,t)
                res=onestep(G,(),w,m[1],depth,cap,memo) and onestep(((x,'s',w),)+G,(),openRec(0,('f',x),b),openRec(0,('f',x),m[2]),depth,cap,memo)
            else:
                al,rest=s[0],s[1:]; x=S.fresh(G,t,s)
                res=onestep(G,(),w,m[1],depth,cap,memo) and onestep(((x,'e',al),)+G,rest,openRec(0,('f',x),b),openRec(0,('f',x),m[2]),depth,cap,memo)
    memo[key]=res
    return res
if __name__=='__main__':
    d=json.load(open(sys.argv[1]))
    for ex in d['ex'].get('nocompress_raw',[]):
        G=tup(ex['G']); s=tup(ex['s']); t2=tup(ex['t2']); m=tup(ex['m'])
        print("config:",S.showG(G),S.showS(s)); print("t2 =",S.show(t2)); print("m  =",S.show(m))
        print("chain terms:",[S.show(tup(x)) for x in ex['terms']])
        for depth in (4,6,8,12):
            r=onestep(G,s,t2,m,depth,cap=3)
            print(f"  one-step derivable at promotion depth {depth}, β-cap 3: {r}",flush=True)
            if r: break
