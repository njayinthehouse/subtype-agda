import sys
sys.argv=[sys.argv[0]]
src=open('/home/egret/gimmick/1/MPSS/conj8-search.py').read().replace("main()\n","")
exec(compile(src,'c8','exec'))
I=L(TOP,B(0))
cands=[
 ((('z','s',F('y')),('y','s',I)), L(F('z'),B(0)), L(F('z'),F('y')), (('app',A(F('z'),F('z'))),)),
 ((('z','e',L(F('y'),B(0))),('y','s',I)), A(F('y'),F('z')), L(F('y'),F('y')), (('app',A(F('y'),F('y'))),)),
 ((('z','s',F('y')),('y','e',I)), L(F('z'),B(0)), L(F('z'),F('y')), (('app',A(F('z'),F('z'))),)),
]
for (G,u,t,Co) in cands:
    cu,ct=plugs(Co,u),plugs(Co,t)
    print(showG(G),"| Co[u] =",show(cu),"| Co[t] =",show(ct),"| hyp:",wf(G,u),wf(G,t),wsub(G,u,t,5),wf(G,cu),wf(G,ct))
    for (K,D,SZ) in [(2,4,14),(2,6,18),(3,8,24),(3,10,30)]:
        globals()['SIZE']=SZ; S._memo.clear(); _smemo.clear()
        Lc=closure(sreds,G,(),cu,K,D); Rc=closure(ereds,G,(),ct,K,D)
        print(f"  K={K} D={D} SIZE={SZ}: |ˢ|={len(Lc)} |ᵉ|={len(Rc)} join={bool(Lc&Rc)}",flush=True)
        if Lc&Rc: print("  join term:",show(min(Lc&Rc,key=tsize))); break
