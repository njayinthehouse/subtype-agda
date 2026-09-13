import sys
sys.argv=[sys.argv[0]]
src=open('/home/egret/gimmick/1/MPSS/conj8-search.py').read().replace("main()\n","")
exec(compile(src,'c8','exec'))
G=(('z','e',A(F('y'),TOP)),('y','e',L(TOP,L(TOP,B(1)))))
y,z=F('y'),F('z')
us=[A(y,A(y,y)), A(y,L(TOP,y)), L(TOP,A(y,y)), L(TOP,L(TOP,y))]
ts=[A(y,A(y,z)), A(y,L(TOP,z)), L(TOP,A(y,z)), L(TOP,L(TOP,z))]
globals()['SIZE']=30; globals()['WD']=10
ok=0
for u in us:
    for t in ts:
        S._memo.clear(); _smemo.clear(); _wfmemo.clear()
        r=wsub(G,u,t,10); ok+=r
        print(show(u),"≤*wf",show(t),":",r,flush=True)
print("resolved",ok,"of 16")
