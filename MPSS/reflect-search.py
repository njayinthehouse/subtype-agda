"""Does u ⊲ t (machine chain, no side conditions) between well-formed u, t imply u ≤*wf t
(promotions between well-formed terms)? Search on small terms."""
import sys
argv=sys.argv[1:]; sys.argv=[sys.argv[0]]
src=open('/home/egret/gimmick/1/MPSS/conj8-search.py').read().replace("main()\n","")
exec(compile(src,'c8','exec'))
maxsize=int(argv[0])
names=['y','z']
anns=[TOP, L(TOP,TOP), L(TOP,B(0)), L(TOP,L(TOP,TOP)), L(L(TOP,TOP),B(0)), L(TOP,L(TOP,B(1)))]
ctxs=[()]
for a in anns:
    for c in ('s','e'): ctxs.append((('y',c,a),))
for a in anns:
    for c in ('s','e'):
        for b in [TOP,F('y'),L(F('y'),B(0)),L(TOP,F('y')),A(F('y'),TOP)]:
            for c2 in ('s','e'):
                G=(('z',c2,b),('y',c,a))
                if S.ctx_prevalid(G): ctxs.append(G)
terms=gen_terms(names,maxsize)
stats=collections.Counter(); ex=[]
for G in ctxs:
    S._memo.clear(); _smemo.clear(); _wfmemo.clear(); gc.collect()
    dn=S.dom(G); ts=[t for t in terms if S.fv(t)<=dn]
    wfs=[t for t in ts if wf(G,t)]
    for u in wfs:
        for t in wfs:
            if u==t: continue
            if not machine(G,(),u,t,2,5): continue
            stats['machine']+=1
            if wsub(G,u,t,6): stats['also_wsub']+=1
            else:
                # escalate the well-subtyping search depth
                globals()['WD']=7
                ok=wsub(G,u,t,8); globals()['WD']=3
                if ok: stats['wsub_escalated']+=1
                else:
                    stats['GAP']+=1; ex.append((G,u,t))
                    print("GAP:",showG(G),"| u =",show(u),"| t =",show(t),flush=True)
    print(f"ctx {showG(G)}: {dict(stats)}",flush=True)
print(dict(stats))
