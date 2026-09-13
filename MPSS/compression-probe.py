"""Compression check for the reassembly gap.

For two original one-step reductions d1, d2 of t0 at a fixed configuration: peel d1 into a chain
of variant steps, join it link by link against d2 with an executable version of the mixed
diamond's join construction (MixedDiamond), and ask whether the chain of original steps this
produces from t2 is a single original step (membership of its end in the capped reduct set of
t2). Reports, per configuration, how many strips compress at cap k and the smallest that does
not compress at the largest cap tried."""
import sys, random, gc, collections, copy
sys.setrecursionlimit(200000)
sys.argv=[sys.argv[0]]+sys.argv[1:]
src=open('/home/egret/gimmick/1/MPSS/mixed-measure-probe.py').read().replace("main()\n","")
exec(compile(src,'mmp','exec'))
S=R.S
A,L,F,B,TOP=S.A,S.L,S.F,S.B,S.TOP
D=R.D; openRec=S.openRec; closeRec=S.closeRec; subst_t=R.subst_t

# ------------------------------------------------------------ derivation utilities
def subst_tree(d,x,vsrc,vtgt,drop_binding=False):
    """substitute x := vsrc in sources/contexts/stacks and x := vtgt in targets, throughout the tree.
    If drop_binding, remove the context entry for x."""
    e=dict(d)
    e['src']=subst_t(d['src'],x,vsrc); e['tgt']=subst_t(d['tgt'],x,vtgt)
    G=tuple((n,k,subst_t(t,x,vsrc)) for (n,k,t) in d['G'] if not (drop_binding and n==x))
    e['G']=G; e['s']=tuple(subst_t(a,x,vsrc) for a in d['s'])
    if 'alpha' in d: e['alpha']=subst_t(d['alpha'],x,vsrc)
    if 'ann' in d: e['ann']=subst_t(d['ann'],x,vsrc)
    for key in ('e','o','p','F','a'):
        if key in d: e[key]=subst_tree(d[key],x,vsrc,vtgt,drop_binding)
    return e

def push_any(d,s_extra,variant):
    return vweaken(d,d['G'],s_extra) if variant else R.weaken(d,d['G'],s_extra)

def subst_deriv(d,x,sv,variant=False,drop_binding=False):
    """⟶-subst: sv : G;[] ⊢ v ⟶ v′ substituted for x (unbound, or ≡-bound to v when drop_binding)."""
    v,vt=sv['src'],sv['tgt']
    r=d['rule']
    if r=='Var' and d['x']==x:
        # x ⟶ x becomes v ⟶ v′ pushed under the current stack (with x substituted away)
        s=tuple(subst_t(a,x,v) for a in d['s'])
        G=tuple((n,k,subst_t(t,x,v)) for (n,k,t) in d['G'] if not (drop_binding and n==x))
        out=push_any(dict(sv,G=G),s,variant)
        return out
    if r=='Pro' and d['x']==x:
        # x ≡ v: the premise d.e : v ⟶ w becomes v ⟶ w[x:=v′]
        return subst_deriv(d['e'],x,sv,variant,drop_binding)
    e=subst_tree({k:val for k,val in d.items() if k not in ('e','o','p','F','a')},x,v,vt,drop_binding)
    for key in ('e','o','p','F','a'):
        if key in d: e[key]=subst_deriv(d[key],x,sv,variant,drop_binding)
    return e

def drop_ctx_binding(d,x):
    e=dict(d); e['G']=tuple(en for en in d['G'] if en[0]!=x)
    for key in ('e','o','p','F','a'):
        if key in d: e[key]=drop_ctx_binding(d[key],x)
    return e

def refl(G,s,t): return R.refl_deriv(G,s,t)

def rename_to(d,x_from,x_to,other):
    if x_from==x_to: return d
    if x_to in R.names_d(d): d=R.rename_d(d,x_to,R.fresh_name(R.names_d(d)|R.names_d(other)))
    return R.rename_d(d,x_from,x_to)

# ------------------------------------------------------------ the mixed join
def cr_tgt(c): return R.cr_tgt(c)

def join(v,d,c1,c2):
    """(t3, J1 : tgt v ⟶ t3 at tgt c1 [original], J2 : tgt d ⟶ t3 at tgt c2 [original])"""
    G1,s1=cr_tgt(c1); G2,s2=cr_tgt(c2)
    r1,r2=v['rule'],d['rule']
    if r1=='Var' and r2=='Var':
        t3=v['tgt']; return t3, D('Var',t3,t3,G1,s1,x=v['x']), D('Var',t3,t3,G2,s2,x=v['x'])
    if r1=='Top' and r2=='Top':
        return TOP, D('Top',TOP,TOP,G1,s1), D('Top',TOP,TOP,G2,s2)
    if r1=='TAp' and r2=='TAp':
        return TOP, D('Top',TOP,TOP,G1,s1), D('Top',TOP,TOP,G2,s2)
    if r1=='TAp' and r2=='App':
        return TOP, D('Top',TOP,TOP,G1,s1), D('TAp',d['tgt'],TOP,G2,s2)
    if r1=='App' and r2=='TAp':
        return TOP, D('TAp',v['tgt'],TOP,G1,s1), D('Top',TOP,TOP,G2,s2)
    if r1=='Pro' and r2=='Pro':
        return join(vweaken(v['e'],v['G'],v['s']),d['e'],c1,c2)
    if r1=='Var' and r2=='Pro':
        x=v['x']; piece=vweaken(R.extract(c1,x),v['G'],v['s'])
        t3,J1p,J2=join(piece,d['e'],c1,c2)
        ap=R.lookup_eqv(G1,x)
        return t3, D('Pro',('f',x),t3,G1,s1,x=x,alpha=ap,e=J1p), J2
    if r1=='Pro' and r2=='Var':
        x=v['x']; piece=R.weaken(R.extract(c2,x),d['G'],())
        t3,J1p,J2p=join(v['e'],piece,R.empty(c1),R.empty(c2))
        ap=R.lookup_eqv(G2,x)
        J1=R.weaken(J1p,G1,s1); J2=D('Pro',('f',x),t3,G2,s2,x=x,alpha=ap,e=R.weaken(J2p,G2,s2))
        return t3,J1,J2
    if r1=='App' and r2=='App':
        u3,J1o,J2o=join(v['o'],d['o'],R.stk(c1,v['p']),R.stk(c2,d['p']))
        v3,J1p,J2p=join(v['p'],d['p'],R.empty(c1),R.empty(c2))
        t3=('a',u3,v3)
        return t3, D('App',v['tgt'],t3,G1,s1,o=J1o,p=J1p), D('App',d['tgt'],t3,G2,s2,o=J2o,p=J2p)
    if r1=='Fun' and r2=='Fun':
        t3a,J1a,J2a=join(v['a'],d['a'],R.empty(c1),R.empty(c2))
        x=v['x']; Fd=rename_to(d['F'],d['x'],x,v['F'])
        t=v['src'][1]
        w3,J1b,J2b=join(v['F'],Fd,R.ann(c1,x,'s',t,v['a']),R.ann(c2,x,'s',t,d['a']))
        b3=closeRec(0,x,w3); t3=('l',t3a,b3)
        return t3, D('Fun',v['tgt'],t3,G1,s1,x=x,a=J1a,F=J1b), D('Fun',d['tgt'],t3,G2,s2,x=x,a=J2a,F=J2b)
    if r1=='FOp' and r2=='FOp':
        t3a,J1a,J2a=join(v['a'],d['a'],R.empty(c1),R.empty(c2))
        x=v['x']; Fd=rename_to(d['F'],d['x'],x,v['F'])
        c1p,q1=R.pop_any(c1); c2p,q2=R.pop_any(c2)
        al=v['alpha']
        w3,J1b,J2b=join(v['F'],Fd,R.ann(c1p,x,'e',al,q1),R.ann(c2p,x,'e',al,q2))
        b3=closeRec(0,x,w3); t3=('l',t3a,b3)
        return t3, D('FOp',v['tgt'],t3,G1,s1,x=x,alpha=s1[0],a=J1a,F=J1b), D('FOp',d['tgt'],t3,G2,s2,x=x,alpha=s2[0],a=J2a,F=J2b)
    if r1=='Bet' and r2=='Bet':
        v3,J1p,J2p=join(v['p'],d['p'],R.empty(c1),R.empty(c2))
        x=v['x']; Fd=rename_to(d['F'],d['x'],x,v['F'])
        w3,J1b,J2b=join(v['F'],Fd,c1,c2)
        b3=closeRec(0,x,w3); t3=openRec(0,v3,b3)
        # open₀: substitute the operand joins for x
        J1=subst_deriv(J1b,x,J1p); J2=subst_deriv(J2b,x,J2p)
        return t3,J1,J2
    if r1=='App' and r2=='Bet':
        o1=v['o']; x=o1['x']; vv=v['src'][2]
        Fd=rename_to(d['F'],d['x'],x,o1)
        Fw=R._weaken(Fd,((x,'e',vv),)+d['G'],())
        v3,J1p,J2p=join(v['p'],d['p'],R.empty(c1),R.empty(c2))
        w3,J1b,J2b=join(o1['F'],Fw,R.ann(c1,x,'e',vv,v['p']),R.ann(c2,x,'e',vv,d['p']))
        b3=closeRec(0,x,w3); t3=openRec(0,v3,b3)
        J1b_s=drop_ctx_binding(J1b,x)          # the Bet side's join never uses x (invariant)
        J1=D('Bet',v['tgt'],t3,G1,s1,x=x,F=J1b_s,p=J1p,ann=v['tgt'][1][1])
        J2=subst_deriv(J2b,x,J2p,drop_binding=True)   # subst≡-head
        return t3,J1,J2
    if r1=='Bet' and r2=='App':
        o2=d['o']; x=o2['x']; vv=d['src'][2]
        Fv=rename_to(v['F'],v['x'],x,o2)
        Fw=_vweaken(Fv,((x,'e',vv),)+v['G'],())
        v3,J1p,J2p=join(v['p'],d['p'],R.empty(c1),R.empty(c2))
        w3,J1b,J2b=join(Fw,o2['F'],R.ann(c1,x,'e',vv,v['p']),R.ann(c2,x,'e',vv,d['p']))
        b3=closeRec(0,x,w3); t3=openRec(0,v3,b3)
        J1=subst_deriv(J1b,x,J1p,drop_binding=True)
        J2b_s=drop_ctx_binding(J2b,x)
        J2=D('Bet',d['tgt'],t3,G2,s2,x=x,F=J2b_s,p=J2p,ann=d['tgt'][1][1])
        return t3,J1,J2
    raise ValueError((r1,r2,S.show(v['src'])))

# ------------------------------------------------------------ peeling an original step
def vrefl(G,s,t):
    """a variant reflexivity derivation (same as refl_deriv: Var/Top/App/Fun/FOp only)"""
    return R.refl_deriv(G,s,t)

def peel(d):
    """a list of variant steps composing to d (same source, same target)"""
    r=d['rule']; G,s=d['G'],d['s']
    if r in ('Var','Top','TAp'): return [dict(d)]
    if r=='Pro':
        al=d['alpha']
        first=D('Pro',d['src'],al,G,s,x=d['x'],alpha=al,e=vrefl(G,(),al))
        return [first]+peel(d['e'])
    if r=='App':
        u,v=d['src'][1],d['src'][2]
        out=[]
        cur_u=u
        for st in peel(d['o']):                     # operator chain at stack v∷s, operand held
            out.append(D('App',('a',st['src'],v),('a',st['tgt'],v),G,s,o=st,p=vrefl(G,(),v))); cur_u=st['tgt']
        for st in peel(d['p']):                     # operand chain, operator held at the current operand's stack
            out.append(D('App',('a',cur_u,st['src']),('a',cur_u,st['tgt']),G,s,o=vrefl(G,(st['src'],)+s,cur_u),p=st))
        return out
    if r=='Fun':
        x=d['x']; t=d['src'][1]; out=[]
        for st in peel(d['F']):                     # body chain, annotation held
            out.append(D('Fun',('l',t,closeRec(0,x,st['src'])),('l',t,closeRec(0,x,st['tgt'])),G,s,x=x,a=vrefl(G,(),t),F=st))
        b_t=d['F']['tgt']
        for st in peel(d['a']):                     # annotation chain, body held
            out.append(D('Fun',('l',st['src'],closeRec(0,x,b_t)),('l',st['tgt'],closeRec(0,x,b_t)),G,s,x=x,a=st,
                         F=vrefl(((x,'s',st['src']),)+G,(),b_t)))
        return out
    if r=='FOp':
        x=d['x']; t=d['src'][1]; al=d['alpha']; out=[]
        for st in peel(d['F']):
            out.append(D('FOp',('l',t,closeRec(0,x,st['src'])),('l',t,closeRec(0,x,st['tgt'])),G,s,x=x,alpha=al,a=vrefl(G,(),t),F=st))
        b_t=d['F']['tgt']
        for st in peel(d['a']):
            out.append(D('FOp',('l',st['src'],closeRec(0,x,b_t)),('l',st['tgt'],closeRec(0,x,b_t)),G,s,x=x,alpha=al,a=st,
                         F=vrefl(((x,'e',al),)+G,s[1:],b_t)))
        return out
    if r=='Bet':
        x=d['x']; t=d['ann']; v=d['src'][2]
        bsteps=peel(d['F']); psteps=peel(d['p'])
        b1=bsteps[0]; p1=psteps[0]
        out=[D('Bet',d['src'],openRec(0,p1['tgt'],closeRec(0,x,b1['tgt'])),G,s,x=x,F=b1,p=p1,ann=t)]
        v1=p1['tgt']
        for st in bsteps[1:]:                       # remaining body steps with v1 substituted for x
            out.append(subst_deriv(st,x,vrefl(G,(),v1),variant=True))
        b_t=d['F']['tgt']
        for st in psteps[1:]:                       # remaining operand steps under the body's target
            out.append(subst_deriv(vrefl(G,s,b_t),x,st,variant=True))
        return out
    raise ValueError(r)

# ------------------------------------------------------------ strip and the compression check
def strip(d1,d2,c2):
    """peel d1; join link by link against d2 (c1 = Refl); return (end m, one-step J from t1, chain from t2)"""
    G,s=d1['G'],d1['s']
    chain=peel(d1)
    cur=d2; steps=[]
    Jlast=None
    for v in chain:
        try:
            t3,J1,J2=join(v,cur,('Refl',G,s),c2)
        except Exception as ex:
            return None,None,None,('joinfail',repr(ex))
        steps.append(J2); cur=J1; Jlast=J1
    return cur['tgt'], Jlast, steps, None

def one_step(G,s,t,m,cap):
    return m in S.reducts(G,s,t,cap)

ST=collections.Counter(); EX={}
import os as _os
CAPS=tuple(int(c) for c in _os.environ.get("CAPS","1,2,3").split(","))
def run_cfg(G,s,t,k,maxruns,seed,caps=None):
    caps=caps or CAPS
    R._dmemo.clear(); S._memo.clear(); gc.collect()
    ds=R.derivs(G,s,t,k)
    if len(ds)>4000: print(f"  skipped ({len(ds)} d)",flush=True); return
    pairs=[(a,b) for a in ds for b in ds]
    if len(pairs)>maxruns: pairs=random.Random(seed).sample(pairs,maxruns)
    for (d1,d2) in pairs:
        d1=copy.deepcopy(d1); d2=copy.deepcopy(d2)
        m,J1,steps,err=strip(d1,d2,('Refl',G,s))
        if err: ST['joinfail']+=1; EX.setdefault('joinfail',(S.show(t),S.showG(G),S.showS(s),err)); continue
        ST['strips']+=1
        n=len(steps); ST['maxlen']=max(ST['maxlen'],n)
        # trivial: the chain from t2 is a single step already?
        t2=d2['tgt']
        if n<=1: ST['len<=1']+=1; continue
        # collapse consecutive identical terms (reflexive steps)
        terms=[t2]+[st['tgt'] for st in steps]
        nontriv=sum(1 for i in range(1,len(terms)) if terms[i]!=terms[i-1])
        if nontriv<=1: ST['nontriv<=1']+=1; continue
        ST['needs_compression']+=1
        ok=None
        for cap in caps:
            try:
                if one_step(G,s,t2,m,cap): ok=cap; break
            except MemoryError:
                S._memo.clear(); gc.collect(); ST['memerr']+=1; break
        if ok is None:
            ST['NOT_compressed@cap%d'%caps[-1]]+=1
            key=(S.tsize(t) if hasattr(S,'tsize') else 0,)
            EX.setdefault('nocompress',(S.show(t),S.showG(G),S.showS(s),S.show(d1['tgt']),S.show(t2),[S.show(x) for x in terms],S.show(m)))
            EX.setdefault('nocompress_raw',[]); EX['nocompress_raw'].append(dict(G=G,s=s,t2=t2,m=m,t1=d1['tgt'],terms=terms))
        else: ST['compressed@%d'%ok]+=1

def all_cfgs(nrand):
    cfgs=S.families()
    y,v,x,w,u='y','v','x','w','u'
    cfgs.append((((v,'e',A(F(y),A(A(TOP,TOP),A(TOP,TOP)))),(y,'e',L(TOP,A(B(0),B(0))))),(),F(v)))
    cfgs.append((((u,'e',L(TOP,A(F(w),B(0)))),(w,'e',L(TOP,B(0)))),(),A(F(u),F(u))))
    cfgs.append(((),(),A(L(TOP,A(B(0),B(0))),L(TOP,B(0)))))
    rng=random.Random(20260912)
    cfgs+=[S.rand_cfg(rng) for _ in range(nrand)]
    return [c for c in cfgs if S.prevalid(c[0],c[1]) and S.lc(c[2]) and S.fv(c[2])<=S.dom(c[0])]

def main():
    import subprocess, json, os
    k=int(sys.argv[1]); maxruns=int(sys.argv[2]); nrand=int(sys.argv[3]) if len(sys.argv)>3 else 0
    resdir=os.path.join(os.path.dirname(os.path.abspath(__file__)),'compress-results'); os.makedirs(resdir,exist_ok=True)
    if len(sys.argv)>4 and sys.argv[4]=='--one':
        i=int(sys.argv[5]); G,s,t=all_cfgs(nrand)[i]
        run_cfg(G,s,t,k,maxruns,i)
        json.dump(dict(stats=dict(ST),ex=EX),open(os.path.join(resdir,f'c{k}_{i}.json'),'w')); return
    cfgs=all_cfgs(nrand); tot=collections.Counter(); exs={}
    for i,(G,s,t) in enumerate(cfgs):
        print(f"[{i}] {S.show(t)} @ {S.showG(G)};{S.showS(s)}",flush=True)
        f=os.path.join(resdir,f'c{k}_{i}.json')
        if os.path.exists(f): os.remove(f)
        rc=os.system(f'bash -c "ulimit -v 2500000; timeout 240 python3 {os.path.abspath(__file__)} {k} {maxruns} {nrand} --one {i}" > /dev/null 2>&1')
        if not os.path.exists(f): tot['no_result']+=1; print("  no result (timeout/crash)",flush=True); continue
        d=json.load(open(f))
        for kk,vv in d['stats'].items(): tot[kk]=max(tot[kk],vv) if kk=='maxlen' else tot[kk]+vv
        for kk,vv in d['ex'].items(): exs.setdefault(kk,(i,vv))
        print("  "+" ".join(f"{a}={b}" for a,b in sorted(d['stats'].items())),flush=True)
    for kk,vv in sorted(tot.items(),key=str): print(kk,vv)
    for name,ex in exs.items(): print("EXAMPLE",name,ex)
main()
