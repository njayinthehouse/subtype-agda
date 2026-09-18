"""Hand-built instances for the substitution-route algorithm (conj8-subst-probe.py)."""
import sys, os, functools
os.environ['C8_NOMAIN'] = '1'
print = functools.partial(print, flush=True)
src = open('/home/egret/gimmick/1/MPSS/conj8-subst-probe.py').read()
exec(compile(src, 'subst', 'exec'))
globals()['WD'] = 7; globals()['SIZE'] = 40

def run(name, G, p, p2, S_):
    print("==", name)
    print("   p  =", show(p)); print("   p′ =", show(p2), "| stack", S.showS(S_), "| context", showG(G))
    lhs, rhs = spine(p, S_), spine(p2, S_)
    print("   p ⟶ˢ p′:", p2 in sreds(G, (), p, 3), "| wf:", wf_(G, p), wf_(G, p2), "| plugs wf:", wf_(G, lhs), wf_(G, rhs))
    try:
        R, Z = run_instance(G, [('s', p, p2)], S_)
    except (Unresolved, Budget) as e:
        print("   algorithm:", type(e).__name__, e); return
    bad = check0(G, Z)
    bad = [b for b in bad if not ('not found wf' in b[0] and wf_strong(G, b[1] if ('from' in b[0] or 'turn' in b[0]) else b[2]))]
    print("   chain of", len(Z), "steps; calls:", [(d, o, show(a), show(b)) for (d, o, a, b, _) in R.trace])
    for (k, a, b) in Z: print("      ", k, show(a), " → ", show(b))
    print("   RESULT:", "valid" if not bad else [(m, show(a), show(b)) for (m, a, b) in bad])

Aty = L(TOP, TOP)
# 1. the dependent bound of CONJ8.md §13
bound = L(B(1), TOP)
run("dependent bound", (), L(TOP, L(B(0), L(bound, A(B(0), B(1))))),
    L(TOP, L(B(0), L(bound, A(L(B(2), TOP), B(1))))), (Aty, Aty, L(Aty, B(0))))
# 2. a redex the body already contains: f = λx≤w. (λz≤A. x z) o,  w = λ⊤.⊤, promoted at the head x
w = L(TOP, TOP)
f  = L(w, A(L(Aty, A(B(1), B(0))), Aty))
f2 = L(w, A(L(Aty, A(w, B(0))), Aty))
run("redex in the body", (), f, f2, (L(TOP, B(0)),))
# 3. the depth example of §8
G3 = (('y', 'e', L(TOP, B(0))),)
y = F('y')
run("§8's depth example", G3, L(y, A(B(0), A(y, B(0)))), L(y, A(y, A(y, B(0)))), (A(y, A(y, y)),))
