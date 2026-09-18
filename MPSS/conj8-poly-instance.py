"""One instance for the narrowing algorithm: a bound that mentions a type variable instantiated
by an earlier operand.

  p  = λy≤⊤. λo≤y. λx≤(λz≤y.⊤). x o        p′ = the same with the head x promoted to its bound
  context  ((□ A) a) α   with  A = λ⊤.⊤,  a ≤ A,  α ≤ λz≤A.⊤

Under the abstract y the operand o is below y only; after y := A the algorithm's intermediate
point puts a term m (between α and λz≤A.⊤) in place of x *inside the body, under the abstract y*,
where `m o` needs o ≤ A. Is the point well-formed? Does the conjecture hold here anyway?
"""
import sys, os, functools
print = functools.partial(print, flush=True)
sys.argv = [sys.argv[0], '0', '0', '1']
src = open('/home/egret/gimmick/1/MPSS/conj8-lift-probe.py').read()
src = src[:src.rindex("main()")]
exec(compile(src, 'lift', 'exec'))
globals()['WD'] = 7; globals()['SIZE'] = 40

G = ()
Aty = L(TOP, TOP)
for name, a_, alpha in [("a = A, α = λz≤A.z", Aty, L(Aty, B(0))),
                        ("a = A, α = λz≤A.A", Aty, L(Aty, Aty))]:
    bound = L(B(1), TOP)                      # λz≤y.⊤ , y is index 1 under o
    p  = L(TOP, L(B(0), L(bound, A(B(0), B(1)))))
    p2 = L(TOP, L(B(0), L(bound, A(L(B(2), TOP), B(1)))))
    S_ = (Aty, a_, alpha)
    lhs, rhs = spine(p, S_), spine(p2, S_)
    print("==", name)
    print(" p  =", show(p)); print(" p′ =", show(p2))
    print(" p, p′ wf:", wf_(G, p), wf_(G, p2), "| p ⟶ˢ p′:", p2 in sreds(G, (), p, 3))
    print(" Co[p] wf:", wf_(G, lhs), "| Co[p′] wf:", wf_(G, rhs))
    print(" conclusion, by search (one layer):", layer(G, lhs, rhs, WFD))
    R = Run()
    try:
        Z = lift(R, G, [('s', p, p2)], S_, 0, (p, p2))
        bad = check(G, Z, S_, None)
        print(" the algorithm's chain:", len(Z), "steps; rounds", R.maxdepth)
        for (k, a, b) in Z: print("    ", k, show(spine(a, S_)), " → ", show(spine(b, S_)))
        for (msg, a, b) in bad:
            strong = wf_strong(G, a if ('from' in msg or 'turn' in msg) else b)
            print("   FLAG:", msg, "|", show(a), "→", show(b), "| with longer chains:", strong)
        if not bad: print("   every point well-formed")
    except Exception as e:
        print(" algorithm failed:", type(e).__name__, e)
