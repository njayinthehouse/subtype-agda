import os, functools
os.environ['C8_NOMAIN'] = '1'
src = open('/home/egret/gimmick/1/MPSS/conj8-subst-probe.py').read()
exec(compile(src, 'subst', 'exec'))
globals()['WD'] = 7; globals()['SIZE'] = 60
T  = L(TOP, L(B(0), B(1)))        # λy≤⊤. λx≤y. y
I  = L(TOP, B(0))                 # λx≤⊤. x
TT = A(T, T)
for name, t in [("T", T), ("T T", TT), ("id", I), ("id (T T)", A(I, TT)), ("(id (T T)) T", A(A(I, TT), T)), ("(T T) T", A(TT, T))]:
    print(name, "=", show(t), "| wf:", wf_((), t))
