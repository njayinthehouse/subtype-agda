"""Conjecture 8 in MPSS extended by ONE recursive type definition, R ≡ λx≤R.R.

This is NOT MPSS: prevalidity forbids an annotation that mentions its own name, and the entry
`R ≡ λR.R` is admitted here by relaxing that one check for the name R. The point is to see what
the conjecture does when the domain order on bounds (CONJ8.md §9) is not well-founded — R's domain
is R — since a well-formed type-level looping combinator would give MPSS proper such a bound.

With δ = λx≤R. x x:   f = λx≤R. x δ   promotes, at the empty stack, to   f′ = λx≤R. R δ.
Both are well-formed, and so are f δ and f′ δ. The conjecture says f δ ≤*wf f′ δ.
"""
import sys, functools
print = functools.partial(print, flush=True)
sys.argv = [sys.argv[0], '0', '0', '1']
src = open('/home/egret/gimmick/1/MPSS/conj8-depth-probe.py').read()
src = src[:src.rindex("main()")]
exec(compile(src, 'c8d', 'exec'))

_orig = S.ctx_prevalid
def ctx_prevalid(G):
    if not G: return True
    x, c, t = G[0]; tail = G[1:]
    scope = S.dom(tail) | ({x} if x == 'R' else set())
    return ctx_prevalid(tail) and x not in S.dom(tail) and S.lc(t) and S.fv(t) <= scope
S.ctx_prevalid = ctx_prevalid

R = F('R')
G = (('R', 'e', L(R, R)),)
delta = L(R, A(B(0), B(0)))
f  = L(R, A(B(0), delta))
f2 = L(R, A(R, delta))
lhs, rhs = A(f, delta), A(f2, delta)

globals()['WK'] = 1; globals()['SIZE'] = 24
K1 = 1
x = F('x'); Gx = (('x', 's', R),) + G
top = L(R, TOP); LRR = L(R, R)

def step(kind, ctx, stack, a, b):
    ok = b in (ereds(ctx, stack, a, K1) if kind == 'e' else sreds(ctx, stack, a, K1))
    print(f"  {'⟶ᵉ' if kind == 'e' else '⟶ˢ'}  {show(a):28} to {show(b):28} at {showG(ctx)} ; {S.showS(stack)} :", ok)
    return ok

print("context:", showG(G), " (prevalid in the extension:", S.ctx_prevalid(G), ")")
print("the steps the well-formedness of the instance rests on:")
allok = all([
    step('s', Gx, (), x, R),                       # x ≤ R
    step('e', Gx, (), R, LRR),                     # R unfolds
    step('s', Gx, (), LRR, top),                   # λR.R ≤ λR.⊤      so x ≤*wf λR.⊤, x x is well-formed
    step('s', Gx, (), A(x, x), A(R, x)),           # x x ≤ R x
    step('e', Gx, (), A(R, x), A(LRR, x)),
    step('e', Gx, (), A(LRR, x), R),               # … ≡ R            so the body of δ is below R
    step('s', G, (), delta, L(R, A(R, B(0)))),     # δ ≤ λx≤R. R x
    step('e', G, (), L(R, A(R, B(0))), L(R, A(LRR, B(0)))),
    step('e', G, (), L(R, A(LRR, B(0))), LRR),     # … ≡ λR.R ≡ R     so δ ≤*wf R
    step('e', G, (), R, LRR),
    step('s', G, (), delta, top),                  # δ ≤ λR.⊤         so δ δ is well-formed
    step('s', G, (), f, f2),                       # f ≤ f′ at the empty stack
    step('s', G, (), f, top), step('s', G, (), f2, top),   # so f δ and f′ δ are well-formed
])
print("all of them are machine steps:", allok)
print("the conclusion f δ ≤*wf f′ δ needs a machine chain f δ ⟶ˢ* c ⟵ᵉ* f′ δ:")
for depth in (3, 4, 5, 6):
    left  = closure(sreds, G, (), lhs, K1, depth)
    right = closure(ereds, G, (), rhs, K1, depth)
    print(f"  chains of length ≤ {depth}: {len(left)} terms from f δ, {len(right)} from f′ δ, in common: {len(left & right)}")
notop = lambda t: 'T' not in repr(t)
print("  ⊤-free terms reached from f δ (sample):", sorted({show(t) for t in left if notop(t) and tsize(t) <= 11})[:6])
print("  terms reached from f′ δ (sample)      :", sorted({show(t) for t in right if tsize(t) <= 7})[:8])
print("  does any reduct of f′ δ contain ⊤?     :", any(not notop(t) for t in right))
# Lemma 6: evaluation preserves well-formedness. (δ δ) δ needs δ δ below an abstraction.
dd = A(delta, delta)
reach_dd = closure(sreds, G, (), dd, K1, 6)
print("Lemma 6: terms reached from δ δ by ⟶ˢ in 6 steps:", len(reach_dd), "· abstractions among them:", sum(1 for t in reach_dd if t[0] == 'l'))
