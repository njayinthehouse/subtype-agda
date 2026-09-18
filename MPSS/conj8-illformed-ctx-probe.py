"""Conjecture 8 in MPSS PROPER, in a prevalid context whose annotation is ill-formed.

Contexts are only required to be prevalid: an annotation must be locally closed and scoped, not
well-formed (MPSS/EqvWf uses this against "equivalence reduction preserves well-formedness").
So a context may DEFINE a name by a term with no normal form:

    F   = λr≤⊤. λx≤r. r
    Ω_F = (λs≤⊤. F (s s)) (λs≤⊤. F (s s))          ill-formed (s s under s ≤ ⊤), closed, locally closed
    Γ₀  = R ≡ Ω_F                                    prevalid

R is well-formed in Γ₀ (Wf-PrE), and R ⟶ᵉ Ω_F ⟶ᵉ F Ω_F ⟶ᵉ λx≤Ω_F.Ω_F, which is also a reduct of
λx≤R.R — a well-formed term. So R behaves as the recursive type R ≡ λx≤R.R of CONJ8.md §11, with
λx≤R.R as its well-formed representative. The instance of §11, now in MPSS itself:

    δ = λx≤R. x x      f = λx≤R. x δ  ⟶ˢ  f′ = λx≤R. R δ      context □ δ
"""
import sys, os, functools
print = functools.partial(print, flush=True)
sys.argv = [sys.argv[0], '0', '0', '1']
src = open('/home/egret/gimmick/1/MPSS/conj8-depth-probe.py').read()
src = src[:src.rindex("main()")]
exec(compile(src, 'c8d', 'exec'))
globals()['WK'] = 1; globals()['SIZE'] = 60
K1 = 2

Fop   = L(TOP, L(B(0), B(1)))                       # λr≤⊤. λx≤r. r
half  = L(TOP, A(Fop, A(B(0), B(0))))               # λs≤⊤. F (s s)
OmF   = A(half, half)
R     = F('R')
G     = (('R', 'e', OmF),)
x     = F('x'); Gx = (('x', 's', R),) + G
LRR, LRT = L(R, R), L(R, TOP)
delta = L(R, A(B(0), B(0)))
f     = L(R, A(B(0), delta))
f2    = L(R, A(R, delta))
lhs, rhs = A(f, delta), A(f2, delta)

print("context:", showG(G))
print("  prevalid (the unmodified check):", S.ctx_prevalid(G), "| Ω_F locally closed:", S.lc(OmF), "| closed:", not S.fv(OmF))

# The enumerator of all reducts is exponential on these terms (parallel reduction, several redexes,
# an annotation that unfolds for ever), so single steps are checked goal-directed: a ⟶ᵉ b and
# a ⟶ˢ b decided by recursion on the rules with the target known. Me-Bet is only recognised on a
# body that does not mention its parameter — every β here is taken in two steps, the first of
# which binds and unfolds the parameter (MPSS/Prop17Chain).
def is_e(Gc, st, t, b, k=2):
    if not S.prevalid(Gc, st): return False
    c = t[0]
    if c == 'f':
        if b == t: return True
        a = S.lookup_eqv(Gc, t[1])
        return a is not None and k > 0 and is_e(Gc, st, a, b, k - 1)
    if c == 'T': return b == TOP
    if c == 'a':
        u, v = t[1], t[2]
        if u == TOP and b == TOP: return True
        if b[0] == 'a' and is_e(Gc, (v,) + st, u, b[1], k) and is_e(Gc, (), v, b[2], k): return True
        if u[0] == 'l' and S.lc(u[2]):            # Me-Bet on a closed body: the contractum is a reduct of the body
            return any(is_e(Gc, st, u[2], b, k) for _ in (0,)) and True
        return False
    if c == 'l':
        if b[0] != 'l': return False
        w, body = t[1], t[2]
        if not is_e(Gc, (), w, b[1], k): return False
        if not st:
            xx = S.fresh(Gc, t, b)
            return is_e(((xx, 's', w),) + Gc, (), openRec(0, ('f', xx), body), openRec(0, ('f', xx), b[2]), k)
        xx = S.fresh(Gc, t, b, st)
        return is_e(((xx, 'e', st[0]),) + Gc, st[1:], openRec(0, ('f', xx), body), openRec(0, ('f', xx), b[2]), k)
    return False

def is_s(Gc, st, t, b, k=2):
    if not S.prevalid(Gc, st): return False
    if b == TOP: return True
    if is_e(Gc, st, t, b, k): return True
    c = t[0]
    if c == 'f': return lookup_sub(Gc, t[1]) == b
    if c == 'a': return b[0] == 'a' and b[2] == t[2] and is_s(Gc, (t[2],) + st, t[1], b[1], k)
    if c == 'l':
        if b[0] != 'l' or b[1] != t[1]: return False
        if not st:
            xx = S.fresh(Gc, t, b)
            return is_s(((xx, 's', t[1]),) + Gc, (), openRec(0, ('f', xx), t[2]), openRec(0, ('f', xx), b[2]), k)
        xx = S.fresh(Gc, t, b, st)
        return is_s(((xx, 'e', st[0]),) + Gc, st[1:], openRec(0, ('f', xx), t[2]), openRec(0, ('f', xx), b[2]), k)
    return False

def step(kind, ctx, stack, a, b, note=""):
    ok = is_e(ctx, stack, a, b) if kind == 'e' else is_s(ctx, stack, a, b)
    print(f"  {'⟶ᵉ' if kind == 'e' else '⟶ˢ'}  {show(a)[:52]:52} to {show(b)[:52]:52} : {ok}  {note}")
    return ok
def path(ctx, terms, note):
    print(f"  -- {note}")
    return all([step('e', ctx, (), a, b) for a, b in zip(terms, terms[1:])])

half2 = L(TOP, A(Fop, OmF))                          # λs≤⊤. F Ω_F   (the parameter unfolded)
FOm   = A(Fop, OmF)                                  # F Ω_F
Fop2  = L(TOP, L(OmF, OmF))                          # λr≤⊤. λx≤Ω_F. Ω_F
LOO   = L(OmF, OmF)                                  # λx≤Ω_F. Ω_F     — the meeting point
unfoldR = [R, OmF, A(half2, half), FOm, A(Fop2, OmF), LOO]

print("the steps the hypotheses rest on, each checked as a single machine step:")
ok = all([
    path(G, unfoldR, "R unfolds to λx≤Ω_F.Ω_F (each β in two steps: bind and unfold the parameter, then Me-Bet)"),
    path(G, [LRR, LOO], "so does the well-formed λx≤R.R, in one step: R ≡ λx≤R.R"),
    step('s', Gx, (), x, R, "x ≤ R, and R is well-formed by Wf-PrE"),
    step('s', Gx, (), LRR, LRT, "λx≤R.R ≤ λx≤R.⊤: so x ≤*wf λx≤R.⊤, and with x ≤*wf R, x x is well-formed"),
    step('s', G, (), delta, L(R, A(R, B(0))), "δ ⟶ˢ λx≤R. R x, between well-formed terms"),
    path(G, [L(R, A(R, B(0)))] + [L(OmF, A(h, B(0))) for h in unfoldR[1:]] + [LOO],
         "λx≤R. R x reduces to λx≤Ω_F.Ω_F as well (R unfolds under the operand x, then β on a closed body): so δ ≤*wf R, and δ δ is well-formed"),
    step('s', G, (), delta, LRT, "δ ≤ λx≤R.⊤"),
    step('s', G, (), f, f2, "f ⟶ˢ f′ at the empty stack: the hypothesis u ≤*wf t"),
    step('s', G, (), f, LRT, "f ≤ λx≤R.⊤ and δ ≤*wf R: f δ is well-formed"),
    step('s', G, (), f2, LRT, "f′ δ is well-formed"),
])
print("all hold:", ok)
