"""Which quantity goes down along the nesting of the substitution route? (CONJ8.md §19)

Runs conj8-subst-probe.py unchanged and records every call of `under` — the lifting of one
promotion A ⟶ˢ B under one operand v — with the call it is nested in. For each nested pair
(parent, child) it tests candidate measures:

  hnB   head steps (β, and unfolding of a ≡-bound head) from B v to a head normal form
  hnA   the same from A v
  hnmax max of the two
  szB   size of B v

A measure is a candidate for a termination argument only if the child's value is strictly below
the parent's on every nested pair.

  python3 conj8-measure-probe.py MAXSIZE SHARD NSHARDS [STACKSIZE]      (env as conj8-subst-probe.py)
"""
import sys, os, functools
argv_keep = sys.argv[:]
os.environ['C8_NOMAIN'] = '1'
src = open('/home/egret/gimmick/1/MPSS/conj8-subst-probe.py').read()
exec(compile(src, 'subst', 'exec'))
CAP = 80

def hn(G, X):
    n = 0
    while n < CAP:
        h, args = head_and_args(X)
        if h[0] == 'f':
            ann = [e for e in G if e[0] == h[1] and e[1] == 'e']
            if not ann: return n
            X = ann[0][2]
            for a in args: X = ('a', X, a)
            n += 1; continue
        b = beta_head(G, X)
        if b is None: return n
        X = b[2]; n += 1
    return CAP

MEAS = {
    'hnB':   lambda G, A_, B_, v: hn(G, ('a', B_, v)),
    'hnA':   lambda G, A_, B_, v: hn(G, ('a', A_, v)),
    'hnmax': lambda G, A_, B_, v: max(hn(G, ('a', A_, v)), hn(G, ('a', B_, v))),
    'szB':   lambda G, A_, B_, v: tsize(('a', B_, v)),
}
records, stack_ = [], []
_under, _run_instance, _rank_descent = under, run_instance, rank_descent

def under(R, G, A_, B_, v, depth):
    records.append((stack_[-1] if stack_ else None, G, A_, B_, v))
    stack_.append(len(records) - 1)
    try: return _under(R, G, A_, B_, v, depth)
    finally: stack_.pop()

def run_instance(G, D, S_):
    records.clear(); stack_.clear()
    return _run_instance(G, D, S_)

def rank_descent(R, stats):
    _rank_descent(R, stats)
    for (par, G, A_, B_, v) in records:
        if par is None: continue
        _, pG, pA, pB, pv = records[par]
        stats['m:nested'] += 1
        for name, f in MEAS.items():
            c, p = f(G, A_, B_, v), f(pG, pA, pB, pv)
            if c < p: stats['m:' + name + ' lower'] += 1
            else:
                stats['m:' + name + ' NOT LOWER'] += 1
                if stats['m:' + name + ' NOT LOWER'] <= 6:
                    print(f"{name} NOT LOWER: parent {show(pA)} ⟶ˢ {show(pB)} under {show(pv)} ({p}) in {showG(pG)}"
                          f" → child {show(A_)} ⟶ˢ {show(B_)} under {show(v)} ({c}) in {showG(G)}")

argv1 = argv_keep[1:]
main()
