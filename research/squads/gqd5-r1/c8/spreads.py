"""Ovoid O of Q4(q) = spread of W(q) (point ids of Q4 = line ids of W).  Second ovoid O' disjoint from O obtained as the
image of O under a random product of symplectic transvections x -> x + lam*w(x,v)*v of W(q)."""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, regular_spread_W, is_partial_ovoid

def getW(q):
    return W(q)

def transvection(Wq, v, lam):
    F = Wq.F
    # returns point permutation of W(q)
    perm = np.zeros(Wq.np, dtype=int)
    for i, x in enumerate(Wq.coords):
        wxv = Wq.form(x, v)
        y = tuple(F.add[x[k]][F.mul[F.mul[lam][wxv]][v[k]]] for k in range(4))
        # normalise
        from gqlib import _norm
        perm[i] = Wq.index[_norm(F, y)] if any(y) else -1
    return perm

def line_map(Wq, perm):
    lid = {frozenset(l): i for i, l in enumerate(Wq.lines)}
    return [lid[frozenset(perm[list(l)])] for l in Wq.lines]

def second_spread(Wq, O, seed=0, tries=20000):
    rng = random.Random(seed)
    F = Wq.F; q = F.q
    Oset = set(O)
    perms = []
    for t in range(tries):
        # random product of 3 transvections
        k = 3
        P = np.arange(Wq.np)
        for _ in range(k):
            v = Wq.coords[rng.randrange(Wq.np)]
            lam = rng.randrange(1, q)
            Pt = transvection(Wq, v, lam)
            if (Pt < 0).any():
                break
            P = Pt[P]
        else:
            LM = line_map(Wq, P)
            O2 = [LM[l] for l in O]
            if not (set(O2) & Oset):
                return sorted(O2), t
    return None, tries

if __name__ == '__main__':
    q = int(sys.argv[1])
    Wq = getW(q)
    O = regular_spread_W(Wq)
    print('q', q, 'O', len(O))
    O2, t = second_spread(Wq, O, seed=1)
    print('second spread disjoint:', O2 is not None, 'after', t, 'tries')
    if O2:
        from gqlib import is_partial_spread
        print('O2 partial spread (pairwise disjoint lines):', is_partial_spread(Wq, O2), len(O2))
