"""Ball sizes in Weyl-distance graphs: for each relation X with degree <= 16, the number of same-side vertices within
distance 2, 4, 6 of a vertex (sum of q_w over the reachable Weyl distances, divided by P_I)."""
import sys, itertools
import numpy as np
import weyl_graphs as wg

def ballsizes(C, q, I, J, reps, PI, steps=6):
    inv = [int(C.inv[y]) for y in reps]
    R = C.parabolic(I); same = R.copy(); out = []
    for k in range(1, steps + 1):
        rr, Kc = (reps, J) if k % 2 else (inv, I)
        V = np.zeros(C.N, dtype=bool)
        for y in rr:
            V |= C.times_elem(R, y)
        R = C.rclose(V, Kc)
        if k % 2 == 0:
            same |= R
            out.append(int(sum(q[np.nonzero(same)[0]])) // PI)
    return out

def run(t, n, params, I, J, maxdeg=16):
    C = wg.Coxeter(t, n); q = C.qw(params)
    PW = int(sum(q)); PI = int(sum(q[np.nonzero(C.parabolic(I))[0]])); PJ = int(sum(q[np.nonzero(C.parabolic(J))[0]]))
    dcs = C.double_cosets(I, J)
    ND = [int(sum(q[np.nonzero(S)[0]])) for (w, S) in dcs]
    budget = maxdeg * min(PI, PJ)
    cand = sorted([k for k in range(len(dcs)) if ND[k] <= budget], key=lambda k: ND[k])
    rows = []
    stack = [((), 0, 0)]
    while stack:
        X, NX, st = stack.pop()
        if X and NX // PJ == maxdeg:
            reps = [dcs[k][0] for k in X]
            b = ballsizes(C, q, I, J, reps, PI)
            words = [''.join(str(i + 1) for i in C.word[y]) or 'e' for y in reps]
            rows.append((b[1], b, words, NX // PJ, NX // PI))
        for k in range(st, len(cand)):
            kk = cand[k]
            if NX + ND[kk] > budget: break
            stack.append((X + (kk,), NX + ND[kk], k + 1))
    rows.sort(reverse=True)
    print(f'{t}{n} params {params} I={I} J={J}: side {PW // PI}; relations of degree {maxdeg}: {len(rows)}')
    for r in rows[:8]:
        print('  ball(2,4,6) =', r[1], 'X =', r[2], 'deg', r[3], r[4])

run('D', 4, [2, 2, 2, 2], (), ())
run('B', 3, [2, 2, 4], (), ())
run('B', 3, [4, 4, 2], (0,), (1,))
run('B', 3, [4, 4, 2], (2,), (2,))
