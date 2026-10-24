#!/usr/bin/env python3
"""Weyl-distance graphs of finite buildings at D = 7, max degree <= 12 (job cell-12-7).

Reuses weyl_graphs.py (copied from branch claude/beat-16-5-squad-jiiwg2, research/theorems/squad165/), which scanned
D = 5 with both sides <= 54,241. Here: every building type in the list below, every pair of residue types (I, J) with
both sides <= the D = 7 same-side Moore count and |A| + |B| >= MINORDER, every union X of (W_I, W_J) double cosets with
both degrees <= MAXDEG. Exact eccentricities from the BN-pair set product (no graph is built).

usage: python3 d7scan.py [MAXDEG] [MINORDER] [MAXD] [SHOWNEAR]
"""
import itertools, sys, time
import numpy as np
from weyl_graphs import Coxeter, ecc_side

MAXDEG = int(sys.argv[1]) if len(sys.argv) > 1 else 12
MINORDER = int(sys.argv[2]) if len(sys.argv) > 2 else 664301
MAXD = int(sys.argv[3]) if len(sys.argv) > 3 else 7
SHOWNEAR = int(sys.argv[4]) if len(sys.argv) > 4 else 9


def moore_same(dA, dB, D):
    """same-side vertices within distance D-1 (D odd) from an A-vertex of degree dA whose neighbours have degree dB."""
    tot, lev = 1, 1
    for k in range((D - 1) // 2):
        lev = dA * (dB - 1) if k == 0 else lev * (dA - 1) * (dB - 1)
        tot += lev
    return tot


def buildings():
    qs = (2, 3, 4, 5, 7, 8, 9, 11)
    out = []
    for n in range(2, 8):
        for qq in qs:
            if n == 7 and qq > 2:
                continue
            out.append((f'A{n}({qq})', 'A', n, [qq] * n))
    for n in range(2, 7):
        for qq in qs:
            if n == 6 and qq > 2:
                continue
            out.append((f'B{n}/C{n}({qq})', 'B', n, [qq] * n))
            out.append((f'2D{n+1}({qq}) Q-(2n+1,q)', 'B', n, [qq] * (n - 1) + [qq * qq]))
        for qq in (2, 3):
            out.append((f'2A{2*n-1}({qq}) H(2n-1,q^2)', 'B', n, [qq * qq] * (n - 1) + [qq]))
            out.append((f'2A{2*n}({qq}) H(2n,q^2)', 'B', n, [qq * qq] * (n - 1) + [qq ** 3]))
    for n in (4, 5, 6):
        for qq in (2, 3, 4, 5):
            if n == 6 and qq > 2:
                continue
            out.append((f'D{n}({qq})', 'D', n, [qq] * n))
    for qq in (2, 3):
        out.append((f'E6({qq})', 'E', 6, [qq] * 6))
        out.append((f'F4({qq})', 'F', 4, [qq] * 4))
        out.append((f'2E6({qq})', 'F', 4, [qq, qq, qq * qq, qq * qq]))
    for qq in qs:
        out.append((f'G2({qq})', 'G', 2, [qq, qq]))
    for qq in (2, 3):
        out.append((f'3D4({qq})', 'G', 2, [qq, qq ** 3]))
    return out


def main():
    cache = {}
    results = []
    big = moore_same(MAXDEG, MAXDEG, MAXD)
    t0 = time.time()
    for name, t, n, params in buildings():
        key = (t, n)
        if key not in cache:
            cache[key] = Coxeter(t, n)
        C = cache[key]
        q = C.qw(params)
        PW = int(sum(q))
        subsets = [K for r in range(n) for K in itertools.combinations(range(n), r)]
        PK = {K: int(sum(q[np.nonzero(C.parabolic(K))[0]])) for K in subsets}
        side = {K: PW // PK[K] for K in subsets}
        good = [K for K in subsets if side[K] <= big]
        npairs = 0
        for I in good:
            for J in good:
                if side[I] + side[J] < MINORDER:
                    continue
                if side[I] == side[J] and J < I:
                    continue      # (I,J) and (J,I) give the same graph up to swapping sides when X is inverted
                npairs += 1
                dcs = C.double_cosets(I, J)
                ND = [int(sum(q[np.nonzero(S)[0]])) for (w, S) in dcs]
                budget = MAXDEG * min(PK[I], PK[J])
                cand = sorted([k for k in range(len(dcs)) if ND[k] <= budget], key=lambda k: ND[k])
                stack = [((), 0, 0)]
                count = 0
                while stack:
                    X, NX, start = stack.pop()
                    if X:
                        dA, dB = NX // PK[J], NX // PK[I]
                        if (NX % PK[J] == 0 and NX % PK[I] == 0 and dA <= MAXDEG and dB <= MAXDEG and
                                side[I] <= moore_same(dA, dB, MAXD) and side[J] <= moore_same(dB, dA, MAXD)):
                            count += 1
                            reps = [dcs[k][0] for k in X]
                            inv = [int(C.inv[y]) for y in reps]
                            eA = ecc_side(C, C.parabolic(I), reps, inv, I, J, maxsteps=SHOWNEAR + 1)
                            eB = ecc_side(C, C.parabolic(J), inv, reps, J, I, maxsteps=SHOWNEAR + 1)
                            vals = list(eA) + list(eB)
                            if all(v is not None for v in vals):
                                D = max(vals)
                                words = [''.join(str(i + 1) for i in C.word[y]) or 'e' for y in reps]
                                rec = (D, side[I] + side[J], name, I, J, words, dA, dB, side[I], side[J])
                                results.append(rec)
                                if D <= MAXD:
                                    print('HIT', rec, flush=True)
                    for k in range(start, len(cand)):
                        kk = cand[k]
                        if NX + ND[kk] > budget:
                            break
                        stack.append((X + (kk,), NX + ND[kk], k + 1))
        print(f'done {name} P_W={PW} pairs={npairs} t={time.time()-t0:.0f}s', flush=True)
    results.sort(key=lambda r: (r[0], -r[1]))
    print('\n== best by diameter (D, order, building, I, J, X words, dA, dB, |A|, |B|) ==')
    for r in results[:80]:
        print(r)


if __name__ == '__main__':
    main()
