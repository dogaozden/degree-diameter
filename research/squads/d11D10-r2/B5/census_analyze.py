#!/usr/bin/env python3
"""Card B5: parse the three RANDORB=4 LEVELS=4 runs (k10_afrobh, k10_afrobd, k5_afrob3) and print the census tables.

haar_sym prints, for sample t < LEVELS, "levels: lev0 ... lev8 cost c" on stderr. lev[h] is the cumulative number of
distinct elements of the side reached at BFS step h (side B for even h, side A for odd h, the start (e,A) counted in
A); the count for each side accumulates only that side's new elements, so the number of distinct elements at BFS
distance L (L = h + 1) is lev[h] - lev[h - 2], with lev[-1] = 1 (the identity on side A) and lev[-2] = 0.
"""
import math
import os
import re

B5 = '/home/user/degree-diameter/research/squads/d11D10-r2/B5'
N = 78917652            # |PSL(2,243) x Z11| = 243 (243^2 - 1) / 2 * 11
DMAX = 9                # D = 10: the target side is reached within D - 1 = 9 steps
FAMS = [('k10H', 'ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2', 'k10_afrobh'),
        ('k10D', 'ORBIT="10 1 1" AFROB=1 AFROBD=1 AR=2', 'k10_afrobd'),
        ('k5F3', 'ORBIT="5 2 1" AFROB=3 (AR=3 default)', 'k5_afrob3')]


def read_samples(stem):
    rows = []
    with open(os.path.join(B5, stem + '.err')) as f:
        for line in f:
            m = re.match(r'levels:((?: -?\d+)+) cost (-?\d+)', line)
            if m:
                rows.append(([int(x) for x in m.group(1).split()], int(m.group(2))))
    return rows


def new_counts(lev):
    """Distinct elements at BFS distance L = 1..9 from cumulative per-side counts."""
    out = {}
    for L in range(1, DMAX + 1):
        h = L - 1
        if h - 2 >= 0:
            prev = lev[h - 2]
        else:
            prev = 1 if h - 2 == -1 else 0
        out[L] = lev[h] - prev
    return out


def free(L):
    return 11 * 10 ** (L - 1)


def model_new():
    """Uniform random S: non-backtracking words of length j (free(j) of them) are independent uniform elements."""
    def E(M):
        return N * (1 - math.exp(-M / N))

    def M_cum(L):   # words on the side of parity L with length <= L (identity sits on side A, distance 0)
        tot = 1 if L % 2 == 0 else 0
        tot += sum(free(j) for j in range(1, L + 1) if j % 2 == L % 2)
        return tot
    R = {}
    for L in range(1, DMAX + 1):
        R[L] = E(M_cum(L)) - (E(M_cum(L - 2)) if L >= 2 else 0.0)
    return R


def main():
    R = model_new()
    data = {}
    for name, _, stem in FAMS:
        rows = read_samples(stem)
        assert len(rows) == 4, (stem, len(rows))
        per = [new_counts(lev) for lev, _ in rows]
        mean = {L: sum(p[L] for p in per) / len(per) for L in range(1, DMAX + 1)}
        lo = {L: min(p[L] for p in per) for L in range(1, DMAX + 1)}
        hi = {L: max(p[L] for p in per) for L in range(1, DMAX + 1)}
        checks = {'lev0_is_11': all(lev[0] == 11 for lev, _ in rows),
                  'cost_eq_N_minus_lev8': all(c == N - lev[8] for lev, c in rows),
                  'costs': [c for _, c in rows],
                  'lev8': [lev[8] for lev, _ in rows]}
        data[name] = dict(mean=mean, lo=lo, hi=hi, checks=checks, rows=rows)

    print('Free count 11*10^(L-1) and random-model expectation R_L (uniform random S):')
    for L in range(1, DMAX + 1):
        print('L=%d side=%s free=%d model=%.1f' % (L, 'B' if L % 2 else 'A', free(L), R[L]))
    print()
    for name, desc, stem in FAMS:
        d = data[name]
        print('%s (%s): cost per sample %s, lev8 %s, lev0==11: %s, cost==N-lev8: %s' % (
            name, desc, d['checks']['costs'], d['checks']['lev8'], d['checks']['lev0_is_11'],
            d['checks']['cost_eq_N_minus_lev8']))
        for L in range(1, DMAX + 1):
            m = d['mean'][L]
            print('  L=%d n=%.1f [%d..%d] n/free=%.6f n/model=%.6f' % (
                L, m, d['lo'][L], d['hi'][L], m / free(L), m / R[L]))
        print()


if __name__ == '__main__':
    main()
