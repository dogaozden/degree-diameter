"""DATA_CHECK.md §3-§6: model mu with special targets + coincidences, best-of-T (budget) model, abelian bound, parity x family.
Run from this folder: python3 data_check2.py"""
import math, itertools
import numpy as np
from data_check import records, ols
from model import mu_model, W
from groups_inv import prod, sl2, psl2, pgl2, cyc

def A_ab(d, D):
    """#{c in Z^d : sum c = eps, |c|_1 <= D-1, |c|_1 = D-1 mod 2}: image of the covered set in G^ab (Theorem 2)."""
    l = D - 1; eps = 1 if D % 2 == 0 else 0
    # count by dynamic programming over coordinates: state (sum, l1)
    from collections import Counter
    st = Counter({(0, 0): 1})
    for _ in range(d):
        nx = Counter()
        for (s, a), c in st.items():
            for v in range(-l, l + 1):
                if a + abs(v) <= l: nx[(s + v, a + abs(v))] += c
        st = nx
    return sum(c for (s, a), c in st.items() if s == eps and a % 2 == l % 2)

def mu_max_budget(N, D, B):
    """capability rule of SIZE_LAW §4.1/§8: mu_max = 13 + 2 ln(M/1e5), M = B / (c N b)."""
    c = 1.5e-9 if N >= 1e7 else 4.5e-10; b = 2 if D % 2 else 1
    return 13 + 2 * math.log(B / (c * N * b) / 1e5)

def excess(r):
    """the group's model excess mu_model/mu_generic at its own order (held fixed near that order)"""
    return mu_model(r['d'], r['D'], r['N'], r['g'])[0] / r['mu'] if r['g'] else 1.0

def N_solve(d, D, target, eps=1.0):
    """largest order m with eps * m e^(-W/m) <= target(m)"""
    lo, hi = 10.0, float(W(d, D))
    for _ in range(100):
        m = math.sqrt(lo * hi)
        if eps * m * math.exp(-W(d, D) / m) < target(m): lo = m
        else: hi = m
    return lo

def N_pred(r, B):
    return N_solve(r['d'], r['D'], lambda m: mu_max_budget(m, r['D'], B), excess(r))

if __name__ == '__main__':
    rows = records(); B = sorted([r for r in rows if r['best']], key=lambda r: (r['D'], r['d']))
    print('== Theorem 2 check: |G^ab| <= A(d,D) for every record ==')
    worst = []
    for r in rows:
        g = r['g']
        if g is None: continue
        ab = r['N'] // g['comm'] if g.get('comm') else None
        if ab is None: continue
        a = A_ab(r['d'], r['D']); worst.append((ab / a, r['src'], ab, a)); assert ab <= a, r
    worst.sort(reverse=True)
    for w in worst[:5]: print('  |G^ab| = %d  A = %d  ratio %.3g  %s' % (w[2], w[3], w[0], w[1]))
    print('  A(d,D) for d=6..16, D=5..10:')
    for d in (6, 8, 10, 12, 16): print('   d=%2d ' % d + ' '.join('%d' % A_ab(d, D) for D in range(5, 11)))

    print('\n== best-of-T: one-parameter budget model (SIZE_LAW capability rule, budget B fitted) ==')
    BB = [r for r in B if r['D'] >= 7]
    best = None
    for lb in np.linspace(math.log(1), math.log(1e7), 161):
        e = np.array([math.log(r['N'] / N_pred(r, math.exp(lb))) for r in BB])
        s = math.sqrt((e ** 2).mean())
        if best is None or s < best[0]: best = (s, lb, e)
    s, lb, e = best
    print('  fitted budget B = %.0f core-seconds per order; rms log error in N over %d cells (D>=7): %.3f' % (math.exp(lb), len(BB), s))
    for r, ei in zip(BB, e): print('   (%2d,%2d) N=%-10d pred=%-10d  err %+.3f  mu_rec %.1f  mu_max(B) %.1f' % (
        r['d'], r['D'], r['N'], N_pred(r, math.exp(lb)), ei, mu_model(r['d'], r['D'], r['N'], r['g'])[0],
        mu_max_budget(r['N'], r['D'], math.exp(lb))))
    # compare with: constant mu* (1 param)
    for lab, f in (('constant mu* (1 param)', None),):
        best2 = None
        for lm in np.linspace(0, 4, 200):
            e2 = [math.log(r['N'] / N_solve(r['d'], r['D'], lambda m: math.exp(lm), excess(r))) for r in BB]
            e2 = np.array(e2); s2 = math.sqrt((e2 ** 2).mean())
            if best2 is None or s2 < best2[0]: best2 = (s2, lm)
        print('  %s: mu* = %.1f, rms log error %.3f' % (lab, math.exp(best2[1]), best2[0]))
    # D-drift explained: per D mean residual
    for D in (7, 8, 9, 10):
        v = [ei for r, ei in zip(BB, e) if r['D'] == D]
        print('   D=%d mean err %+.3f (n=%d)' % (D, np.mean(v), len(v)))

    print('\n== parity x family: groups with many involutions (I >= sqrt(N)) ==')
    for par in (0, 1):
        sel = [r for r in rows if r['g'] is not None and r['D'] % 2 == par and r['D'] >= 7]
        many = [r for r in sel if r['g']['inv'] >= math.sqrt(r['N'])]
        mb = [r for r in many if r['best']]
        print('  D %s: %d files, %d with I >= sqrt(N) (%d of them cell records): %s' % (
            'even' if par == 0 else 'odd', len(sel), len(many), len(mb), ', '.join(sorted(set(r['spec'].split(' n ')[0] for r in many)))))
