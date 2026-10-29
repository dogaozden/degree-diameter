#!/usr/bin/env python3
"""Optimal sums for Lemma 4.2 (D7_THEOREMS.md Section 4), replacing the first-found search of hubsum.py.

Parts: cores (s, c) = H(s) blown up by at most c (each colour any size in [K0(s), c K0(s)], own degree c(s+1)), and at
most one pendant-tree part (Lemma 4.3, last, own degree dL, sizes checked by tree_ok).  With r parts every part needs
own degree + r - 1 <= delta.  We enumerate multisets of cores (types in a fixed order, so each multiset once), r <= RMAX,
with an optional tree part, and maximise K1 + K2 subject to K1 <= T1, K2 <= T2 (targets = slot counts), where the sizes
of colour 1 can be any value in [sum lo, sum hi] (sum over cores) plus the tree's, and the same for colour 2.  The order
condition of Lemma 4.2 (|A_j| <= |B_i|, |B_j| <= |A_i| for i < j) is then met by an explicit size assignment, which
`assign` constructs and `verify` checks.  Output: certificates and the best value per (q, k)."""
import sys, itertools
from hubcap_lib import PP, K0, slots, tree_ok, kappa_cover

RMAX = 9

def core_types(cap):
    T = []
    for s in PP:
        if s + 1 > cap: break
        for c in range(1, cap // (s + 1) + 1):
            T.append((s, c))
    return T

def assign(cores, tree, T1, T2):
    """cores: list of (s, c) sorted by K0(s) descending, then c descending; tree: dL or None.  Choose sizes
    (x_i, y_i) per part with sum = (K1, K2) as large as possible <= (T1, T2), the order condition holding.
    Greedy: give the tree what is left after the cores are filled from the first part on."""
    lo = [K0(s) for (s, c) in cores]; hi = [c * K0(s) for (s, c) in cores]
    if sum(lo) > min(T1, T2):
        return None
    best = None
    for target in ((T1, T2),):
        res = []
        for col in (0, 1):
            T = target[col]
            # fill cores in order up to hi, keeping lo for all later ones
            rem = T - sum(lo)
            sizes = list(lo)
            for i in range(len(cores)):
                add = min(hi[i] - lo[i], rem)
                sizes[i] += add; rem -= add
            res.append((sizes, rem))
        (x, r1), (y, r2) = res
        if tree is None:
            K1, K2 = sum(x), sum(y)
            parts = [('core', s, c, x[i], y[i]) for i, (s, c) in enumerate(cores)]
        else:
            # the tree takes the remainders (if any) up to what tree_ok allows; shrink until feasible
            t1, t2 = r1, r2
            cap = kappa_cover(tree)
            t1 = min(t1, cap); t2 = min(t2, cap)
            if cores:
                m = min(min(x), min(y))
                t1 = min(t1, m); t2 = min(t2, m)
            while t1 >= 7 and t2 >= 7 and not tree_ok(t1, t2, tree):
                if t1 >= t2: t1 -= 1
                else: t2 -= 1
            if t1 < 7 or t2 < 7:
                return None
            K1, K2 = sum(x) + t1, sum(y) + t2
            parts = [('core', s, c, x[i], y[i]) for i, (s, c) in enumerate(cores)] + [('tree', tree, t1, t2)]
        if verify(parts, K1, K2):
            best = (K1 + K2, K1, K2, parts)
    return best

def part_deg(p):
    return p[2] * (p[1] + 1) if p[0] == 'core' else p[1]
def sizes(p):
    return (p[3], p[4]) if p[0] == 'core' else (p[2], p[3])
def verify(parts, K1, K2):
    r = len(parts)
    if sum(sizes(p)[0] for p in parts) != K1 or sum(sizes(p)[1] for p in parts) != K2:
        return False
    for i in range(r):
        for j in range(i + 1, r):
            ai, bi = sizes(parts[i]); aj, bj = sizes(parts[j])
            if aj > bi or bj > ai:
                return False
    for p in parts:
        if p[0] == 'core':
            if not (K0(p[1]) <= p[3] <= p[2] * K0(p[1]) and K0(p[1]) <= p[4] <= p[2] * K0(p[1])):
                return False
        elif not tree_ok(p[2], p[3], p[1]):
            return False
    return True
def degree_ok(parts, d):
    r = len(parts)
    return all(part_deg(p) + r - 1 <= d for p in parts)

def optimise(T1, T2, d):
    """best (K1 + K2, K1, K2, parts) with K1 <= T1, K2 <= T2, max degree <= d"""
    best = (0, 0, 0, None)
    for r in range(1, RMAX + 1):
        cap = d - (r - 1)
        if cap < 2: break
        types = core_types(cap)
        types.sort(key=lambda t: (-K0(t[0]), -t[1]))
        for with_tree in (False, True):
            ncores = r - 1 if with_tree else r
            if ncores < 0: continue
            # multisets of ncores types; prune: lo sum must be <= min(T1, T2)
            lo_min = min(K0(s) for (s, c) in types) if types else 0
            suf = [0] * (len(types) + 1)
            for i in range(len(types) - 1, -1, -1):
                suf[i] = max(suf[i + 1], types[i][1] * K0(types[i][0]))
            def rec(start, chosen, losum, hisum):
                nonlocal best
                if len(chosen) == ncores:
                    if hisum + (kappa_cover(cap) if with_tree else 0) < best[0] / 2 - 1:
                        return
                    a = assign(list(chosen), cap if with_tree else None, T1, T2)
                    if a and degree_ok(a[3], d) and a[0] > best[0]:
                        best = a
                    return
                left = ncores - len(chosen)
                for i in range(start, len(types)):
                    s, c = types[i]
                    l = K0(s)
                    if losum + l + (left - 1) * lo_min > min(T1, T2):
                        continue
                    # upper bound: every remaining part has hi <= suf[i]
                    if 2 * (hisum + suf[i] * left + (kappa_cover(cap) if with_tree else 0)) < best[0]:
                        break
                    rec(i, chosen + [types[i]], losum + l, hisum + c * l)
            rec(0, [], 0, 0)
            if best[1] == T1 and best[2] == T2:
                return best
    return best

if __name__ == '__main__':
    QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    out = open('hubopt.out', 'w')
    def say(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); out.write(s + '\n'); out.flush()
    say('Lemma 4.2 sums, optimised: for each (q, k) the largest K_B'' + K_A'' <= slots (m = q^2+1) with a certificate')
    for k in range(2, KMAX + 1):
        full = []
        for q in PP:
            if q > QMAX: break
            d = q - k
            if d < 2: continue
            T1, T2 = slots(q, k)
            tot, K1, K2, parts = optimise(T1, T2, d)
            if parts is None:
                say('k=%d q=%d: none' % (k, q)); continue
            tag = 'FULL' if (K1, K2) == (T1, T2) else 'partial'
            def desc(p):
                if p[0] == 'core':
                    return 'H(%d)x%d[%d,%d]' % (p[1], p[2], p[3], p[4])
                s, cP, cL, gP, gL = tree_ok(p[2], p[3], p[1])
                return 'tree(delta=%d)[%d,%d]{PG(2,%d); c_P=%d c_L=%d g_P=%d g_L=%d}' % (p[1], p[2], p[3], s, cP, cL, gP, gL)
            say('k=%d q=%d delta=%d slots=(%d,%d) -> (%d,%d) %s: %s' % (k, q, d, T1, T2, K1, K2, tag, ' + '.join(desc(p) for p in parts)))
