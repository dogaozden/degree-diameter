#!/usr/bin/env python3
"""The cells (Delta, 7), Delta = 14..26, under Theorem 3.1 / Corollary 3.2 (D7_THEOREMS.md Section 5).

For every Delta and every prime power q >= 4 with k = Delta - q - 1 >= 1: F_k(q) (m = q^2+1) and the status of the hub
graph at the full slots: 'proof' (k = 1: D7_HEXAGON Corollary 9.1, q >= 5; k >= 2: Theorem 4.4, q >= q_k, from
hubsum.out), 'computer' (a hub graph checked by hgcheck: hgrun.out, or the lab's graphs, hgcheck_lab.out, at the same
sizes), else 'open'.  Also the 2013-table value max over (q, k) of 2(2k+1)N(q) for comparison.  Output: table.out"""
import re
from hubcap_lib import slots, PP as _PP

def N(q): return (q + 1) * (q ** 4 + q ** 2 + 1)
PP = [q for q in _PP if q < 64]
unc = {}
for line in open('hubsum.out'):
    mm = re.match(r'k=(\d+): NOT covered: \[(.*)\]', line)
    if mm:
        unc[int(mm.group(1))] = [int(x) for x in mm.group(2).split(',') if x.strip()]
comp = set()
for line in open('hgrun.out'):
    mm = re.match(r'q=(\d+) k=(\d+) .*RESULT VALID HG\((\d+),(\d+);', line)
    if mm:
        q, k, a, b = map(int, mm.groups())
        if (a, b) == slots(q, k):
            comp.add((q, k))
for line in open('hgcheck_lab.out'):
    mm = re.search(r'RESULT VALID HG\((\d+),(\d+);(\d+)\)', line)
    if mm:
        a, b, d = map(int, mm.groups())
        for q in PP:
            k = q - d
            if k >= 1 and slots(q, k) == (a, b):
                comp.add((q, k))

def status(q, k):
    if k == 1:
        return 'proof' if q >= 5 else 'open'
    if q not in unc.get(k, []) and q - k >= 2:
        return 'proof'
    return 'computer' if (q, k) in comp else 'open'

def F(q, k):
    KB, KA = slots(q, k)
    return 2 * (2 * k + 1) * N(q) + KA + KB

out = open('table.out', 'w')
def say(s):
    print(s); out.write(s + '\n')
say('| cell | 2013-type value $\\max 2(2k+1)N$ | best $(q,k)$ | $F_k(q)$ | hub graph | other $(q,k)$ |')
say('|---|---:|---|---:|---|---|')
for D in range(14, 27):
    cands = [(q, D - q - 1) for q in PP if q >= 4 and D - q - 1 >= 1 and D - q - 1 <= q - 1]
    base = max(2 * (2 * k + 1) * N(q) for (q, k) in cands)
    rows = sorted(((F(q, k), q, k, status(q, k)) for (q, k) in cands), reverse=True)
    best = rows[0]
    others = '; '.join('$(%d,%d)$: %s (%s)' % (q, k, format(f, ','), st) for (f, q, k, st) in rows[1:3])
    say('| (%d,7) | %s | $(%d,%d)$ | %s | %s | %s |' % (D, format(base, ','), best[1], best[2], format(best[0], ','),
                                                    best[3], others))

# the largest equal-sided hub graph that Lemmas 4.1-4.3 give below the slots (search of hubsum.py), for the cells
# whose full slots are not proved: the best value of Theorem 3.1 with proofs only
import signal
from hubsum import search
def _alarm(*a): raise TimeoutError
def maxprov(q, k):
    KB, KA = slots(q, k); d = q - k
    lo, hi = 7, min(KB, KA)        # binary search on K (not monotone in general; the result is a found certificate)
    best = None
    while lo <= hi:
        mid = (lo + hi) // 2
        signal.signal(signal.SIGALRM, _alarm); signal.alarm(20)
        try:
            sol = search(mid, mid, d)
        except TimeoutError:
            sol = None
        signal.alarm(0)
        if sol:
            best = (mid, sol); lo = mid + 1
        else:
            hi = mid - 1
    return best
say('\nbest value of Theorem 3.1 with a proved hub graph (equal sides), where the full slots are not proved:')
for D in range(14, 27):
    cands = [(q, D - q - 1) for q in PP if q >= 5 and 2 <= D - q - 1 <= q - 2]
    res = []
    for (q, k) in cands:
        if status(q, k) == 'proof':
            res.append((F(q, k), q, k, 'full slots'))
            continue
        b = maxprov(q, k)
        if b:
            K, sol = b
            res.append((2 * (2 * k + 1) * N(q) + 2 * K, q, k, 'K=%d: %s' % (K, ' + '.join(
                'H(%d)x%d' % (p[1], p[2]) if p[0] == 'core' else 'tree' for p in sol))))
    res.sort(reverse=True)
    if res:
        f, q, k, how = res[0]
        say('(%d,7): (q,k)=(%d,%d) %s  [%s]' % (D, q, k, format(f, ','), how))
