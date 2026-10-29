#!/usr/bin/env python3
"""The cells (Delta, 7), Delta = 14..26 (D7_THEOREMS.md Section 5.2).

For every Delta and prime power q with k = Delta - q - 1 in [1, q-1]: F_k(q) (Corollary 3.2, m = q^2+1) and the status
of its hub graph at the full slots: 'proof' (k = 1: D7_HEXAGON Corollary 9.1, q >= 5; k >= 2: a certificate of
hubopt.py), 'computer' (a hub graph checked by hgcheck at exactly these sizes: hgrun.out, hgcheck_lab.out), else 'open'.
The proved value: the largest K_B' + K_A' <= slots found by hubopt.optimise (a certificate of Lemma 4.2), plugged into
Theorem 3.1.  Output: table.md (the table of Section 5.2) and table.out (with the certificates)."""
import re
from hubcap_lib import slots, PP as _PP
from hubopt import optimise

def N(q): return (q + 1) * (q ** 4 + q ** 2 + 1)
PP = [q for q in _PP if q < 64]
comp = set()
for fn in ('hgrun.out', 'hgcheck_lab.out'):
    for line in open(fn):
        mm = re.search(r'RESULT VALID HG\((\d+),(\d+);(\d+)\)', line)
        if mm:
            a, b, d = map(int, mm.groups())
            for q in PP:
                k = q - d
                if k >= 1 and slots(q, k) == (a, b):
                    comp.add((q, k))

def fmt_parts(parts):
    return ' + '.join(('H(%d)x%d' % (p[1], p[2]) if p[2] > 1 else 'H(%d)' % p[1]) if p[0] == 'core'
                      else 'tree(%d)' % p[1] for p in parts)

def F(q, k):
    KB, KA = slots(q, k)
    return 2 * (2 * k + 1) * N(q) + KA + KB

def proved(q, k):
    """(value, K1, K2, parts) of Theorem 3.1 with the hub graph found by hubopt"""
    KB, KA = slots(q, k)
    if k == 1:
        return (F(q, k), KB, KA, 'Lemma 7.1') if q >= 5 else None
    tot, K1, K2, parts = optimise(KB, KA, q - k)
    if parts is None:
        return None
    return (2 * (2 * k + 1) * N(q) + K1 + K2, K1, K2, fmt_parts(parts))

out = open('table.out', 'w')
md = ['| cell | level graphs | $(q,k)$ | $F_k(q)$ | hub graph at full slots | proved | at $(q,k)$: hubs | hub graph of the proved value |',
      '|------|---------:|-----|----------:|--------|----------:|------------|----------------|']
for D in range(14, 27):
    cands = [(q, D - q - 1) for q in PP if q >= 4 and 1 <= D - q - 1 <= q - 1]
    base = max(2 * (2 * k + 1) * N(q) for (q, k) in cands)
    rows = []
    for (q, k) in cands:
        p = proved(q, k)
        full = p is not None and (p[1], p[2]) == slots(q, k)
        st = 'proof' if full else ('computer' if (q, k) in comp else 'open')
        rows.append((F(q, k), q, k, st, p))
        out.write('(%d,7) q=%d k=%d F=%d status=%s proved=%s\n' % (D, q, k, F(q, k), st, p))
    best = max(rows, key=lambda r: r[0])
    pv = max((r for r in rows if r[4]), key=lambda r: r[4][0])
    p = pv[4]
    md.append('| (%d,7) | %s | $(%d,%d)$ | %s | %s | %s | $(%d,%d)$: %s + %s | %s |' % (
        D, format(base, ','), best[1], best[2], format(best[0], ','), best[3], format(p[0], ','), pv[1], pv[2],
        format(p[1], ','), format(p[2], ','), p[3]))
open('table.md', 'w').write('\n'.join(md) + '\n')
print('\n'.join(md))
