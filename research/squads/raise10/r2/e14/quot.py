#!/usr/bin/env python3
"""quot.py: walk-count DP on the quotient Z_k (j-coordinate). For each side, count sequences (s_1..s_L), L<=D-1 or D,
of alternating words (A->B: +s, B->A: -s in j-coordinate), grouped by resulting j. Shows which j-fibers get few walks."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise10/r2/e14')
from anatlib import parse
def counts(k, jS, D, side):
    # vec over Z_k, number of length-L sequences; side 0 means first step is +.
    v = np.zeros(k, dtype=object); v[0] = 1
    out = {}
    cur = side
    for L in range(1, D + 1):
        w = np.zeros(k, dtype=object)
        sg = 1 if cur == 0 else -1
        for s in jS:
            w = w + np.roll(v, (sg * s) % k)
        v = w; cur = 1 - cur
        out[L] = v.copy()
    return out
if __name__ == '__main__':
    d, D, m, k, r, S = parse(sys.argv[1])
    jS = [s[1] for s in S]
    print(f"Z_{m} x| Z_{k}: j-projection of S = {jS}, D={D}, m={m}")
    for side in (0, 1):
        c = counts(k, jS, D, side)
        # target side: after odd L count lands on the other side; take the parity that reaches the other side within D
        tgt = {}
        for L in range(1, D + 1):
            if (L % 2 == 1) == (side == 0):   # from A (side 0) odd L -> B
                tgt[L] = c[L]
        # total over reached lengths (<= D-1 to be strict, and <= D)
        tot = sum(c[L] for L in tgt if L <= D)
        vals = [int(x) for x in tot]
        order = np.argsort(vals)
        print(f"source side {'A' if side==0 else 'B'}: walk counts over j (lengths<= {D}), min {min(vals)} at j={list(order[:6])} max {max(vals)}")
        print("   j -> count:", {int(j): vals[j] for j in order[:8]})
