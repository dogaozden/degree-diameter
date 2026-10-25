#!/usr/bin/env python3
"""Given the 0/1 matrix A of a solution of the 'A only' problem (Theorem Q), decide whether a weighing-matrix signing
W exists. W W^T = (k-2) I holds iff for every alternating square c->e1<-d->e2<-c (c,d non-adjacent, {e1,e2} their
common out-neighbours) s(c,e1)+s(d,e1)+s(c,e2)+s(d,e2) = 1 over GF(2), where s(arc) = 0 for +1 and 1 for -1.
Prints the result; if there is no signing, prints a certificate: a set of squares of odd size in which every arc
occurs an even number of times (summing their equations gives 0 = 1)."""
import sys, itertools
import numpy as np

def squares(A):
    m = len(A)
    out = [set(np.nonzero(A[c])[0]) for c in range(m)]
    sq = []
    for c, d in itertools.combinations(range(m), 2):
        if A[c, d] or A[d, c]: continue
        co = sorted(out[c] & out[d])
        assert len(co) == 2, (c, d, co)
        e1, e2 = co
        sq.append(((c, e1), (d, e1), (c, e2), (d, e2)))
    return sq

def solve(A):
    sq = squares(A)
    arcs = sorted({a for s in sq for a in s})
    idx = {a: i for i, a in enumerate(arcs)}
    n = len(arcs)
    # rows as python ints: bits 0..n-1 arc coefficients, bit n = rhs; track combination of original rows
    rows = []
    for i, s in enumerate(sq):
        v = 0
        for a in s: v ^= 1 << idx[a]
        rows.append([v | (1 << n), 1 << i])
    piv = {}
    for r in rows:
        v, h = r
        for col in sorted(piv, reverse=True):
            pass
        # reduce
        while True:
            low = v & ((1 << n) - 1)
            if low == 0: break
            col = low.bit_length() - 1
            if col in piv:
                pv, ph = piv[col]; v ^= pv; h ^= ph
            else:
                piv[col] = (v, h); break
        if v & ((1 << n) - 1) == 0 and v >> n & 1:
            return False, [i for i in range(len(sq)) if h >> i & 1], sq
    return True, None, sq

if __name__ == '__main__':
    A = np.load(sys.argv[1])
    ok, cert, sq = solve(A)
    print('squares', len(sq), 'signing exists' if ok else 'NO signing')
    if not ok:
        print('certificate: %d squares' % len(cert))
        cnt = {}
        for i in cert:
            for a in sq[i]: cnt[a] = cnt.get(a, 0) + 1
        assert all(v % 2 == 0 for v in cnt.values()) and len(cert) % 2 == 1
        print('arcs involved', len(cnt), 'check ok')
