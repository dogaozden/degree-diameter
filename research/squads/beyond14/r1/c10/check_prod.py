#!/usr/bin/env python3
"""Independent diameter check for Haar graphs H(G,S), G = Z_m1 x|_r1 Z_k1  x  Z_m2 x|_r2 Z_k2 (x Z_n with n = 1).
Usage: check_prod.py SOLUTION   (haar_gen3 format: header 'd D prod meta m1 k1 r1 meta m2 k2 r2 n 1 N N', then d lines
'<idx> prod[meta(a=A,j=J);meta(a=A,j=J)] z=0').
Written for c10 (job beyond-d14, round 1). Vertices (g,A), (g,B); (g,A) ~ (s g,B). Right multiplication is a transitive
automorphism on each side, so ecc from (e,A) and (e,B) gives the diameter. Uses only numpy permutation BFS.
Exit 0 iff all vertices reached from both (e,A) and (e,B) within D, and S has d distinct elements."""
import re
import sys
import numpy as np

def read_sol(path):
    lines = open(path).read().strip().splitlines()
    h = lines[0].split()
    d, D = int(h[0]), int(h[1])
    assert h[2] == 'prod' and h[3] == 'meta' and h[7] == 'meta', 'only prod meta x meta supported'
    m1, k1, r1 = int(h[4]), int(h[5]), int(h[6])
    m2, k2, r2 = int(h[8]), int(h[9]), int(h[10])
    S = []
    for ln in lines[1:1 + d]:
        mm = re.search(r'prod\[meta\(a=(\d+),j=(\d+)\);meta\(a=(\d+),j=(\d+)\)\]', ln)
        S.append(tuple(int(x) for x in mm.groups()))
    return d, D, (m1, k1, r1), (m2, k2, r2), S

def left_table(m, k, r, s_a, s_j):
    """permutation g -> s g on G1 = Z_m x|_r Z_k, elements indexed a*k + j."""
    n = m * k
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(n, dtype=np.int64)
    b = idx // k
    l = idx % k
    a_out = (s_a + rp[s_j] * b) % m
    j_out = (s_j + l) % k
    return a_out * k + j_out

def main():
    d, D, G1, G2, S = read_sol(sys.argv[1])
    m1, k1, r1 = G1; m2, k2, r2 = G2
    n1, n2 = m1 * k1, m2 * k2
    N = n1 * n2
    print(f"group prod meta {G1} x meta {G2}, N = {N}, d = {d}, D = {D}")
    assert len(set(S)) == d, 'S not distinct'
    assert S[0] == (0, 0, 0, 0), 'first generator must be e'
    # permutations g -> s g on the product (index g1 * n2 + g2)
    perms = []
    for (a1, j1, a2, j2) in S:
        L1 = left_table(m1, k1, r1, a1, j1)
        L2 = left_table(m2, k2, r2, a2, j2)
        P = (L1[:, None] * n2 + L2[None, :]).ravel()
        perms.append(P)
    # checks: each permutation is a bijection
    for P in perms:
        assert np.array_equal(np.sort(P), np.arange(N)), 'not a permutation'
    invs = []
    for P in perms:
        inv = np.empty(N, dtype=np.int64); inv[P] = np.arange(N); invs.append(inv)

    def ecc_from(side):
        visA = np.zeros(N, bool); visB = np.zeros(N, bool)
        e = 0  # identity index is (0,0),(0,0) -> 0
        if side == 'A':
            visA[e] = True; frontier = np.array([e]); on = 'A'
        else:
            visB[e] = True; frontier = np.array([e]); on = 'B'
        level = 0
        while frontier.size:
            new = []
            if on == 'A':   # A-vertices g -> B-vertices s g
                for P in perms:
                    nb = P[frontier]
                    nb = nb[~visB[nb]]
                    visB[nb] = True
                    new.append(nb)
                on = 'B'
            else:           # B-vertices h -> A-vertices s^-1 h
                for inv in invs:
                    nb = inv[frontier]
                    nb = nb[~visA[nb]]
                    visA[nb] = True
                    new.append(nb)
                on = 'A'
            allnew = np.unique(np.concatenate(new)) if new else np.array([], dtype=np.int64)
            # the new frontier consists of vertices newly marked on the side just reached
            frontier = allnew
            if frontier.size:
                level += 1
        reachedA = int(visA.sum()); reachedB = int(visB.sum())
        return level, reachedA, reachedB

    eA, rA, rB = ecc_from('A')
    print(f"from (e,A): last level {eA}, reached A {rA}/{N}, B {rB}/{N}")
    eB, rA2, rB2 = ecc_from('B')
    print(f"from (e,B): last level {eB}, reached A {rA2}/{N}, B {rB2}/{N}")
    ok = (rA == N and rB == N and rA2 == N and rB2 == N and eA <= D and eB <= D)
    print("DIAMETER", "OK" if ok else "FAIL", f"(max ecc {max(eA, eB)} <= D = {D} ? {max(eA, eB) <= D})")
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
