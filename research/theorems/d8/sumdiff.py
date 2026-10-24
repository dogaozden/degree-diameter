"""Largest M for the 'n+2 cover' with j constant-voltage matchings.

Theorem (guaranteed walks): B bipartite, diameter <= n (n even), equal colour classes; j perfect matchings s_1..s_j
(colour class 0 -> 1); Z_M-lift with voltage 0 on B and t_k on s_k.  If
    S(T) = {0} u {+-t_k} u {t_k - t_l : k != l} u {t_k + t_l : k <= l}  =  Z_M
then the lift has diameter <= n + 2 (for any matchings).  This script finds max M per j and all optimal T (up to
multipliers coprime to M)."""
import itertools
import math
import sys

def S(T, M):
    s = {0}
    for t in T:
        s.add(t % M); s.add(-t % M)
    for a in T:
        for b in T:
            if a != b:
                s.add((a - b) % M)
            s.add((a + b) % M)
    return s

out = []
for j in range(1, 6):
    bound = 1 + 2 * j + j * (j - 1) + j * (j + 1) // 2
    best = None
    for M in range(bound, 0, -1):
        sols = []
        for T in itertools.combinations(range(1, M), j):
            if len(S(T, M)) == M:
                sols.append(T)
        if sols:
            # canonical up to units
            canon = set()
            for T in sols:
                forms = []
                for u in range(1, M):
                    if math.gcd(u, M) == 1:
                        forms.append(tuple(sorted((u * t) % M for t in T)))
                canon.add(min(forms))
            best = (M, sorted(canon))
            break
    line = f'j={j}: counting bound {bound}, max M = {best[0]}, T (up to units) = {best[1][:6]}'
    print(line, flush=True)
