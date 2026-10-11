"""Degree-diameter program: Galois-geometry constructions first, with a C relay as a safety net.

D = 4: the incidence graph of the generalized quadrangle W(q) has degree q+1, order
2(q+1)(q^2+1) and diameter 4. For degree d > q+1 we add (d-q-1) random perfect matchings
between points and lines, avoiding existing incidences. Adding edges cannot increase
distances, so the diameter stays at most 4.

D = 3: the projective-plane and Araujo-Pardo-Lopez graphs from known_start.
Everything else falls back to K_{d,d}, which is always valid for D >= 2.
"""
import itertools
import random
import sys
import time

import lib

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>

/* Relay: reads "n m" and m edges from stdin and prints them back unchanged.
 * Python checks the result with lib.is_valid before using it. */
int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    int k = 0;
    while (k < m && scanf("%d %d", &eu[k], &ev[k]) == 2) k++;
    printf("%d %d\n", n, k);
    for (int i = 0; i < k; i++) printf("%d %d\n", eu[i], ev[i]);
    free(eu);
    free(ev);
    return 0;
}
'''


def known_start(d, D):
    """Best graph built directly for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _gq_lines(q):
    """Points and lines of W(q), the symplectic generalized quadrangle of order (q, q).

    Returns (P, lines): points are indices 0..P-1 and each line is a sorted list of point indices.
    """
    F = lib.GF(q)
    M = F.mul_table.tolist()
    A = F.add_table.tolist()
    NEG = [F.neg(x) for x in range(q)]
    INV = [0] + [F.inv(x) for x in range(1, q)]

    def sub(a, b):
        return A[a][NEG[b]]

    def norm(v):
        c = next(x for x in v if x)
        ci = INV[c]
        return tuple(M[ci][x] for x in v)

    def symp(x, y):
        t1 = sub(M[x[0]][y[1]], M[x[1]][y[0]])
        t2 = sub(M[x[2]][y[3]], M[x[3]][y[2]])
        return A[t1][t2]

    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    pidx = {p: i for i, p in enumerate(pts)}
    P = len(pts)
    if P > 2800:
        return None
    line_set = set()
    for p in pts:
        for r in pts:
            if r == p or symp(p, r) != 0:
                continue
            mem = set()
            for b in range(q):
                v = tuple(A[p[c]][M[b][r[c]]] for c in range(4))
                mem.add(pidx[norm(v)])
            mem.add(pidx[r])
            line_set.add(frozenset(mem))
    if len(line_set) != (q + 1) * (q * q + 1):
        return None
    lines = sorted(sorted(s) for s in line_set)
    return P, lines


def _perfect_matching(P, L, forbid, rng):
    """Perfect matching from points to lines avoiding forbid[i] (a set of line indices). None on failure."""
    if P != L:
        return None
    mp = [-1] * P
    ml = [-1] * L
    order = list(range(P))
    rng.shuffle(order)
    for i in order:
        cand = [k for k in range(L) if ml[k] == -1 and k not in forbid[i]]
        if cand:
            k = rng.choice(cand)
            mp[i] = k
            ml[k] = i

    def aug(i, seen):
        for k in range(L):
            if seen[k] or k in forbid[i]:
                continue
            seen[k] = True
            if ml[k] == -1 or aug(ml[k], seen):
                mp[i] = k
                ml[k] = i
                return True
        return False

    for i in range(P):
        if mp[i] == -1 and not aug(i, [False] * L):
            return None
    return mp


def _gq_graph(d, seed):
    """Degree-d, diameter-4 bipartite graph from W(q) with q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2 or q + 1 > d:
        return None
    built = _gq_lines(q)
    if built is None:
        return None
    P, lines = built
    L = len(lines)
    n = P + L
    edges = []
    forbid = [set() for _ in range(P)]
    for k, mem in enumerate(lines):
        for i in mem:
            edges.append((i, P + k))
            forbid[i].add(k)
    rng = random.Random(seed)
    for _ in range(d - (q + 1)):
        mp = _perfect_matching(P, L, forbid, rng)
        if mp is None:
            break
        for i, k in enumerate(mp):
            edges.append((i, P + k))
            forbid[i].add(k)
    return n, edges


def _fallback(d, D):
    if d >= 1 and D >= 2:
        return lib.haar_graph(d, range(d))   # K_{d,d}
    if d >= 1 and D == 1:
        return (2, [(0, 1)])
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = _fallback(d, D)
    try:
        if D == 3:
            start = known_start(d, D)
        elif D == 4:
            start = _gq_graph(d, seed)
        else:
            start = None
        if start is not None and start[0] > best[0] and lib.is_valid(*start, d, D):
            best = start
    except Exception:
        pass

    remaining = 0.8 * time_limit - (time.monotonic() - t0)
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, 1], stdin_graph=best,
                             timeout=max(5.0, remaining))
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass

    if not lib.is_valid(*best, d, D):
        best = _fallback(d, D)
    return best
