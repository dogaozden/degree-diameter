import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: the main search is now a C simulated annealer over bi-Cayley
# voltage lifts, not a Python loop. Base sizes K = 1, 2, 3 give orders 2KG,
# and each group is cyclic or Z_M x| Z_KK (given by r). The C engine counts
# unreached pairs from one representative per base block (valid by left
# translation), and it returns only a graph with zero cost.
#
# Python keeps two safe fallbacks: K_{d,d} (diameter 2) and the
# arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* usage: prog d D seed budget K M KK R
   Lift with base K per side, group Z_M x| Z_KK (element a*KK+b, r^KK = 1 mod M).
   Layer L is a permutation p_L of the K base vertices; dart (i, p_L(i), s)
   joins A_{i,g} to B_{p_L(i), g*s} for all g. Output "n m" + edges, or "0 0". */

static int dg, Dd, K, M, KK, G, N, NDART;
static int *mulT, *dI, *dJ, *dS, *adj, *fillc, *stamp, *qbuf;
static int curStamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double runif(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int rint_n(int n) {
    return (int)(rnext() % (uint64_t)n);
}

/* Returns the number of (representative, vertex) pairs at distance > D,
   plus a penalty of 1e6 for each pair of duplicate darts. Zero = valid. */
static long long cost_eval(void) {
    long long pen = 0;
    int nd = NDART;
    int x, y, v, g, k, r, lvl, i, j, s;
    for (x = 0; x < nd; x++) {
        for (y = x + 1; y < nd; y++) {
            if (dI[x] == dI[y] && dJ[x] == dJ[y] && dS[x] == dS[y]) pen += 1000000LL;
        }
    }
    for (v = 0; v < N; v++) fillc[v] = 0;
    for (x = 0; x < nd; x++) {
        i = dI[x];
        j = dJ[x];
        s = dS[x];
        for (g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + mulT[g * G + s];
            if (fillc[a] >= dg || fillc[b] >= dg) return (1LL << 50);
            adj[a * dg + fillc[a]++] = b;
            adj[b * dg + fillc[b]++] = a;
        }
    }
    long long total = pen;
    int reps[8];
    int nr = 0;
    for (i = 0; i < K; i++) reps[nr++] = i * G;
    for (j = 0; j < K; j++) reps[nr++] = (K + j) * G;
    for (r = 0; r < nr; r++) {
        curStamp++;
        int head = 0, tail = 0;
        int src = reps[r];
        stamp[src] = curStamp;
        qbuf[tail++] = src;
        for (lvl = 0; lvl < Dd && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qbuf[head++];
                const int *au = adj + (size_t)u * dg;
                for (k = 0; k < dg; k++) {
                    int w = au[k];
                    if (stamp[w] != curStamp) {
                        stamp[w] = curStamp;
                        qbuf[tail++] = w;
                    }
                }
            }
        }
        total += (long long)(N - tail);
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D seed budget K M KK R\n");
        return 1;
    }
    dg = atoi(argv[1]);
    Dd = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    KK = atoi(argv[7]);
    int R = atoi(argv[8]);

    if (dg < 1 || Dd < 1 || K < 1 || K > 3 || M < 1 || KK < 1 || KK > 64) {
        printf("0 0\n");
        return 0;
    }
    G = M * KK;
    if (G > 3000) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * K * G;
    NDART = dg * K;
    rs = (uint64_t)seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    long long pw[64];
    pw[0] = 1 % M;
    for (int b = 1; b < KK; b++) pw[b] = (pw[b - 1] * (long long)R) % M;

    mulT = (int *)malloc(sizeof(int) * (size_t)G * G);
    dI = (int *)malloc(sizeof(int) * NDART);
    dJ = (int *)malloc(sizeof(int) * NDART);
    dS = (int *)malloc(sizeof(int) * NDART);
    adj = (int *)malloc(sizeof(int) * (size_t)N * dg);
    fillc = (int *)calloc(N, sizeof(int));
    stamp = (int *)calloc(N, sizeof(int));
    qbuf = (int *)malloc(sizeof(int) * N);
    if (!mulT || !dI || !dJ || !dS || !adj || !fillc || !stamp || !qbuf) {
        printf("0 0\n");
        return 0;
    }

    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            int a1 = x / KK, b1 = x % KK, c = y / KK, d2 = y % KK;
            int a = (int)((a1 + pw[b1] * c) % M);
            int b = (b1 + d2) % KK;
            mulT[x * G + y] = a * KK + b;
        }
    }

    /* Random initial darts: each layer is a permutation of the K base vertices. */
    for (int L = 0; L < dg; L++) {
        int perm[3];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int t = rint_n(i + 1);
            int tmp = perm[i];
            perm[i] = perm[t];
            perm[t] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int x = L * K + i;
            dI[x] = i;
            dJ[x] = perm[i];
            dS[x] = rint_n(G);
        }
    }

    long long cur = cost_eval();
    const double T0 = 3.0, T1 = 0.05;
    double T = T0;
    clock_t t0 = clock();
    long long iter = 0;

    while (cur > 0) {
        if ((iter & 63) == 0) {
            double el = (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
            if (el >= budget) break;
            double frac = el / budget;
            T = T0 * pow(T1 / T0, frac);
        }
        iter++;
        if (K >= 2 && runif() < 0.2) {
            int L = rint_n(dg);
            int a = rint_n(K), b = rint_n(K);
            if (a == b) continue;
            int xa = L * K + a, xb = L * K + b;
            int t = dJ[xa];
            dJ[xa] = dJ[xb];
            dJ[xb] = t;
            long long c2 = cost_eval();
            long long delta = c2 - cur;
            if (delta <= 0 || runif() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                t = dJ[xa];
                dJ[xa] = dJ[xb];
                dJ[xb] = t;
            }
        } else {
            int x = rint_n(NDART);
            int old = dS[x];
            int nw = rint_n(G);
            if (nw == old) continue;
            dS[x] = nw;
            long long c2 = cost_eval();
            long long delta = c2 - cur;
            if (delta <= 0 || runif() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                dS[x] = old;
            }
        }
    }

    if (cur == 0) {
        long long m = (long long)NDART * G;
        printf("%d %lld\n", N, m);
        for (int x = 0; x < NDART; x++) {
            int i = dI[x], j = dJ[x], s = dS[x];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + mulT[g * G + s];
                printf("%d %d\n", a, b);
            }
        }
    } else {
        printf("0 0\n");
    }

    free(mulT);
    free(dI);
    free(dJ);
    free(dS);
    free(adj);
    free(fillc);
    free(stamp);
    free(qbuf);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: fallbacks and group choices.
# ----------------------------------------------------------------------------

def _group_options(G, rng):
    """Return (M, KK, R) choices with M*KK = G for the semidirect group Z_M x| Z_KK."""
    opts = [(G, 1, 1)]
    for KK in (2, 3, 4, 5, 6, 8):
        if G % KK:
            continue
        M = G // KK
        if M < 2:
            continue
        rs = [r for r in range(1, M)
              if math.gcd(r, M) == 1 and pow(r, KK, M) == 1 % M]
        if rs:
            opts.append((M, KK, rng.choice(rs)))
    return opts


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Diameter-3 candidates: PG(2,q) plus arc-based extra vertices, for q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for n_c, e_c in _arc_extensions(d, start + 0.15 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Main search: C annealing over bi-Cayley lifts with base K in {1, 2, 3}.
    if D >= 3 and d >= 2:
        ks = [1, 2, 3]
        errors = 0
        it = 0
        while True:
            remaining = end - time.monotonic()
            if remaining < 4.0 or errors >= 2:
                break
            k = ks[it % len(ks)]
            it += 1
            lo = best_n // (2 * k) + 1
            G = max(lo, 2) + rng.randrange(0, 3)
            opts = _group_options(G, rng)
            M, KK, R = opts[rng.randrange(len(opts))]
            budget = min(8.0, remaining - 2.0)
            if budget < 2.0:
                break
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, rng.randrange(1, 2 ** 31), f"{budget:.2f}",
                                 k, M, KK, R],
                                timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
            except (RuntimeError, ValueError):
                errors += 1
                continue
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
