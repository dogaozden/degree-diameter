import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an ARBITRARY finite group given as a
# multiplication table (read from stdin), with K A-blocks and K B-blocks.
# Layer l is a perfect matching between A-blocks and B-blocks (permutation dJ),
# and each dart carries a group voltage dS. Vertex A_{i,g} = i*G + g is joined
# to B_{j,g*s} = (K+j)*G + mt[g][s]. Left multiplication is an automorphism,
# so diameter <= D iff BFS of depth D from each of the 2K block representatives
# (g = identity) covers the whole graph. Simulated annealing with breakout
# weights minimises the number of uncovered (representative, vertex) pairs.
# The engine stops at the first zero-cost configuration or at its deadline.
#
# stdin protocol: "G G*G", then G*G lines "x*G+y  x*y" (identity must be 0).
# argv: DEG DIAM seed deadline_seconds K
# stdout: "n m" and edges, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 20000
#define BRK 200
#define MAXG 1300

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, K, G, T;
static int *mt;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx, *bestJ, *bestS;
static long long *wt, *unc;
static long long wsum_w = 0;
static long long last_w = 0;
static int curstamp = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = mt[g * G + s];
}

static void alloc_all(void) {
    int N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int r = 0; r < 2 * K; r++) { wt[r] = 1; unc[r] = 0; }
    wsum_w = 2 * K;
    curstamp = 0;
}

/* Returns the true cost: total uncovered (representative, vertex) pairs.
   Sets unc[] per representative and last_w to the weighted cost. */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = N - count;
        total += unc[r];
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void random_init(void) {
    int *p = malloc(sizeof(int) * (size_t)K);
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    free(p);
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Breakout annealing on the weighted cost. Returns the best true cost; the
   best configuration is stored in bestJ / bestS. */
static long long run_sa(int iters, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed deadline K  (group table on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (DEG < 1 || DIAM < 1 || K < 1 || n < 1 || n > MAXG || m != n * n) {
        printf("0 0\n");
        return 0;
    }
    G = n;
    mt = malloc(sizeof(int) * (size_t)G * G);
    for (int i = 0; i < G * G; i++) mt[i] = -1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= G * G || v < 0 || v >= G) { printf("0 0\n"); return 0; }
        mt[u] = v;
    }
    for (int i = 0; i < G * G; i++) if (mt[i] < 0) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++) if (mt[x] != x) { printf("0 0\n"); return 0; }

    alloc_all();
    int N = 2 * K * G;
    int found = 0;
    while (elapsed() < DEADLINE) {
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, cost);
        if (bc == 0) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            found = 1;
            break;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int M = T * G;
    printf("%d %d\n", N, M);
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Candidate groups: semidirect products Z_m x| Z_k (r^k = 1 mod m), with the
# block count K. Each candidate gives total order n = 2*K*G, ordered ascending
# from a target so the first searches aim just above the record region.
# ----------------------------------------------------------------------------

def _candidates(target, seed):
    rng = random.Random(seed)
    out = []
    for K in (1, 2, 3, 4):
        g0 = max(2, -(-target // (2 * K)))
        for G in range(g0, g0 + 5):
            if G > 1200:
                break
            for k in range(1, 13):
                if G % k or G // k < 2:
                    continue
                m = G // k
                if k == 1:
                    rlist = [1]
                else:
                    rlist = [r for r in range(1, m)
                             if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
                    rng.shuffle(rlist)
                    rlist = rlist[:2]
                for r in rlist:
                    out.append((2 * K * G, K, m, k, r))
    out.sort(key=lambda c: (c[0], rng.random()))
    return out


# ----------------------------------------------------------------------------
# Driver: baselines, then time-sliced group-lift searches in C.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= moore:
        return best

    deadline = start + 0.92 * time_limit - 1.0
    target = max(best_n + 1, int(0.44 * moore) + 1)
    cands = _candidates(target, seed)

    for idx, (n_c, K, m, k, r) in enumerate(cands):
        if n_c <= best_n:
            continue
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        budget = min(9.0, remaining)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
            edges = [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]
            out = lib.run_c(C_SOURCE, [d, D, seed * 1000 + idx, f"{budget:.2f}", K],
                            stdin_graph=(order, edges), timeout=budget + 6.0)
            nn, ee = lib.parse_graph_text(out)
            consider(nn, ee)
        except Exception:
            continue

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
