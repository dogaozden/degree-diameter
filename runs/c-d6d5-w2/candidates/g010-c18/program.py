import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction family: voltage lifts over an ARBITRARY finite group G given by
# its multiplication table (not only Z_m x|_r Z_k). The base graph has K A-blocks
# and K B-blocks, with DEG layers. Layer l is a permutation p_l of the K blocks,
# so every block vertex gets exactly DEG neighbours. Dart (i, p_l(i), s) joins
# A_{i,g} to B_{p_l(i), g*s} for all g. Left multiplication is an automorphism,
# so diameter <= D iff a BFS of depth D from each of the 2K block identities
# covers every vertex. Python picks the group and K; C anneals the voltages.
#
# Group input: stdin is "G G*G" followed by G*G pairs "x*G+y  x*y" (identity 0).
# C checks that 0 is the identity before searching.
#
# Candidate choice: every valid lift must have n = 2*K*G, so the candidates are
# the orders just above the current best, ascending, with a random group of
# each order. Time is shared among candidates and a candidate that succeeds
# stops its run early.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 30000
#define MAXK 8

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static double TS = 1.0;

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

static int DEG, DIAM, K, G, N, T;
static int *mt;
static int *dI, *dJ, *dS, *bJ, *bS;
static int *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;

static int read_group(void) {
    int g, m;
    if (scanf("%d %d", &g, &m) != 2) return 0;
    if (g < 1 || m != g * g) return 0;
    mt = malloc(sizeof(int) * (size_t)m);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= m || v < 0 || v >= g) return 0;
        mt[u] = v;
    }
    G = g;
    return 1;
}

static int identity_ok(void) {
    for (int y = 0; y < G; y++)
        if (mt[y] != y || mt[y * G] != y) return 0;
    return 1;
}

/* Returns the total number of uncovered (source, target) pairs over the 2K block identities.
   Returns BIGC if two darts coincide (that would create a repeated edge). */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G, s = dS[t];
        for (int g = 0; g < G; g++) {
            int a = ai + g;
            int b = bj + mt[g * G + s];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = r * G;
        stamp[r * G] = curstamp;
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
        total += N - count;
    }
    return total;
}

static void random_init(void) {
    int p[MAXK];
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) dJ[l * K + i] = p[i];
    }
    for (int t = 0; t < T; t++) dS[t] = rnd_int(G);
}

/* Annealing from the current state (cost cur, already evaluated). Best state goes to bJ/bS. */
static long long run_sa(int iters, long long cur) {
    long long bestc = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = TS * (1.0 - frac) + 0.02;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            long long c2 = eval_cost();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                dS[t] = olds;
            }
        }
        if (cur < bestc) {
            bestc = cur;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void emit(const int *J, const int *S) {
    printf("%d %d\n", N, T * G);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", dI[t] * G + g, (K + J[t]) * G + mt[g * G + S[t]]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit K  (group table on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    if (DEG < 1 || DIAM < 1 || K < 1 || K > MAXK || !read_group() || G < 2 || !identity_ok()) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    adj = malloc(sizeof(int) * (size_t)N * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        random_init();
        long long c = eval_cost();
        TS = (c > 0 && c < BIGC) ? 0.02 * (double)c : 1.0;
        if (TS < 1.0) TS = 1.0;
        long long bc = run_sa(ITERS, c);
        if (bc == 0) {
            emit(bJ, bS);
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (fallbacks, always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Group and candidate helpers.
# ----------------------------------------------------------------------------

MAX_G = 600  # keeps the Python multiplication table and the C input small


def _group_options(G):
    """All semidirect products Z_m x|_r Z_k with m*k = G, m >= 2, as (m, k, r) triples."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _group_table(m, k, r):
    """Return (order, pairs) where pairs are (x*order + y, x*y) for the group from lib.semidirect_group."""
    order, mul, _ = lib.semidirect_group(m, k, r)
    pairs = [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]
    return order, pairs


def _candidates(best_n):
    """Orders n = 2*K*G just above best_n, ascending, with K in 1..4."""
    cands = []
    for K in (1, 2, 3, 4):
        gmin = best_n // (2 * K) + 1
        for G in range(gmin, gmin + 5):
            if 2 <= G <= MAX_G:
                cands.append((2 * K * G, K, G))
    cands.sort()
    return cands[:12]


# ----------------------------------------------------------------------------
# Driver.
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

    if D >= 3:
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if best_n >= lib.moore_bound(d, D):
        return best

    rng = random.Random(seed * 7919 + 13)
    cands = _candidates(best_n)
    for idx in range(len(cands)):
        _, K, G = cands[idx]
        left = 0.85 * time_limit - 1.5 - (time.monotonic() - start)
        if left < 1.0:
            break
        slice_ = max(1.0, left / (len(cands) - idx))
        opts = _group_options(G)
        if not opts:
            continue
        nontriv = [o for o in opts if o[2] != 1]
        pool = nontriv if (nontriv and rng.random() < 0.7) else opts
        m, k, r = rng.choice(pool)
        try:
            order, pairs = _group_table(m, k, r)
        except Exception:
            continue
        if order != G:
            continue
        hard = min(slice_ + 2.0, time_limit - (time.monotonic() - start) - 1.5)
        if hard < 1.0:
            break
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{slice_:.2f}", K],
                            stdin_graph=(order, pairs), timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
