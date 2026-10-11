import itertools
import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an ARBITRARY finite group, given as a
# multiplication table on stdin. Vertices: A_i,g = i*G + g, B_j,h = (K+j)*G + h.
# Dart t = (i, j, s) joins A_i,g to B_j,(g*s) for every g. Each layer is a
# permutation of the K base B-vertices, so every vertex has degree DEG.
#
# Left multiplication is an automorphism, so diameter <= D iff a BFS of depth D
# from each of the 2K block representatives (element 0 of each block) covers
# every vertex. Only associativity and cancellation are needed, so the engine
# works for any group. Heisenberg groups, direct products, and semidirect
# products all go through the same code.
#
# Search: simulated annealing on the weighted cost (breakout weights per block),
# with an elite pool used for iterated local search, as in the parent.
#
# Input on stdin: "G G*G" then G*G pairs "x*G+y  x*y" (the table, row-major).
# Arguments: d D seed time K start_n.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define POOLMAX 48
#define POOLP 0.6
#define BRK 150
#define MAXK 4

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

static int DEG, DIAM, K, G, T, N;
static int *mt;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;

typedef struct { long long cost; int *J, *S; } Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = mt[(size_t)g * G + s];
}

static void reset_weights(void) {
    for (int r = 0; r < 2 * K; r++) wt[r] = 1;
    wsum_w = 2 * K;
}

/* Returns the true cost (uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
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
    }
    long long total = 0, w = 0;
    for (int r = 0; r < 2 * K; r++) {
        total += unc[r];
        w += wt[r] * unc[r];
    }
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Random kicks: target swaps inside a layer, or voltage changes. */
static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

/* Annealing on the weighted cost with breakout weight bumps.
   The caller must have just called eval_cost() on the start state.
   The best state (by true cost) goes to bestJ/bestS. Returns the best true cost. */
static long long run_sa(int iters, double tscale, long long cost) {
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
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
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

static void emit(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = m;
    best_n = N;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the best. */
static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (N > best_n) emit();
    }
}

static void pool_add(long long cost, const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    pool[slot].cost = cost;
    memcpy(pool[slot].J, J, sizeof(int) * (size_t)T);
    memcpy(pool[slot].S, S, sizeof(int) * (size_t)T);
}

/* Best of three random pool entries (the group is fixed, so all are eligible). */
static int pick_pool(void) {
    if (npool == 0) return -1;
    int bi = rnd_int(npool);
    for (int s = 0; s < 2; s++) {
        int c = rnd_int(npool);
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    timespec_get(&T0, TIME_UTC);
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time K [start_n] < table\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    int start_n = argc > 6 ? atoi(argv[6]) : 0;
    best_n = start_n;
    best_m = 0;

    int gn = 0, gm = 0;
    if (scanf("%d %d", &gn, &gm) != 2 || gn < 1 || gn > 2000 || gm != gn * gn) {
        printf("0 0\n");
        return 0;
    }
    G = gn;
    mt = malloc(sizeof(int) * (size_t)gm);
    for (int k = 0; k < gm; k++) {
        int i = 0, v = 0;
        if (scanf("%d %d", &i, &v) != 2 || i < 0 || i >= gm || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        mt[i] = v;
    }
    if (DEG < 1 || DIAM < 1 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * K * G;
    T = DEG * K;
    if (N <= best_n) {
        printf("0 0\n");
        return 0;
    }

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
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)T);
        pool[i].S = malloc(sizeof(int) * (size_t)T);
        pool[i].cost = BIGC;
    }
    reset_weights();

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            memcpy(dJ, pool[pi].J, sizeof(int) * (size_t)T);
            memcpy(dS, pool[pi].S, sizeof(int) * (size_t)T);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            reset_weights();
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
        } else {
            random_init();
            reset_weights();
            long long cst = eval_cost();
            long long bc = run_sa(ITERS, 1.0, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
        }
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Groups as (order, mul) with elements 0..order-1.
# ----------------------------------------------------------------------------

GMAX = 800   # table size limit: GMAX^2 pairs go through stdin
NRUN = 5     # number of groups given a C search slice


def _heis(n):
    """Heisenberg group mod n: triples (a, b, c), product (a+a', b+b', c+c'+a*b'). Order n^3."""
    nn = n * n

    def mul(x, y):
        a, r = divmod(x, nn)
        b, c = divmod(r, n)
        a2, r2 = divmod(y, nn)
        b2, c2 = divmod(r2, n)
        return ((a + a2) % n) * nn + ((b + b2) % n) * n + (c + c2 + a * b2) % n

    return n ** 3, mul


def _direct(g, h):
    """Direct product of two groups given as (order, mul)."""
    n1, m1 = g
    n2, m2 = h

    def mul(x, y):
        x1, x2 = divmod(x, n2)
        y1, y2 = divmod(y, n2)
        return m1(x1, y1) * n2 + m2(x2, y2)

    return n1 * n2, mul


def _cyclic(m):
    return m, (lambda x, y: (x + y) % m)


def _semi(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    return order, mul


def _candidates(lo, hi):
    """Groups with order in [lo, hi] as (label, order, (order, mul))."""
    out = []
    for n in range(2, 10):
        if lo <= n ** 3 <= hi:
            out.append(("heis", n ** 3, _heis(n)))
    for n in (2, 3, 4, 5):
        h = _heis(n)
        for j in range(2, hi // h[0] + 1):
            order = h[0] * j
            if lo <= order <= hi:
                out.append(("heisZ", order, _direct(h, _cyclic(j))))
    for k in range(2, 7):
        for m in range(max(3, lo // k), hi // k + 2):
            order = m * k
            if order < lo or order > hi:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            picks = [rs[0], rs[-1]] if len(rs) > 1 else rs
            for r in picks:
                out.append(("semi", order, _semi(m, k, r)))
    return out


def _plans(best_n, moore):
    """Candidate (2KG, K, label, G, mul) with 2KG > best_n and 2KG <= moore, closest above best first."""
    plans = []
    for K in (1, 2, 3):
        lo = best_n // (2 * K) + 1
        hi = min(GMAX, moore // (2 * K), lo + max(12, lo // 6))
        if lo < 2 or hi < lo:
            continue
        for label, order, mul in _candidates(lo, hi):
            plans.append((2 * K * order, K, label, order, mul))
    plans.sort(key=lambda p: (p[0], p[1]))
    return plans


def _pick(plans, k):
    """Round-robin over group families so the slices try different constructions."""
    buckets = {}
    for p in plans:
        buckets.setdefault(p[2], []).append(p)
    keys = list(buckets)
    chosen = []
    while len(chosen) < k and any(buckets.values()):
        for key in keys:
            if buckets[key] and len(chosen) < k:
                chosen.append(buckets[key].pop(0))
    return chosen


def _table(order, mul):
    """Multiplication table as (index, value) pairs, index = x*order + y."""
    return [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end_time = start + 0.94 * time_limit - 1.5
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    chosen = _pick(_plans(best_n, moore), NRUN)
    for idx, (n_tot, K, label, order, mul) in enumerate(chosen):
        if n_tot <= best_n:
            continue
        table = _table(order, mul)
        left = end_time - time.monotonic()
        runs_left = len(chosen) - idx
        budget = left / runs_left
        if budget < 1.5:
            break
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", K, best_n],
                            stdin_graph=(order, table), timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
