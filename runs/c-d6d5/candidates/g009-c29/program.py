import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New family: voltage lifts over ARBITRARY finite groups supplied as a
# multiplication table. The table is passed through lib.run_c as a fake graph:
# header "G G*G", then one line per table entry "table[i] 0" (row-major).
# Python builds semidirect products Z_m x| Z_k (including direct products,
# r = 1) with numpy, and chooses a group order G that makes 2*K*G beat the
# current best. Each C job is an annealing search over voltages for a fixed
# base of K A-vertices and K B-vertices (DEG = d layers, each a permutation).
#
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g (left multiplication
# is an automorphism), so diameter <= D iff BFS of depth D from the representative
# of each of the 2K blocks covers everything.
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

static int DEG, DIAM, K, G, ID, T, N;
static int *mt;
static int *dI, *dJ, *dS, *bestJ, *bestS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;
static long long *wt, *unc;
static long long wsum = 0;
static long long last_w = 0;

static inline int gmul(int x, int y) { return mt[x * G + y]; }

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

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
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G + ID;
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
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void alloc_all(void) {
    N = 2 * K * G;
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
    for (int b = 0; b < 2 * K; b++) { wt[b] = 1; unc[b] = 0; }
    wsum = 2 * K;
    curstamp = 0;
}

static void random_init(void) {
    int p[64];
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

static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost, wcur = last_w, prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) *
                      ((double)wsum / (2.0 * K));
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

static void emit_graph(void) {
    int m = T * G;
    printf("%d %d\n", N, m);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", dI[t] * G + g, (K + dJ[t]) * G + perm[(size_t)t * G + g]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D seed time_limit start_n K G ID  (table on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = atoi(argv[5]);
    K = atoi(argv[6]);
    int gin = atoi(argv[7]);
    ID = atoi(argv[8]);
    if (DEG < 1 || DIAM < 1 || K < 1 || K > 32) {
        printf("0 0\n");
        return 0;
    }

    int gg = 0, mm = 0;
    if (scanf("%d %d", &gg, &mm) != 2 || gg < 1 || mm != gg * gg) {
        printf("0 0\n");
        return 0;
    }
    G = gg;
    if (G != gin) { /* stdin table is authoritative */ }
    mt = malloc(sizeof(int) * (size_t)G * G);
    for (int i = 0; i < mm; i++) {
        int u = 0, v = 0;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        mt[i] = u;
    }

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    alloc_all();
    while (elapsed() < DEADLINE) {
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        if (bc == 0) {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(dS, bestS, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            if (2 * K * G > start_n) {
                emit_graph();
                return 0;
            }
            break;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: group tables, job scheduling, validation.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k+b, built with numpy."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    a = idx // k
    b = idx % k
    rpow = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    ra = (a[:, None] + rpow[b][:, None] * a[None, :]) % m
    rb = (b[:, None] + b[None, :]) % k
    return ra * k + rb


def _group_options(G):
    """All (m, k, r) with m*k = G giving Z_m x|_r Z_k (r = 1 is the direct product)."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m == 1:
            opts.append((1, k, 0))
            continue
        if k == 1:
            opts.append((m, 1, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid whenever D >= 2.
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    rng = random.Random(seed * 1000003 + d * 101 + D)
    budget_end = start + 0.85 * time_limit - 2.0
    span = 4
    job_no = 0
    k_choices = [1, 2, 3, 4, 5, 6]

    while True:
        remaining = budget_end - time.monotonic()
        job_t = min(remaining - 1.0, 5.0)
        if job_t < 1.0:
            break

        K = rng.choice(k_choices)
        G_req = best_n // (2 * K) + 1 + rng.randint(0, span)
        if 2 * K * G_req > moore:
            G_req = max(1, moore // (2 * K))
            if 2 * K * G_req <= best_n:
                span = 0
                continue

        opts = _group_options(G_req)
        if not opts:
            span = 0
            continue
        m, k, r = rng.choice(opts)
        tbl = _semidirect_table(m, k, r)
        G = m * k
        edges = [(v, 0) for v in tbl.ravel().tolist()]

        job_no += 1
        n_new, e_new = 0, []
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, seed * 7919 + job_no, f"{job_t:.2f}", best_n, K, G, 0],
                stdin_graph=(G, edges),
                timeout=job_t + 6.0,
            )
            n_new, e_new = lib.parse_graph_text(out)
        except Exception:
            n_new, e_new = 0, []

        if n_new > best_n and lib.is_valid(n_new, e_new, d, D):
            best = (n_new, e_new)
            best_n = n_new
            span = min(max(1, span * 2), 64)
        else:
            span = span // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
