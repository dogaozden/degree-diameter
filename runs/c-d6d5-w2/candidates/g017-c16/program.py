import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: affine-layer search, a different construction from group lifts.
#
# Vertices: A_{i,x} = i*M + x and B_{j,y} = (K+j)*M + y, for i, j < K and x, y < M.
# There are T = DEG*K darts. Dart t = (i, j, a, b) with i = t % K and layer l = t / K.
# Each layer is a permutation on the K A-blocks, so dart t joins A_{i,x} to
# B_{j,(a*x+b) mod M}. The maps are affine with a a unit mod M. Every A vertex
# gets one edge per dart with its block index, and every B vertex gets one edge
# per layer, so the degree is exactly DEG.
#
# Unlike the group-lift engine, the graph is not assumed vertex-transitive, so
# the cost is computed from ALL vertices at once with bitset balls of radius D:
# cost = (ordered pairs at distance > D) + 100000 * (duplicate neighbour pairs).
# Zero cost means a simple, bipartite, valid graph.
#
# Search: simulated annealing over the affine coefficients and within-layer
# block assignments. Elite configurations are kept in a pool, and later runs
# perturb them and re-anneal at lower temperature.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000000000LL
#define DUPW 100000LL
#define POOLMAX 8
#define RUN_ITERS 12000
#define MAXK 3

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DEG, DIAM, K, M, N, W, T, MAXT;
static int best_n, best_m;
static int *dI, *dJ, *dA, *dB, *bJ, *bA, *bB, *units, *adj, *cnt;
static int nunits;
static uint64_t *bs0 = NULL, *bs1 = NULL;
static int *best_e = NULL;

typedef struct {
    int K, M;
    long long cost;
    int *J, *A, *B;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

static void setup(int k, int m) {
    K = k; M = m;
    N = 2 * K * M;
    W = (N + 63) / 64;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dA = malloc(sizeof(int) * (size_t)T);
    dB = malloc(sizeof(int) * (size_t)T);
    bJ = malloc(sizeof(int) * (size_t)T);
    bA = malloc(sizeof(int) * (size_t)T);
    bB = malloc(sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) dI[t] = t % K;
    units = malloc(sizeof(int) * (size_t)M);
    nunits = 0;
    for (int a = 1; a < M; a++)
        if (gcd_i(a, M) == 1) units[nunits++] = a;
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    bs0 = malloc(sizeof(uint64_t) * (size_t)N * W);
    bs1 = malloc(sizeof(uint64_t) * (size_t)N * W);
}

static void teardown(void) {
    free(dI); free(dJ); free(dA); free(dB);
    free(bJ); free(bA); free(bB);
    free(units); free(adj); free(cnt); free(bs0); free(bs1);
    dI = dJ = dA = dB = bJ = bA = bB = units = adj = cnt = NULL;
    bs0 = bs1 = NULL;
}

/* Cost: ordered unreached pairs + DUPW * duplicate neighbour pairs. Zero iff valid. */
static long long eval_cost(void) {
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * M, bj = (K + dJ[t]) * M;
        long long a = dA[t], b = dB[t];
        for (int x = 0; x < M; x++) {
            int y = (int)((a * x + b) % M);
            int u = ai + x, v = bj + y;
            if (cnt[u] >= DEG || cnt[v] >= DEG) return PEN;
            adj[(size_t)u * DEG + cnt[u]++] = v;
            adj[(size_t)v * DEG + cnt[v]++] = u;
        }
    }
    long long dups = 0;
    for (int u = 0; u < N; u++) {
        const int *au = adj + (size_t)u * DEG;
        for (int e1 = 0; e1 < DEG; e1++)
            for (int e2 = e1 + 1; e2 < DEG; e2++)
                if (au[e1] == au[e2]) dups++;
    }

    uint64_t *cur = bs0, *nxt = bs1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int e = 0; e < DEG; e++) {
                const uint64_t *c2 = cur + (size_t)adj[(size_t)v * DEG + e] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long unc = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int reach = 0;
        for (int w = 0; w < W; w++) reach += popc(c[w]);
        unc += N - reach;
    }
    return unc + DUPW * dups;
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
            dJ[t] = p[i];
            dA[t] = units[rnd_int(nunits)];
            dB[t] = rnd_int(M);
        }
    }
}

static void perturb_cfg(int nm) {
    for (int s = 0; s < nm; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dA[t] = units[rnd_int(nunits)];
            dB[t] = rnd_int(M);
        }
    }
}

static void save_best(void) {
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bA, dA, sizeof(int) * (size_t)T);
    memcpy(bB, dB, sizeof(int) * (size_t)T);
}

static int accept_move(long long c2, long long c1, double temp) {
    if (c2 <= c1) return 1;
    double de = (double)(c2 - c1) / (double)N;
    return rnd_unit() < exp(-de / temp);
}

/* Simulated annealing; returns the best cost seen, with that state saved in bJ/bA/bB. */
static long long sa_run(int iters, double thi, double tlo) {
    long long cur = eval_cost();
    long long bestc = cur;
    save_best();
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        double p = (double)it / (double)iters;
        double temp = tlo + (thi - tlo) * (1.0 - p);
        long long c2;
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            c2 = eval_cost();
            if (accept_move(c2, cur, temp)) cur = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rnd_int(T);
            int oa = dA[t], ob = dB[t];
            dA[t] = units[rnd_int(nunits)];
            dB[t] = rnd_int(M);
            c2 = eval_cost();
            if (accept_move(c2, cur, temp)) cur = c2;
            else { dA[t] = oa; dB[t] = ob; }
        }
        if (cur < bestc) {
            bestc = cur;
            save_best();
        }
    }
    return bestc;
}

/* A zero-cost state is a valid simple bipartite graph: store it if it beats the record. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    int n = 2 * K * M;
    if (n <= best_n) return;
    int m = T * M;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        int i = dI[t];
        for (int x = 0; x < M; x++) {
            int y = (int)(((long long)bA[t] * x + bB[t]) % M);
            best_e[idx++] = i * M + x;
            best_e[idx++] = (K + bJ[t]) * M + y;
        }
    }
    best_n = n;
    best_m = m;
}

static void pool_add(long long cost) {
    if (cost <= 0 || cost >= PEN) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->K = K; c->M = M; c->cost = cost;
    memcpy(c->J, bJ, sizeof(int) * (size_t)T);
    memcpy(c->A, bA, sizeof(int) * (size_t)T);
    memcpy(c->B, bB, sizeof(int) * (size_t)T);
}

/* Pick an elite configuration whose order still beats the record (best of 3 samples). */
static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (2LL * pool[i].K * pool[i].M > best_n) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    if (DEG < 2 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    MAXT = MAXK * DEG;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].A = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].B = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = PEN;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < 0.5) pi = pick_pool();
        if (pi >= 0) {
            Cfg *c = &pool[pi];
            setup(c->K, c->M);
            memcpy(dJ, c->J, sizeof(int) * (size_t)T);
            memcpy(dA, c->A, sizeof(int) * (size_t)T);
            memcpy(dB, c->B, sizeof(int) * (size_t)T);
            perturb_cfg(2 + rnd_int(4));
            long long bc = sa_run(RUN_ITERS / 2, 1.0, 0.05);
            finish_run(bc);
            pool_add(bc);
            teardown();
        } else {
            int k = 1 + rnd_int(MAXK);
            int gmin = best_n / (2 * k) + 1;
            int spread = gmin / 10 + 2;
            int m = gmin + rnd_int(spread);
            if (m < 2) m = 2;
            setup(k, m);
            random_init();
            long long bc = sa_run(RUN_ITERS, 3.0, 0.05);
            finish_run(bc);
            pool_add(bc);
            teardown();
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
# Safe baseline families (Python).
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
# Driver: safe baselines, then the C affine-layer annealer.
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget. The margin covers process
    # start, the cached compile step, parsing and validation in Python.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
