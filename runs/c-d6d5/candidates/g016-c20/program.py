import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley / voltage lifts over two families of finite groups.
#
#   GT = 0: semidirect product Z_M x| Z_K2 (element a*K2+b, r^K2 = 1 mod M).
#   GT = 1: Heisenberg-type group H(M) of order M^3, elements (a,b,c) with
#           (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b') mod M.
#           Non-abelian for every M; for M = 7 the order is 343.
#
# Layout: K A-blocks and K B-blocks, each a copy of G. Dart t = (i, j, s) joins
# A_{i,g} to B_{j, g*s} for all g. Each layer is a permutation of the blocks, so
# every vertex has degree DEG. Left multiplication is an automorphism, so
# diameter <= D iff a BFS of depth D from the identity of each of the 2K blocks
# reaches everything.
#
# Search: simulated annealing on the number of uncovered ordered pairs, with
# breakout weights per block. The annealer may move dart voltages and the
# B-target of darts within a layer. The engine cycles between the two group
# families, so the Heisenberg family is tried on every run. An elite pool
# keeps good near-solutions for iterated local search.
#
# Timing uses a wall clock measured from program start.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 5000
#define ILS_ITERS 2500
#define MAXPOOL 32
#define POOLP 0.5
#define BRK 120
#define MAXDEG 16
#define MAXT 64
#define MAXG 4096
#define MAXN 24576
#define MAXK2 16
#define MAXEDGE (MAXT * MAXG)

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

static int DEG, DIAM;
static int GT, K, K2, M, R, G, T, N;
static int Rpow[MAXK2];
static int dI[MAXT], dJ[MAXT], dS[MAXT], bestJ[MAXT], bestS[MAXT];
static int perm[MAXEDGE];
static int adjv[MAXN * MAXDEG];
static int cnt[MAXN], stamp[MAXN], frA[MAXN], nxA[MAXN];
static int curstamp = 0;
static long long wt[6], unc[6];
static long long wsum_w = 0, last_w = 0;
static int best_n = 0, best_m = 0;
static int best_e[2 * MAXEDGE];

typedef struct {
    int gt, k, k2, m, r, n;
    long long cost;
    int J[MAXT], S[MAXT];
} Cfg;

static Cfg pool[MAXPOOL];
static int npool = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group multiplication for the current family. */
static int gmul(int x, int y) {
    if (GT == 0) {
        int a = x / K2, b = x % K2;
        int c = y / K2, e = y % K2;
        int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
        return ra * K2 + (b + e) % K2;
    } else {
        int MM = M * M;
        int a = x / MM, b = (x / M) % M, c = x % M;
        int a2 = y / MM, b2 = (y / M) % M, c2 = y % M;
        int na = (a + a2) % M, nb = (b + b2) % M;
        int nc = (c + c2 + a * b2) % M;
        return (na * M + nb) * M + nc;
    }
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

/* Returns the true cost (uncovered ordered pairs over the 2K block identities).
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
            adjv[a * DEG + cnt[a]++] = b;
            adjv[b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = frA, *h = nxA;
        int fsz = 1, count = 1;
        int src = r * G;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adjv + (size_t)f[q] * DEG;
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

static void setup_group(int gt, int k, int k2, int m, int r) {
    GT = gt; K = k; K2 = k2; M = m; R = r;
    G = (gt == 0) ? m * k2 : m * m * m;
    N = 2 * K * G;
    T = DEG * K;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 6; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

static void emit(void) {
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = T * G;
    best_n = N;
}

static void random_init(void) {
    int p[4];
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

/* Annealing on the weighted cost with breakout weight bumps. The caller must
   have just called eval_cost(). Best state (true cost) goes to bestJ/bestS. */
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

/* A zero-cost run is a valid graph: load it and emit if it beats the best so far. */
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
    if (npool < MAXPOOL) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < MAXPOOL; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    c->gt = GT; c->k = K; c->k2 = K2; c->m = M; c->r = R; c->n = N;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[MAXPOOL], nc = 0;
    for (int i = 0; i < npool; i++)
        if (pool[i].n > best_n) cand[nc++] = i;
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
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG || 2 * DEG > MAXT) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search from an elite configuration. */
            Cfg c = pool[pi];
            setup_group(c.gt, c.k, c.k2, c.m, c.r);
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            continue;
        }

        /* Fresh lift: alternate between the two group families. */
        int k = (rnd_unit() < 0.5) ? 1 : 2;
        int gt = (rnd_unit() < 0.5) ? 1 : 0;
        int gmin = best_n / (2 * k) + 1;
        if (gt == 1) {
            int m = 2;
            while (m * m * m < gmin) m++;
            m += rnd_int(2);
            if (m > 16) continue;
            setup_group(1, k, 1, m, 1);
        } else {
            int spread = gmin / 6 + 2;
            int g = gmin + rnd_int(spread);
            if (g < 2) g = 2;
            if (g > MAXG) continue;
            int opts[12], no = 0;
            for (int c = 1; c <= 12; c++)
                if (g % c == 0 && g / c >= 2) opts[no++] = c;
            if (no == 0) continue;
            int c2 = opts[rnd_int(no)];
            int m = g / c2, r = 1;
            if (c2 > 1) {
                int found = 0;
                for (int tr = 0; tr < 200 && !found; tr++) {
                    int cand = 1 + rnd_int(m - 1);
                    if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                        r = cand;
                        found = 1;
                    }
                }
                if (!found) {
                    c2 = 1;
                    m = g;
                    r = 1;
                }
            }
            setup_group(0, k, c2, m, r);
        }
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
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
# Safe baseline families (always validated before being returned).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C search over Heisenberg and
# semidirect bi-Cayley / voltage lifts.
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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Reserve time for compilation (outside the C clock), parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 3.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
