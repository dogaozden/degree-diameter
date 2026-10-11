import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over the groups Z_m^dd x|_A Z_kk (dd = 1, 2, 3).
#
# A group element is (v, b) with v in Z_m^dd and b in Z_kk, coded as
# index v*kk + b. The product is (v, b)(w, e) = (v + A^b w, b + e), where A is
# a dd x dd matrix over Z_m that is invertible mod m and satisfies A^kk = I.
# dd = 1 gives the cyclic semidirect products used before. dd = 2 and 3 give
# non-cyclic normal subgroups, a family the earlier engine never sampled.
#
# Base graph: K A-vertices and K B-vertices. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g, with one dart per layer and each layer a
# permutation. Left multiplication is an automorphism for any group, so
# diameter <= D iff BFS of depth D from the 2K block representatives covers all.
#
# Search: simulated annealing on a breakout-weighted cost, with an elite pool
# and iterated local search (ILS) on pool entries. Timing uses wall-clock time.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h, with identity = index 0.
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
#define MAXG 1200

static uint64_t rs[2];
static struct timespec T0;

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

static int DEG, DIAM, K, DD, M, KK, G, T, MAXT;
static int A[9];
static int *Apow = NULL;
static int *mt = NULL;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;

typedef struct {
    int K, DD, M, KK;
    int A[9];
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

static long long ipow_ll(long long b, int e) {
    long long r = 1;
    for (int i = 0; i < e; i++) {
        r *= b;
        if (r > 1000000000LL) return 1000000000LL;
    }
    return r;
}

static int gcd_i(int a, int b) {
    if (a < 0) a = -a;
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Z = X * Y mod m for dd x dd matrices (Z may alias X or Y). */
static void mat_mul(const int *X, const int *Y, int *Z, int dd, int m) {
    int tmp[9];
    for (int i = 0; i < dd; i++)
        for (int j = 0; j < dd; j++) {
            long long s = 0;
            for (int l = 0; l < dd; l++) s += (long long)X[i * dd + l] * Y[l * dd + j];
            tmp[i * dd + j] = (int)(s % m);
        }
    memcpy(Z, tmp, sizeof(int) * (size_t)(dd * dd));
}

static long long det_small(const int *X, int dd) {
    if (dd == 1) return X[0];
    if (dd == 2) return (long long)X[0] * X[3] - (long long)X[1] * X[2];
    return (long long)X[0] * ((long long)X[4] * X[8] - (long long)X[5] * X[7])
         - (long long)X[1] * ((long long)X[3] * X[8] - (long long)X[5] * X[6])
         + (long long)X[2] * ((long long)X[3] * X[7] - (long long)X[4] * X[6]);
}

/* Set the current group and build its multiplication table. */
static void build_group(int k, int dd, int m, int kk, const int *Am) {
    K = k; DD = dd; M = m; KK = kk;
    int V = (int)ipow_ll(m, dd);
    G = V * kk;
    memcpy(A, Am, sizeof(int) * 9);
    free(Apow);
    Apow = malloc(sizeof(int) * 9 * (size_t)kk);
    int cur[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
    for (int i = 0; i < dd; i++) cur[i * dd + i] = 1 % m;
    for (int b = 0; b < kk; b++) {
        memcpy(Apow + 9 * (size_t)b, cur, sizeof(int) * 9);
        mat_mul(cur, A, cur, dd, m);
    }
    free(mt);
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++) {
        int vx = x / kk, b = x % kk;
        int xd[3] = {0, 0, 0};
        int t = vx;
        for (int i = 0; i < dd; i++) { xd[i] = t % m; t /= m; }
        const int *P = Apow + 9 * (size_t)b;
        for (int y = 0; y < G; y++) {
            int vy = y / kk, e = y % kk;
            int yd[3] = {0, 0, 0};
            t = vy;
            for (int j = 0; j < dd; j++) { yd[j] = t % m; t /= m; }
            int code = 0, mul = 1;
            for (int i = 0; i < dd; i++) {
                int s = xd[i];
                for (int j = 0; j < dd; j++) s += P[i * dd + j] * yd[j];
                s %= m;
                code += s * mul;
                mul *= m;
            }
            mt[(size_t)x * G + y] = code * kk + (b + e) % kk;
        }
    }
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = mt[(size_t)g * G + s];
}

static void alloc_config(void) {
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
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = NULL;
    wt = unc = NULL;
}

/* Returns the true cost (uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
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
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[8];
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

/* Random kicks: voltage changes and within-layer target swaps (both keep layers permutations). */
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

/* Annealing on the weighted cost with breakout weight bumps. */
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
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    }
    best_m = m;
    best_n = 2 * K * G;
}

/* A zero-cost run is a valid graph: load it and emit if it beats the record. */
static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
        memcpy(dS, bestS, sizeof(int) * (size_t)T);
        for (int t = 0; t < T; t++) build_perm(t);
        if (2 * K * G > best_n) emit();
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
    Cfg *c = &pool[slot];
    c->K = K; c->DD = DD; c->M = M; c->KK = KK; c->cost = cost;
    memcpy(c->A, A, sizeof(int) * 9);
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static long long cfg_nodes(const Cfg *c) {
    return 2LL * c->K * ipow_ll(c->M, c->DD) * c->KK;
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (cfg_nodes(&pool[i]) > best_n) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* Sample Z_m^dd x|_A Z_kk with 2*k*G > best_n (gmin = minimal G). */
static int sample_group(int gmin, int *dd_o, int *m_o, int *kk_o, int *A_o) {
    int spread = gmin / 6 + 2;
    int Gt = gmin + rnd_int(spread);
    if (Gt < 2 || Gt > MAXG) return 0;
    double u = rnd_unit();
    int dd = u < 0.4 ? 1 : (u < 0.8 ? 2 : 3);
    int mmax = 1;
    while (mmax + 1 <= Gt && ipow_ll(mmax + 1, dd) <= Gt) mmax++;
    if (mmax < 2) { dd = 1; mmax = Gt; }
    for (int tr = 0; tr < 400; tr++) {
        int m = 2 + rnd_int(mmax - 1);
        long long V = ipow_ll(m, dd);
        if (V > Gt) continue;
        int Am[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
        for (int i = 0; i < dd * dd; i++) Am[i] = rnd_int(m);
        long long dt = det_small(Am, dd) % m;
        if (dt < 0) dt += m;
        if (gcd_i((int)dt, m) != 1) continue;
        int I9[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
        for (int i = 0; i < dd; i++) I9[i * dd + i] = 1;
        int P[9];
        memcpy(P, Am, sizeof(int) * 9);
        long long LIM = MAXG / V + 1;
        long long ord = 1;
        while (ord <= LIM && memcmp(P, I9, sizeof(int) * (size_t)(dd * dd)) != 0) {
            mat_mul(P, Am, P, dd, m);
            ord++;
        }
        if (ord > LIM || memcmp(P, I9, sizeof(int) * (size_t)(dd * dd)) != 0) continue;
        long long step = V * ord;
        long long base = (Gt + step - 1) / step;
        if (base < 1) base = 1;
        long long kk = ord * base;
        long long G2 = V * kk;
        if (G2 > MAXG || G2 < 2) continue;
        *dd_o = dd;
        *m_o = m;
        *kk_o = (int)kk;
        memcpy(A_o, Am, sizeof(int) * 9);
        return 1;
    }
    return 0;
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MAXT = 3 * DEG;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[5] = {1, 1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg c = pool[pi];
            build_group(c.K, c.DD, c.M, c.KK, c.A);
            alloc_config();
            memcpy(dJ, c.J, sizeof(int) * (size_t)T);
            memcpy(dS, c.S, sizeof(int) * (size_t)T);
            for (int t = 0; t < T; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            for (int t = 0; t < T; t++) build_perm(t);
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
            continue;
        }

        /* Fresh random lift over a sampled non-cyclic or cyclic group. */
        int k = kc[rnd_int(5)];
        int gmin = best_n / (2 * k) + 1;
        int dd = 1, m = 2, kk = 1;
        int Am[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
        if (!sample_group(gmin, &dd, &m, &kk, Am)) continue;
        build_group(k, dd, m, kk, Am);
        alloc_config();
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, bestJ, bestS);
        free_config();
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
# Driver: baselines in Python, then the C search over matrix semidirect groups.
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

    # Give the C search most of the budget; leave room for the compile step,
    # parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
