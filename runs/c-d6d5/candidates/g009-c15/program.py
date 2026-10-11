import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New family in this version: voltage lifts over NON-METABELIAN groups.
#
# Two group families are searched by the C engine:
#   type 0: Z_M x| Z_K2 (cyclic normal subgroup, action by a unit R with R^K2 = 1 mod M)
#   type 1: Z_M^2 x| Z_K2 (rank-2 normal subgroup, action by a 2x2 matrix A with A^K2 = I mod M)
# Type 1 groups are genuinely different from the cyclic-based families used before:
# their multiplication is not commutative, so the lifts have different distance structure.
# The group law is stored as an explicit multiplication table (order <= GMAX).
#
# Base graph: K A-vertices and K B-vertices. Dart t = (i, j, s) joins A_{i,g} to B_{j,g*s}
# for all g in the group. Each layer is a permutation, so the graph is DEG-regular and
# bipartite. Left multiplication is an automorphism, so diameter <= D iff BFS of depth D
# from each of the 2K block representatives covers all vertices.
#
# Search: simulated annealing on the weighted count of uncovered pairs (breakout weights),
# with an elite pool and iterated local search. Fresh groups are sampled from both families.
#
# Safe fallback: K_{d,d} (diameter 2), PG(2,q) incidence graphs (D >= 3), W(q) (D >= 4).
# Every result is checked with lib.is_valid before it is returned.
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
#define AFFP 0.6
#define BRK 150
#define GMAX 2000

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

typedef struct {
    int type;        /* 0: Z_M x| Z_K2 with unit R; 1: Z_M^2 x| Z_K2 with matrix A */
    int M, K2, R;
    int A[4];        /* row-major 2x2 matrix mod M (type 1) */
    int G;           /* group order */
} Grp;

typedef struct {
    int K;
    Grp g;
    long long cost;
    int *J, *S;
} Cfg;

static int DEG, DIAM, K, T, G;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp;
static double DEADLINE;
static int best_n, best_m;
static int *best_e = NULL;
static int MAXT;

static long long *wt = NULL;
static long long *unc = NULL;
static long long wsum_w = 0;
static long long last_w = 0;

static Grp GP;
static int *MT = NULL;

static Cfg pool[POOLMAX];
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

/* Multiplication table. Element index for type 0: a*K2+b with a in Z_M.
   For type 1: (vx*M+vy)*K2+b with v in Z_M^2.
   Type 0: (a,b)(c,e) = (a + R^b c, b+e). Type 1: (v,b)(w,e) = (v + A^b w, b+e). */
static void build_group_table(void) {
    int M = GP.M, K2 = GP.K2;
    G = GP.G;
    free(MT);
    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    if (GP.type == 0) {
        int *Rp = malloc(sizeof(int) * (size_t)K2);
        Rp[0] = 1 % M;
        for (int b = 1; b < K2; b++) Rp[b] = (int)((long long)Rp[b - 1] * GP.R % M);
        for (int x = 0; x < G; x++) {
            int a = x / K2, b = x % K2;
            for (int y = 0; y < G; y++) {
                int c = y / K2, e = y % K2;
                int ra = (int)(((long long)a + (long long)Rp[b] * c) % M);
                MT[(size_t)x * G + y] = ra * K2 + (b + e) % K2;
            }
        }
        free(Rp);
    } else {
        int *Ap = malloc(sizeof(int) * 4 * (size_t)K2);
        int P[4] = {1 % M, 0, 0, 1 % M};
        for (int b = 0; b < K2; b++) {
            for (int i = 0; i < 4; i++) Ap[4 * b + i] = P[i];
            int Q[4];
            Q[0] = (int)(((long long)P[0] * GP.A[0] + (long long)P[1] * GP.A[2]) % M);
            Q[1] = (int)(((long long)P[0] * GP.A[1] + (long long)P[1] * GP.A[3]) % M);
            Q[2] = (int)(((long long)P[2] * GP.A[0] + (long long)P[3] * GP.A[2]) % M);
            Q[3] = (int)(((long long)P[2] * GP.A[1] + (long long)P[3] * GP.A[3]) % M);
            memcpy(P, Q, sizeof P);
        }
        int MM = M * M;
        for (int x = 0; x < G; x++) {
            int vi = x / K2, b = x % K2;
            int vx = vi / M, vy = vi % M;
            for (int y = 0; y < G; y++) {
                int wi = y / K2, e = y % K2;
                int wx = wi / M, wy = wi % M;
                int ux = (int)(((long long)Ap[4 * b] * wx + (long long)Ap[4 * b + 1] * wy) % M);
                int uy = (int)(((long long)Ap[4 * b + 2] * wx + (long long)Ap[4 * b + 3] * wy) % M);
                int rx = (vx + ux) % M, ry = (vy + uy) % M;
                int ri = rx * M + ry;
                MT[(size_t)x * G + y] = ri * K2 + (b + e) % K2;
            }
        }
        (void)MM;
        free(Ap);
    }
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = MT[(size_t)g * G + s];
}

/* Returns the true cost (sum of uncovered ordered pairs over block reps).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    int Nn = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < 2 * K; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)Nn);
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
            memset(stamp, 0, sizeof(int) * (size_t)Nn);
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
        unc[r] = Nn - count;
        total += Nn - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void alloc_config(void) {
    int Nn = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)Nn * DEG);
    cnt = malloc(sizeof(int) * (size_t)Nn);
    stamp = calloc((size_t)Nn, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)Nn);
    nx = malloc(sizeof(int) * (size_t)Nn);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc); free(MT);
    dI = dJ = dS = bestJ = bestS = NULL;
    perm = adj = NULL;
    cnt = stamp = fr = nx = NULL;
    wt = NULL;
    unc = NULL;
    MT = NULL;
}

static void setup_group(int k, Grp g) {
    K = k;
    GP = g;
    G = g.G;
    build_group_table();
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
    for (int b = 0; b < 2 * K; b++) wt[b] = 1;
    wsum_w = 2 * K;
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
    c->K = K;
    c->g = GP;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = 2LL * pool[i].K * pool[i].g.G;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* Order of a 2x2 matrix mod m, if it is at most lim; 0 otherwise (also when singular). */
static int mat_order(const int *A, int m, int lim) {
    int P[4] = {1 % m, 0, 0, 1 % m};
    for (int k = 1; k <= lim; k++) {
        int Q[4];
        Q[0] = (int)(((long long)P[0] * A[0] + (long long)P[1] * A[2]) % m);
        Q[1] = (int)(((long long)P[0] * A[1] + (long long)P[1] * A[3]) % m);
        Q[2] = (int)(((long long)P[2] * A[0] + (long long)P[3] * A[2]) % m);
        Q[3] = (int)(((long long)P[2] * A[1] + (long long)P[3] * A[3]) % m);
        memcpy(P, Q, sizeof P);
        if (P[0] == 1 % m && P[1] == 0 && P[2] == 0 && P[3] == 1 % m) return k;
    }
    return 0;
}

/* Random non-metabelian-type group Z_m^2 x| Z_k2 with order in [gmin, gmax]. */
static int try_affine(int gmin, int gmax, Grp *out) {
    if (gmax < gmin) return 0;
    for (int tr = 0; tr < 4000; tr++) {
        int m = 2 + rnd_int(40);
        int A[4];
        for (int i = 0; i < 4; i++) A[i] = rnd_int(m);
        int k2 = mat_order(A, m, 12);
        if (k2 <= 0) continue;
        long long gg = (long long)m * m * k2;
        if (gg < gmin || gg > gmax) continue;
        out->type = 1;
        out->M = m;
        out->K2 = k2;
        out->R = 1;
        for (int i = 0; i < 4; i++) out->A[i] = A[i];
        out->G = (int)gg;
        return 1;
    }
    return 0;
}

/* Cyclic-based semidirect group Z_m x| Z_c2 with order in [gmin, gmax]. */
static int try_cyclic(int gmin, int gmax, Grp *out) {
    if (gmax < gmin) return 0;
    int g = gmin + rnd_int(gmax - gmin + 1);
    if (g < 2) g = 2;
    int opts[12], no = 0;
    for (int c = 1; c <= 12; c++)
        if (g % c == 0 && g / c >= 2) opts[no++] = c;
    if (no == 0) return 0;
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
    out->type = 0;
    out->M = m;
    out->K2 = c2;
    out->R = r;
    for (int i = 0; i < 4; i++) out->A[i] = 0;
    out->G = m * c2;
    return 1;
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
            setup_group(c.K, c.g);
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

        /* Fresh lift over a fresh group of order near the record. */
        int k = kc[rnd_int(5)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 6 + 2;
        int gmax = gmin + spread;
        if (gmax > GMAX) gmax = GMAX;
        if (gmin > gmax) continue;
        Grp g;
        int ok = 0;
        if (rnd_unit() < AFFP) ok = try_affine(gmin, gmax, &g);
        if (!ok) ok = try_cyclic(gmin, gmax, &g);
        if (!ok) continue;
        setup_group(k, g);
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
# Driver: baselines in Python, then the C annealer over cyclic-based and
# rank-2 (non-metabelian) group lifts.
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
