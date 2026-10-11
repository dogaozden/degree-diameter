import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over a base of K A-vertices and K B-vertices, with
# voltages in an arbitrary finite group of order G (given by a multiplication
# table). The group is either abelian Z_p1 x Z_p2 or the semidirect product
# Z_p1 x|_r Z_p2 (needs r^p2 = 1 mod p1). Vertices: A_i,g = i*G + g and
# B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins A_i,g to B_j,g*s for all g.
# Each layer is a permutation i -> j, so every vertex has degree DEG.
# Left multiplication is an automorphism, so the diameter is <= D iff BFS of
# depth D from each of the 2K block representatives covers all vertices.
#
# Search: simulated annealing on a breakout-weighted count of uncovered
# (representative, vertex) pairs, plus an elite pool (iterated local search)
# that re-anneals perturbed configurations from earlier runs. Fresh starts
# sample a group order near the record, a base size K in {1, 2, 3}, and a
# group type (abelian or semidirect, chosen at random among valid factorings).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXG 2000
#define MAXK 4
#define MAXDEG 64
#define POOLMAX 32
#define POOLP 0.5
#define BRK 120
#define ITERS 5000
#define ILS_ITERS 2500

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

typedef struct {
    int K, typ, p1, p2, p3, G;
    long long cost;
    int *J, *S;
} Cfg;

static Cfg pool[POOLMAX];
static int npool = 0;

static int DEG, DIAM, K, G, T, N, typ, P1, P2, P3;
static int *mulT = NULL;
static int *dI = NULL, *dJ = NULL, *dS = NULL, *perm = NULL;
static int *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int *bestJ = NULL, *bestS = NULL;
static int curstamp = 0;
static long long *wt = NULL, *unc = NULL;
static long long wsum_w = 0, last_w = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

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

/* Group element index a*P2 + b for Z_P1 x|_r Z_P2 (r = 1 gives the abelian group).
   (a,b)*(c,e) = (a + r^b c, b + e). Identity is index 0. */
static void build_table(void) {
    free(mulT);
    mulT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    int *pw = malloc(sizeof(int) * (size_t)P2);
    int r = (typ == 1) ? P3 : 1;
    pw[0] = 1 % P1;
    for (int b = 1; b < P2; b++) pw[b] = (int)((long long)pw[b - 1] * r % P1);
    for (int x = 0; x < G; x++) {
        int a = x / P2, b = x % P2;
        for (int y = 0; y < G; y++) {
            int c = y / P2, d = y % P2;
            int ra = (int)(((long long)a + (long long)pw[b] * c) % P1);
            int rb = (b + d) % P2;
            mulT[(size_t)x * G + y] = ra * P2 + rb;
        }
    }
    free(pw);
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = mulT[(size_t)g * G + s];
}

/* Returns the true cost (sum of uncovered pairs over the 2K block representatives).
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

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS); free(perm);
    free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(wt); free(unc); free(mulT);
    dI = NULL; dJ = NULL; dS = NULL; bestJ = NULL; bestS = NULL; perm = NULL;
    adj = NULL; cnt = NULL; stamp = NULL; fr = NULL; nx = NULL;
    wt = NULL; unc = NULL; mulT = NULL;
}

static void setup_group(int k, int ty, int p1, int p2, int p3) {
    K = k; typ = ty; P1 = p1; P2 = p2; P3 = p3;
    G = p1 * p2;
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * (size_t)G);
    adj = malloc(sizeof(int) * (size_t)N * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    curstamp = 0;
    build_table();
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
    best_n = N;
}

/* Random layers: each layer is a random permutation of the K base vertices.
   Duplicate darts (same i, j, s) are avoided when possible. */
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
            int s = 0;
            for (int tr = 0; tr < 200; tr++) {
                s = rnd_int(G);
                int dup = 0;
                for (int u = 0; u < t; u++)
                    if (dI[u] == i && dJ[u] == p[i] && dS[u] == s) { dup = 1; break; }
                if (!dup) break;
            }
            dS[t] = s;
        }
    }
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Random kicks: swap targets inside a layer, or change one voltage. */
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
   Caller must have just called eval_cost(). Best state by true cost goes to bestJ/bestS. */
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

/* A zero-cost run is a valid graph: load it and emit if it beats the current best. */
static void finish_run(long long bc) {
    if (bc != 0) return;
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    if (N > best_n) emit();
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
    c->K = K; c->typ = typ; c->p1 = P1; c->p2 = P2; c->p3 = P3; c->G = G;
    c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)T);
    memcpy(c->S, S, sizeof(int) * (size_t)T);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++)
        if (2LL * pool[i].K * pool[i].G > (long long)best_n) cand[nc++] = i;
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

/* Random group of order near the record: abelian Z_a x Z_b, or a semidirect
   Z_a x|_r Z_b when such an r exists (tried at random, falls back to abelian). */
static void fresh_group(void) {
    static const int kc[4] = {1, 1, 2, 3};
    int k = kc[rnd_int(4)];
    int gmin = best_n / (2 * k) + 1;
    int spread = gmin / 6 + 2;
    int g = gmin + rnd_int(spread);
    if (g < 2) g = 2;
    if (g > MAXG) g = MAXG;
    static int dv[MAXG + 1];
    int nd = 0;
    for (int d = 1; d <= g; d++)
        if (g % d == 0) dv[nd++] = d;
    int b = dv[rnd_int(nd)];   /* P2 */
    int a = g / b;             /* P1 */
    int ty = 0, r = 1;
    if (b >= 2 && a >= 3 && rnd_unit() < 0.7) {
        for (int tr = 0; tr < 200; tr++) {
            int cand = 1 + rnd_int(a - 1);
            if (gcd_i(cand, a) == 1 && powmod(cand, b, a) == 1 % a) {
                ty = 1;
                r = cand;
                break;
            }
        }
    }
    setup_group(k, ty, a, b, r);
    random_init();
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
    if (DEG < 1 || DIAM < 1 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    int MAXT = MAXK * DEG;
    for (int i = 0; i < POOLMAX; i++) {
        pool[i].J = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].S = malloc(sizeof(int) * (size_t)MAXT);
        pool[i].cost = BIGC;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            /* Iterated local search: perturb an elite configuration and re-anneal. */
            Cfg c = pool[pi];
            setup_group(c.K, c.typ, c.p1, c.p2, c.p3);
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
        } else {
            fresh_group();
            long long cost = eval_cost();
            long long bc = run_sa(ITERS, 1.0, cost);
            finish_run(bc);
            pool_add(bc, bestJ, bestS);
            free_config();
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
# Safe baseline families (Python side). Each is checked before use.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d; diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines first, then one C run over group-lift searches with a
# larger family of groups (abelian and semidirect, base size up to 3).
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Spend most of the budget in C; leave room for compile, parsing and validation.
    elapsed = time.monotonic() - start
    remaining = 0.85 * time_limit - elapsed - 2.0
    if remaining >= 1.0:
        hard = min(remaining + 4.0, time_limit - elapsed - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
