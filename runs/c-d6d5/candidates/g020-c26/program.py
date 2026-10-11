"""Degree-diameter search for bipartite graphs, with tabu search over voltage lifts.

Approach: lifts of a K+K base multigraph over a semidirect product Z_m x| Z_K2.
Each lift is searched by tabu search on the number of uncovered (block, vertex)
pairs, using sampled single-dart moves (voltage change or within-layer target
swap). Group orders are ratcheted upward from the current best order, and
the search covers base sizes K = 1..4 with a Moore-bound-aware order range.
A PG(2,q) incidence graph is the Python fallback; any invalid result is replaced.
"""
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXKB 4
#define NSAMP 48
#define TENURE 10
#define RUN_STEPS 3000

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

static int DEG, DIAM, K, K2, M, G, T, R;
static int *Rpow = NULL;
static int *dI = NULL, *dJ = NULL, *dS = NULL, *bestJ = NULL, *bestS = NULL;
static int *perm = NULL, *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int *tabu_until = NULL;
static int curstamp = 0;
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

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

/* True cost: total uncovered ordered pairs over the 2K block representatives.
   Returns BIGC if two darts coincide (that would create a multi-edge). */
static long long eval_cost(void) {
    int N = 2 * K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
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
        total += N - count;
    }
    return total;
}

static void alloc_config(void) {
    int N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    tabu_until = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS); free(tabu_until);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx); free(Rpow);
    dI = dJ = dS = bestJ = bestS = tabu_until = NULL;
    perm = adj = cnt = stamp = fr = nx = NULL;
    Rpow = NULL;
}

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r; G = m * c2;
    alloc_config();
    for (int t = 0; t < T; t++) dI[t] = t % K;
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

/* Each layer l is a permutation: darts t = l*K + i, with dI = i and dJ a permutation of 0..K-1. */
static void random_init(void) {
    int p[MAXKB];
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

/* Evaluate a candidate without keeping it. */
static long long try_shift(int t, int s) {
    int old = dS[t];
    dS[t] = s;
    build_perm(t);
    long long c = eval_cost();
    dS[t] = old;
    build_perm(t);
    return c;
}

static long long try_swap(int t1, int t2) {
    int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
    long long c = eval_cost();
    tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
    return c;
}

/* Tabu search: each step samples NSAMP moves, takes the best non-tabu one
   (aspiration: a tabu move is allowed if it beats the run's best cost).
   Returns the best true cost; the best configuration is in bestJ/bestS. */
static long long tabu_search(long long cost, int steps) {
    long long bestc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) tabu_until[t] = 0;
    for (int st = 1; st <= steps && bestc > 0; st++) {
        if ((st & 31) == 0 && elapsed() > DEADLINE) break;
        long long bc = BIGC;
        int kind = -1, ba = 0, bb = 0;
        for (int s = 0; s < NSAMP; s++) {
            if (K > 1 && rnd_unit() < 0.3) {
                int l = rnd_int(DEG);
                int i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                long long c = try_swap(t1, t2);
                if ((tabu_until[t1] > st || tabu_until[t2] > st) && c >= bestc) continue;
                if (c < bc) { bc = c; kind = 1; ba = t1; bb = t2; }
            } else {
                int t = rnd_int(T);
                int nv = rnd_int(G);
                if (nv == dS[t]) continue;
                long long c = try_shift(t, nv);
                if (tabu_until[t] > st && c >= bestc) continue;
                if (c < bc) { bc = c; kind = 0; ba = t; bb = nv; }
            }
        }
        if (kind < 0) {
            /* No usable sampled move: random kick to keep moving. */
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
            build_perm(t);
            cost = eval_cost();
        } else if (kind == 1) {
            int tmp = dJ[ba]; dJ[ba] = dJ[bb]; dJ[bb] = tmp;
            tabu_until[ba] = st + TENURE + rnd_int(TENURE);
            tabu_until[bb] = st + TENURE + rnd_int(TENURE);
            cost = bc;
        } else {
            dS[ba] = bb;
            build_perm(ba);
            tabu_until[ba] = st + TENURE + rnd_int(TENURE);
            cost = bc;
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
        if (2 * K * G > best_n) emit();
    }
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
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    double moore = 0.0, pw = 1.0;
    for (int i = 0; i < DIAM && i < 60; i++) { moore += pw; pw *= (double)(DEG - 1); }
    moore *= 2.0;

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[6] = {1, 1, 2, 2, 3, 4};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(6)];
        long long lo = best_n / (2 * k) + 1;
        long long hi = (long long)(moore / (2.0 * k));
        if (lo > hi) continue;
        long long span = lo / 4 + 3;
        long long gl = lo + (long long)rnd_int((int)span);
        if (gl > hi) gl = hi;
        int g = (int)gl;
        if (g < 2) continue;

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

        setup_group(k, c2, m, r);
        random_init();
        long long cost = eval_cost();
        long long bc = tabu_search(cost, RUN_STEPS);
        finish_run(bc);
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Most of the budget goes to the C search; the reserve covers parsing,
    # validation and the one-off compile when the cache is cold.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{remaining:.2f}", best_n],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
