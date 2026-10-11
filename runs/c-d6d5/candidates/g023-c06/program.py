import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: tabu search over voltage lifts of semidirect products
# Z_M x| Z_K2 with a base of K A-vertices and K B-vertices.
#
# Compared with the previous annealer, this engine:
#   * scores every voltage move by evaluating a sampled set of alternative
#     voltages and taking the best non-tabu one (tabu search with aspiration),
#   * keeps a short-term tabu list on (dart, old voltage) pairs,
#   * diversifies by perturbing the incumbent or restarting at random,
#   * penalises duplicate darts with a graded cost instead of a flat BIGC, so
#     the search can move through infeasible states.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. Each layer is a permutation of the base, so every
# vertex has degree DEG. Left multiplication is an automorphism, so the diameter
# is at most D iff BFS of depth D from each of the 2K block representatives
# reaches every vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define TABU_ITERS 2500
#define STAG 400
#define SAMPLE 40
#define LAYER_P 0.15

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

static int DEG, DIAM, K, K2, M, G, T, R, N;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static int *Rpow, *dI, *dJ, *dS, *perm, *adj, *cnt, *seen, *fr, *nx, *tabu, *bJ, *bS;
static int gen = 0;

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

static void alloc_group(void) {
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    tabu = calloc((size_t)T * G, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    seen = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    gen = 0;
}

static void free_group(void) {
    free(dI); free(dJ); free(dS); free(bJ); free(bS);
    free(perm); free(tabu); free(adj); free(cnt); free(seen);
    free(fr); free(nx); free(Rpow);
}

static void build_perm(int t) {
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, dS[t]);
}

static void set_volt(int t, int v) {
    dS[t] = v;
    build_perm(t);
}

static void load_best(void) {
    memcpy(dJ, bJ, sizeof(int) * (size_t)T);
    memcpy(dS, bS, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
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
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
    free(p);
    for (int t = 0; t < T; t++) build_perm(t);
}

/* Number of duplicate darts (same i, j and voltage). */
static long long dup_pairs(void) {
    long long c = 0;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) c++;
    return c;
}

/* Cost = uncovered ordered pairs over the 2K block representatives,
   plus N per duplicate dart pair. Zero cost means a valid simple graph. */
static long long eval_cost(void) {
    long long dup = dup_pairs();
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            if (cnt[a] >= DEG || cnt[b] >= DEG) return BIGC;
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (gen >= 2000000000) {
            memset(seen, 0, sizeof(int) * (size_t)N);
            gen = 0;
        }
        gen++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = r * G;
        seen[r * G] = gen;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (seen[v] != gen) {
                        seen[v] = gen;
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
    return total + dup * (long long)N;
}

/* Tabu search from a random start, with diversification. Best state goes to bJ/bS. */
static long long tabu_group(void) {
    random_init();
    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    int last_imp = 0;
    for (int it = 1; it <= TABU_ITERS && bestc > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        if (it - last_imp > STAG) {
            if (rnd_unit() < 0.5) {
                load_best();
                int kicks = 3 + rnd_int(4);
                for (int s = 0; s < kicks; s++) set_volt(rnd_int(T), rnd_int(G));
            } else {
                random_init();
            }
            memset(tabu, 0, sizeof(int) * (size_t)T * G);
            cur = eval_cost();
            last_imp = it;
            continue;
        }
        if (K > 1 && rnd_unit() < LAYER_P) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c = eval_cost();
            if (c <= cur || rnd_unit() < 0.02) {
                cur = c;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int old = dS[t];
            int bestv = -1;
            long long bestvc = 0;
            int enumerate = (G - 1 <= SAMPLE);
            int ns = enumerate ? G - 1 : SAMPLE;
            for (int s = 0; s < ns; s++) {
                int v = enumerate ? (old + 1 + s) % G : rnd_int(G);
                if (v == old) continue;
                set_volt(t, v);
                long long c = eval_cost();
                if (tabu[t * G + v] > it && c >= bestc) continue;   /* tabu, no aspiration */
                if (bestv < 0 || c < bestvc || (c == bestvc && rnd_unit() < 0.5)) {
                    bestv = v;
                    bestvc = c;
                }
            }
            if (bestv < 0) {
                set_volt(t, old);
                continue;
            }
            set_volt(t, bestv);
            tabu[t * G + old] = it + 4 + rnd_int(8);
            cur = bestvc;
        }
        if (cur < bestc) {
            bestc = cur;
            last_imp = it;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
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
    best_n = N;
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
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[4] = {1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(4)];
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 4 + 3;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[16], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
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
        K = k; K2 = c2; M = m; R = r; G = m * c2;
        alloc_group();
        long long bc = tabu_group();
        if (bc == 0) {
            load_best();
            if (N > best_n) emit();
        }
        free_group();
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
# Safe baseline constructions (always valid, used as fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        # Araujo-Pardo & Lopez construction for d = q + 2 with q a prime power >= 3.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ara = lib.araujo_lopez_graph(d - 2)
                consider(ara[0], ara[1])
            except ValueError:
                pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget. The C program measures its own
    # wall-clock deadline from process start; the margin covers compilation,
    # parsing and validation.
    budget = 0.9 * time_limit - (time.monotonic() - start) - 4.0
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                            timeout=budget + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
