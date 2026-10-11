import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley voltage lifts over semidirect products Z_m x|_r Z_k2,
# with K A-blocks and K B-blocks. Searched by steepest-descent tabu search.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h. Dart t = (i, j, s) joins
# A_i,g to B_j,g*s for all g. dI[t] = t % K, so every A-block gets DEG darts.
# Each layer l of darts uses a permutation dJ over the K B-blocks, so every
# B-block also gets DEG darts. Moves keep both properties:
#   - change one dart's shift s (any value in 0..G-1), or
#   - swap two B-targets inside one layer.
#
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS
# of depth D from the identity of each of the 2K blocks reaches all N vertices.
# Cost = total number of unreached (source, vertex) pairs. Cost 0 is valid.
#
# Search: at each step the whole neighbourhood is scanned and the best
# non-tabu move is taken (aspiration when it beats the run's best). The
# tabu tenure is randomised. After STALE_LIMIT steps without improvement,
# the run restarts from a fresh random lift over a newly drawn group.
#
# Groups are drawn with order G such that 2KG exceeds the best known order.
# Any zero-cost lift is emitted as the new best.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define BIGC 1000000000LL
#define STALE_LIMIT 250
#define TENURE_BASE 6
#define TENURE_RAND 10

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, K, K2, M, G, T, N, R;
static int *Rpow = NULL;
static int *dI = NULL, *dJ = NULL, *dS = NULL, *perm = NULL;
static int *bestS = NULL, *bestJ = NULL;
static int *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int *tabu = NULL;
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

static void set_shift(int t, int s) {
    dS[t] = s;
    build_perm(t);
}

static void swap_j(int t1, int t2) {
    int tmp = dJ[t1];
    dJ[t1] = dJ[t2];
    dJ[t2] = tmp;
}

/* Total number of unreached (block representative, vertex) pairs. */
static long long eval_cost(void) {
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

static void setup_group(int k, int c2, int m, int r) {
    K = k; K2 = c2; M = m; R = r;
    G = m * c2;
    T = DEG * K;
    N = 2 * K * G;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    perm = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    tabu = calloc((size_t)T * G, sizeof(int));
    Rpow = malloc(sizeof(int) * (size_t)K2);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    curstamp = 0;
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestS); free(bestJ);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(tabu); free(Rpow);
    dI = dJ = dS = bestS = bestJ = perm = NULL;
    adj = cnt = stamp = fr = nx = NULL;
    tabu = NULL;
    Rpow = NULL;
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

/* Each layer gets a random permutation of the B-blocks; shifts are random. */
static void random_init(void) {
    int p[16];
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

/* Steepest-descent tabu search over single-shift and layer-swap moves.
   Leaves the best configuration found in dS/dJ/perm and returns its cost. */
static long long tabu_search(void) {
    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memset(tabu, 0, sizeof(int) * (size_t)T * G);
    int stale = 0;
    for (int it = 1; bestc > 0 && stale < STALE_LIMIT; it++) {
        if (elapsed() > DEADLINE) break;
        long long bm = -1;
        int bt = -1, bs = -1, btype = -1, ties = 0;

        for (int t = 0; t < T; t++) {
            int old = dS[t];
            for (int s = 0; s < G; s++) {
                if (s == old) continue;
                set_shift(t, s);
                long long c = eval_cost();
                set_shift(t, old);
                int is_tabu = tabu[(size_t)t * G + s] > it;
                if (is_tabu && c >= bestc) continue;
                if (bm < 0 || c < bm) {
                    bm = c; bt = t; bs = s; btype = 0; ties = 1;
                } else if (c == bm) {
                    ties++;
                    if (rnd_int(ties) == 0) { bt = t; bs = s; btype = 0; }
                }
            }
        }

        if (K > 1) {
            for (int l = 0; l < DEG; l++)
                for (int i1 = 0; i1 < K; i1++)
                    for (int i2 = i1 + 1; i2 < K; i2++) {
                        int t1 = l * K + i1, t2 = l * K + i2;
                        swap_j(t1, t2);
                        long long c = eval_cost();
                        swap_j(t1, t2);
                        if (bm < 0 || c < bm) {
                            bm = c; bt = t1; bs = t2; btype = 1; ties = 1;
                        } else if (c == bm) {
                            ties++;
                            if (rnd_int(ties) == 0) { bt = t1; bs = t2; btype = 1; }
                        }
                    }
        }

        if (bt < 0) { stale++; continue; }

        if (btype == 0) {
            int old = dS[bt];
            set_shift(bt, bs);
            tabu[(size_t)bt * G + old] = it + TENURE_BASE + rnd_int(TENURE_RAND);
        } else {
            swap_j(bt, bs);
        }
        cur = bm;
        if (cur < bestc) {
            bestc = cur;
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            stale = 0;
        } else {
            stale++;
        }
    }
    memcpy(dS, bestS, sizeof(int) * (size_t)T);
    memcpy(dJ, bestJ, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_perm(t);
    return bestc;
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
    if (DEG < 1 || DIAM < 1 || DEG > 16) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int k = 1 + rnd_int(3);
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 8 + 2;
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
        setup_group(k, c2, m, r);
        random_init();
        long long bc = tabu_search();
        if (bc == 0 && N > best_n) emit();
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
# Safe baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d. Diameter 3, so it is valid for any D >= 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C tabu search over bi-Cayley lifts.
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # The C search needs d >= 3 and D >= 3 to be useful. Give it nearly all
    # of the budget; the margin covers process start, compile cache and
    # Python-side parsing and validation.
    if d >= 3 and D >= 3:
        remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
        if remaining >= 2.0:
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
