import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley and voltage lifts over explicit finite groups.
#
# Groups are semidirect products Z_m x| Z_k (k = 1 gives cyclic groups, r = 1
# gives direct products Z_m x Z_k). The full multiplication table is built, so
# the search does not depend on a closed-form product.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h. Dart t = (i, j, s)
# joins A_{i,g} to B_{j, g*s} for all g. Each layer is a permutation of the K
# A-vertices onto the K B-vertices, so every vertex has degree DEG and the
# graph is bipartite.
#
# Symmetry: left multiplication is an automorphism. Diameter <= D therefore
# holds iff a BFS of depth D from each of the 2K block representatives covers
# all vertices. For K = 1, right-translating the B side lets us fix the first
# connection element to the identity, which cuts the search space.
#
# Search: simulated annealing on the number of uncovered ordered pairs, with a
# fresh random group and configuration for each run. Zero cost means a valid
# lift, and it is kept if it beats the current best order.
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
#define GMAX 1500

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

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int DEG, DIAM, K, G, T, N;
static int *mt = NULL;           /* G*G multiplication table, identity = 0 */
static int *Rp = NULL;
static int *dI = NULL, *dJ = NULL, *dS = NULL;
static int *bJ = NULL, *bS = NULL;
static int *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int curstamp = 0;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

/* Semidirect product Z_m x| Z_k with (a,b)*(c,e) = (a + r^b c, b + e), index a*k + b. */
static void build_group(int m, int k, int r) {
    G = m * k;
    free(mt);
    free(Rp);
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    Rp = malloc(sizeof(int) * (size_t)k);
    Rp[0] = 1 % m;
    for (int b = 1; b < k; b++) Rp[b] = (int)((long long)Rp[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int ra = (int)(((long long)a + (long long)Rp[b] * c) % m);
            int rb = (b + e) % k;
            mt[(size_t)x * G + y] = ra * k + rb;
        }
    }
}

static void alloc_cfg(int k) {
    K = k;
    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    curstamp = 0;
}

static void free_cfg(void) {
    free(dI); free(dJ); free(dS); free(bJ); free(bS);
    free(adj); free(cnt); free(stamp); free(fr); free(nx);
    dI = dJ = dS = bJ = bS = NULL;
    adj = cnt = stamp = fr = nx = NULL;
}

/* Returns the number of uncovered ordered pairs over block representatives,
   or BIGC if two darts coincide (a multi-edge). */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G, s = dS[t];
        for (int g = 0; g < G; g++) {
            int a = ai + g;
            int b = bj + mt[(size_t)g * G + s];
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
    if (K == 1) dS[0] = 0;  /* normalisation: first connection element is the identity */
}

/* Annealing on the uncovered-pair count. Returns the best cost seen, with the
   best configuration stored in bJ / bS. */
static long long run_sa(int iters) {
    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    int mstart = (K == 1) ? 1 : 0;
    int nmov = T - mstart;
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double f = (double)it / (double)iters;
        double temp = 3.0 * (1.0 - f) + 0.05;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = mstart + rnd_int(nmov);
            int old = dS[t];
            int nw = rnd_int(G);
            if (nw == old) continue;
            dS[t] = nw;
            long long c2 = eval_cost();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                dS[t] = old;
            }
        }
        if (cur < bestc) {
            bestc = cur;
            memcpy(bJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

/* Store the lift defined by (J, S) with the current dI, group and K as the best graph. */
static void emit_cfg(const int *J, const int *S) {
    int m = T * G;
    int n = 2 * K * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + J[t]) * G + mt[(size_t)g * G + S[t]];
        }
    }
    best_m = m;
    best_n = n;
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
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[4] = {1, 1, 1, 2};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(4)];
        int gmin = best_n / (2 * k) + 1;
        if (gmin < 2) gmin = 2;
        int spread = gmin / 5 + 3;
        int g = gmin + (int)(spread * rnd_unit() * rnd_unit());
        if (g > GMAX) g = GMAX;
        if (g < 2) g = 2;

        /* Choose the group: cyclic, or Z_m x| Z_kk with a random valid r. */
        int m = g, kk = 1, r = 1;
        if (rnd_unit() < 0.7) {
            int opts[12], no = 0;
            for (int c = 2; c <= 12; c++)
                if (g % c == 0 && g / c >= 2) opts[no++] = c;
            if (no > 0) {
                kk = opts[rnd_int(no)];
                m = g / kk;
                int found = 0;
                for (int tr = 0; tr < 300 && !found; tr++) {
                    int cand = 1 + rnd_int(m - 1);
                    if (gcd_i(cand, m) == 1 && powmod(cand, kk, m) == 1 % m) {
                        r = cand;
                        found = 1;
                    }
                }
                if (!found) r = 1;  /* direct product Z_m x Z_kk */
            }
        }
        if (kk == 1) { m = g; r = 1; }

        build_group(m, kk, r);
        alloc_cfg(k);
        random_init();
        long long bc = run_sa(ITERS);
        if (bc == 0 && 2 * K * G > best_n) {
            emit_cfg(bJ, bS);
        }
        free_cfg();
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
# Python baselines and driver.
# ----------------------------------------------------------------------------

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

    # Spend most of the budget in C. The margin covers compilation,
    # parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.0
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
