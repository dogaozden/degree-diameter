import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Different construction family from the parent (which searches metacyclic
# groups Z_m x| Z_k): ABELIAN bi-Cayley (voltage) lifts over Z_m1 x Z_m2,
# including non-cyclic groups, with K base vertices per side.
#
# Vertices: A_{i,x} = i*G + x and B_{j,y} = (K+j)*G + y, with x, y in the group.
# Layer l uses a permutation p_l of the K base indices, and dart t = l*K + i
# joins A_{i,x} to B_{p_l(i), x + s_t} for all x. Every vertex gets degree DEG.
# Translation by any group element is an automorphism that acts transitively
# on each side, so diameter <= D iff BFS of depth D from A_0 and from B_0
# (one source per block representative) reaches every vertex.
#
# Search: simulated annealing over the voltages s_t and the layer permutations,
# minimising the number of uncovered (source, target) pairs. Duplicate darts
# are penalised. Each zero-cost state with order above the current best is
# emitted immediately. Group orders are sampled just above the current best,
# and abelian factorisations Z_m1 x Z_m2 are chosen at random.
#
# Safety: the Python driver starts from K_{d,d} (or a projective-plane or
# quadrangle incidence graph when available), passes the best known order to C
# so that only strictly larger valid graphs are emitted, and re-validates the
# result with lib.is_valid. The fallback is always returned if anything fails.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 15000
#define TEMP0 1.2

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static int DEG, DIAM;
static int K, M1, M2, G, T, N;
static int *ADD;
static int *dI, *dJ, *dS, *bJ, *bS;
static int *adj, *cnt, *stamp, *fr, *nx;
static int curstamp;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

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

static void setup(int k, int m1, int m2) {
    K = k; M1 = m1; M2 = m2;
    G = m1 * m2;
    N = 2 * K * G;
    T = DEG * K;
    ADD = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++) {
        int a1 = x / M2, b1 = x % M2;
        for (int y = 0; y < G; y++) {
            int a2 = y / M2, b2 = y % M2;
            ADD[(size_t)x * G + y] = ((a1 + a2) % M1) * M2 + (b1 + b2) % M2;
        }
    }
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
    for (int t = 0; t < T; t++) dI[t] = t % K;
    curstamp = 0;
}

static void free_all(void) {
    free(ADD);
    free(dI); free(dJ); free(dS); free(bJ); free(bS);
    free(adj); free(cnt); free(stamp); free(fr); free(nx);
    ADD = NULL;
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
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
}

/* Number of uncovered (source, vertex) pairs over the 2K block representatives.
   Returns 0 iff the lift has diameter <= DIAM. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G, s = dS[t];
        for (int x = 0; x < G; x++) {
            int a = ai + x;
            int b = bj + ADD[(size_t)x * G + s];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        int src = r * G;
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

static void emit_current(void) {
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int x = 0; x < G; x++) {
            best_e[idx++] = dI[t] * G + x;
            best_e[idx++] = (K + dJ[t]) * G + ADD[(size_t)x * G + dS[t]];
        }
    }
    best_m = m;
    best_n = N;
}

/* Simulated annealing on the uncovered-pair count. Returns the best cost seen;
   the best configuration is left in bJ/bS. */
static long long run_sa(void) {
    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < ITERS && bestc > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        double temp = TEMP0 * (1.0 - (double)it / ITERS) + 0.03;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
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
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            long long c2 = eval_cost();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                dS[t] = olds;
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int k = (rnd_unit() < 0.6) ? 1 : 2;
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 8 + 3;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int divs[64], nd = 0;
        for (int c = 1; c <= g && nd < 64; c++)
            if (g % c == 0) divs[nd++] = c;
        int m2 = divs[rnd_int(nd)];
        if (nd > 1 && rnd_unit() < 0.7) m2 = divs[1 + rnd_int(nd - 1)];
        int m1 = g / m2;
        setup(k, m1, m2);
        random_init();
        long long bc = run_sa();
        if (bc == 0) {
            memcpy(dJ, bJ, sizeof(int) * (size_t)T);
            memcpy(dS, bS, sizeof(int) * (size_t)T);
            if (eval_cost() == 0 && N > best_n) emit_current();
        }
        free_all();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    free(best_e);
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
# Driver: baselines in Python, then the C abelian bi-Cayley search.
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

    # Give the C search nearly all of the budget, leaving margin for process
    # start, parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
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
