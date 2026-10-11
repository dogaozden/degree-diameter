import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: lifts of a semidirect product group G = Z_m x| Z_k2 over a base
# with K A-vertices and K B-vertices. Each dart (layer l, index i) joins
# A_{i,g} to B_{j,s*g*u} for all g, where j = perm_l(i). Each layer is a
# bijection, so every vertex has degree DEG. Simulated annealing minimises the
# number of unreached ordered pairs within distance DIAM plus a penalty for
# parallel edges.
#
# Two modes per run:
#   TW = 0: u = identity. Left multiplication is an automorphism, so BFS from
#           the 2K block representatives suffices (fast).
#   TW = 1: twisted lift with right voltages u. Left multiplication is no longer
#           an automorphism, so BFS runs from every vertex (slow, but a larger
#           family of graphs).
# Runs climb: each success raises the target group order above the new best.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define V_ITERS 60000
#define TW_ITERS 6000

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

static int DEG, DIAM, K, K2, M, R, G, N, T, TW;
static int *Rpow;
static int *dI, *dJ, *gs, *gu, *P, *adj, *cnt, *stamp, *fr, *nx;
static int *bJ, *bS, *bU;
static int curst;
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

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*K2 + b, identity 0. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_row(int t) {
    int *row = P + (size_t)t * G;
    for (int g = 0; g < G; g++) row[g] = gmul(gmul(gs[t], g), gu[t]);
}

static int build_adj(void) {
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G;
        const int *row = P + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + row[g];
            if (cnt[a] >= DEG || cnt[b] >= DEG) return 0;
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    return 1;
}

static int count_dups(void) {
    int d = 0;
    for (int v = 0; v < N; v++) {
        const int *a = adj + (size_t)v * DEG;
        for (int x = 0; x < DEG; x++)
            for (int y = x + 1; y < DEG; y++)
                if (a[x] == a[y]) d++;
    }
    return d;
}

static int bfs_count(int src) {
    if (curst >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)N);
        curst = 0;
    }
    curst++;
    int *f = fr, *h = nx;
    int fs = 1, reached = 1;
    f[0] = src;
    stamp[src] = curst;
    for (int lv = 0; lv < DIAM && fs > 0; lv++) {
        int ns = 0;
        for (int q = 0; q < fs; q++) {
            const int *au = adj + (size_t)f[q] * DEG;
            for (int e = 0; e < DEG; e++) {
                int v = au[e];
                if (stamp[v] != curst) {
                    stamp[v] = curst;
                    h[ns++] = v;
                }
            }
        }
        reached += ns;
        int *tmp = f; f = h; h = tmp;
        fs = ns;
    }
    return reached;
}

/* Cost 0 iff the lift is simple, connected and has diameter <= DIAM. */
static long long eval_cost(void) {
    if (!build_adj()) return (long long)N * 1000000LL;
    int dup = count_dups();
    int nsrc = TW ? N : 2 * K;
    long long unc = 0;
    for (int r = 0; r < nsrc; r++) {
        int src = TW ? r : r * G;
        unc += N - bfs_count(src);
    }
    if (dup) return unc + 4LL * dup * N + 1;
    return unc;
}

static void setup(int k, int k2, int m, int r, int tw) {
    K = k; K2 = k2; M = m; R = r; G = m * k2;
    N = 2 * K * G;
    T = DEG * K;
    TW = tw;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    gs = malloc(sizeof(int) * (size_t)T);
    gu = malloc(sizeof(int) * (size_t)T);
    P = malloc(sizeof(int) * (size_t)T * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    bJ = malloc(sizeof(int) * (size_t)T);
    bS = malloc(sizeof(int) * (size_t)T);
    bU = malloc(sizeof(int) * (size_t)T);
    curst = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    for (int t = 0; t < T; t++) dI[t] = t % K;
}

static void free_all(void) {
    free(dI); free(dJ); free(gs); free(gu); free(P); free(adj); free(cnt);
    free(stamp); free(fr); free(nx); free(Rpow); free(bJ); free(bS); free(bU);
}

static void random_init(void) {
    int p[16];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) dJ[l * K + i] = p[i];
    }
    for (int t = 0; t < T; t++) {
        gs[t] = rnd_int(G);
        gu[t] = TW ? rnd_int(G) : 0;
    }
    for (int t = 0; t < T; t++) build_row(t);
}

static void save_best(void) {
    memcpy(bJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bS, gs, sizeof(int) * (size_t)T);
    memcpy(bU, gu, sizeof(int) * (size_t)T);
}

static long long run_sa(int iters, long long cost, double tscale) {
    long long bestc = cost;
    save_best();
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        double f = (double)it / (double)iters;
        double temp = tscale * (3.0 * (1.0 - f) + 0.05);
        int mv = rnd_int(100);
        if (mv < 35) {
            /* Swap two base targets inside one layer (keeps the layer a bijection). */
            int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else if (TW && mv < 65) {
            /* Change a right voltage u. */
            int t = rnd_int(T);
            int old = gu[t], nw = rnd_int(G);
            if (nw == old) continue;
            gu[t] = nw; build_row(t);
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                gu[t] = old; build_row(t);
            }
        } else {
            /* Change a left voltage s. */
            int t = rnd_int(T);
            int old = gs[t], nw = rnd_int(G);
            if (nw == old) continue;
            gs[t] = nw; build_row(t);
            long long c2 = eval_cost();
            if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                gs[t] = old; build_row(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            save_best();
        }
    }
    return bestc;
}

static void emit_best(void) {
    /* Load the best configuration and write its edge list. */
    memcpy(dJ, bJ, sizeof(int) * (size_t)T);
    memcpy(gs, bS, sizeof(int) * (size_t)T);
    memcpy(gu, bU, sizeof(int) * (size_t)T);
    for (int t = 0; t < T; t++) build_row(t);
    int m = T * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < T; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (K + dJ[t]) * G + P[(size_t)t * G + g];
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
    best_n = argc > 5 ? atoi(argv[5]) : 0;
    best_m = 0;
    if (DEG < 1 || DIAM < 1 || DEG > 12) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    static const int kc[7] = {1, 1, 2, 2, 2, 3, 4};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(7)];
        int tw = rnd_unit() < 0.35;
        int gmin = best_n / (2 * k) + 1;
        int spread = gmin / 8 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[16], no = 0;
        for (int c = 1; c <= 12; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = no ? opts[rnd_int(no)] : 1;
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
        setup(k, c2, m, r, tw);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(tw ? TW_ITERS : V_ITERS, cost, 1.0);
        if (bc == 0 && N > best_n) emit_best();
        free_all();
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
# Safe baseline families (always valid, used as fallback).
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
# Driver: baselines in Python, then one C run (group lifts, twisted and untwisted).
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

    # The C deadline starts after compilation, so reserve 2 s for compile,
    # parsing and validation.
    remaining = 0.93 * time_limit - (time.monotonic() - start) - 2.0
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
