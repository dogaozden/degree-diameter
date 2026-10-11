import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley graphs over small groups.
#
# A graph has vertices A_g = g and B_x = G + x for g, x in a group of order G,
# and connection set S = {s_1..s_DEG} with distinct elements. Edge A_g -- B_{g s}.
# Left multiplication is an automorphism, so the graph has diameter <= DIAM iff
# BFS of depth DIAM from A_e and from B_e reaches everything. The cost is the
# number of unreached (source, vertex) pairs.
#
# Search: the order target grows monotonically. For each attempt, pick a random
# group of order G (cyclic, or Z_m x|_r Z_k), then run simulated annealing on S.
# On success the graph is emitted and the target moves up by one. Only groups
# with valid zero-cost sets are returned.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 64
#define ITERS 30000

static uint64_t rs[2];

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
static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int DEG, DIAM;
static double DEADLINE;

/* current group: element index a*KK + b, (a,b)(c,e) = (a + r^b c, b + e) */
static int G, MM, KK;
static int *RP = NULL, *MT = NULL, *INV = NULL;
static int *S = NULL, *SI = NULL;
static int *stamp = NULL, *bufA = NULL, *bufB = NULL;
static int curstamp = 0;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static int best_G = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(int x, int y) {
    int a = x / KK, b = x % KK;
    int c = y / KK, e = y % KK;
    long long ra = ((long long)a + (long long)RP[b] * c) % MM;
    int rb = (b + e) % KK;
    return (int)ra * KK + rb;
}

static void build_group(int m, int k, int r) {
    MM = m;
    KK = k;
    G = m * k;
    free(RP);
    RP = malloc(sizeof(int) * (size_t)k);
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long long)RP[b - 1] * r % m);

    free(MT);
    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MT[(size_t)x * G + y] = gmul(x, y);

    free(INV);
    INV = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        INV[x] = 0;
        for (int y = 0; y < G; y++)
            if (MT[(size_t)x * G + y] == 0) { INV[x] = y; break; }
    }

    free(stamp);
    free(bufA);
    free(bufB);
    stamp = calloc((size_t)(2 * G), sizeof(int));
    bufA = malloc(sizeof(int) * (size_t)(2 * G));
    bufB = malloc(sizeof(int) * (size_t)(2 * G));
    curstamp = 0;
}

static int bfs_count(int src) {
    if (curstamp >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)(2 * G));
        curstamp = 0;
    }
    curstamp++;
    int *f = bufA, *h = bufB;
    int fsz = 1, count = 1;
    f[0] = src;
    stamp[src] = curstamp;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < G) {
                /* A_g -- B_{g s} */
                const int *row = MT + (size_t)v * G;
                for (int t = 0; t < DEG; t++) {
                    int w = G + row[S[t]];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
                }
            } else {
                /* B_x -- A_{x s^-1} */
                const int *row = MT + (size_t)(v - G) * G;
                for (int t = 0; t < DEG; t++) {
                    int w = row[SI[t]];
                    if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
                }
            }
        }
        count += nsz;
        int *tmp = f; f = h; h = tmp;
        fsz = nsz;
    }
    return count;
}

static int cost_eval(void) {
    int N = 2 * G;
    return (N - bfs_count(0)) + (N - bfs_count(G));
}

static int used(int x, int upto) {
    for (int t = 0; t < upto; t++) if (S[t] == x) return 1;
    return 0;
}

static int anneal(void) {
    for (int t = 0; t < DEG; t++) {
        int x;
        do { x = rnd_int(G); } while (used(x, t));
        S[t] = x;
        SI[t] = INV[x];
    }
    int cost = cost_eval();
    int bestc = cost;
    for (int it = 0; it < ITERS && bestc > 0; it++) {
        if ((it & 255) == 0 && now_s() > DEADLINE) break;
        double temp = 1.2 * (1.0 - (double)it / ITERS) + 0.05;
        int t = rnd_int(DEG);
        int old = S[t], oldi = SI[t];
        int nw;
        do { nw = rnd_int(G); } while (used(nw, DEG));
        S[t] = nw;
        SI[t] = INV[nw];
        int c2 = cost_eval();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) bestc = cost;
        } else {
            S[t] = old;
            SI[t] = oldi;
        }
    }
    return cost;
}

static void emit_current(void) {
    int n = 2 * G, m = DEG * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < DEG; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = g;
            best_e[idx++] = G + MT[(size_t)g * G + S[t]];
        }
    best_n = n;
    best_m = m;
}

static void pick_group(int g, int *m_out, int *k_out, int *r_out) {
    static const int ks[4] = {2, 3, 4, 6};
    int k = 1;
    if (rnd_int(2) == 0) {
        int cand = ks[rnd_int(4)];
        if (g % cand == 0 && g / cand >= 2) k = cand;
    }
    int m = g / k, r = 1 % m;
    if (k > 1) {
        int found = 0;
        for (int tr = 0; tr < 300 && !found; tr++) {
            int c = 1 + rnd_int(m - 1);
            if (gcd_i(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = c;
                found = 1;
            }
        }
        if (!found) {
            k = 1;
            m = g;
            r = 1 % m;
        }
    }
    *m_out = m;
    *k_out = k;
    *r_out = r;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    DEADLINE = tl;

    S = malloc(sizeof(int) * (size_t)DEG);
    SI = malloc(sizeof(int) * (size_t)DEG);

    best_n = 0;
    best_m = 0;
    best_G = start_n / 2;
    if (best_G < DEG) best_G = DEG;

    while (now_s() < DEADLINE) {
        int g = best_G + 1 + rnd_int(4);
        int m, k, r;
        pick_group(g, &m, &k, &r);
        build_group(m, k, r);
        if (G <= DEG) continue;
        if (anneal() == 0) {
            emit_current();
            best_G = G;
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
# Driver: safe baselines first, then the C bi-Cayley annealer.
# ----------------------------------------------------------------------------

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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
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
