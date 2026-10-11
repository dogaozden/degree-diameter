import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: Haar graphs over groups.
#
# For a finite group G and a connection set S = {s_1..s_d} of distinct elements,
# H(G, S) has vertices A_g and B_x (g, x in G) and edges A_g -- B_{g*s} for s in S.
# It is bipartite and d-regular with 2|G| vertices. Left multiplication is an
# automorphism, so the diameter is at most D iff BFS of depth D from A_e and from
# B_e reaches everything. Two BFS runs per evaluation make the search cheap.
#
# The groups are semidirect products Z_m x| Z_k (element (a,b) coded as a*k+b,
# (a,b)(c,e) = (a + r^b c, b+e), r^k = 1 mod m). The C engine searches random
# groups of order just above half the best known vertex count, and anneals S to
# minimise the number of unreachable pairs from the two BFS sources.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GMAX 1400
#define MAXDEG 200
#define ITERS 40000
#define TRIES_R 200

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
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int DEG, DIAM, G, M, K2, R;
static int *mt = NULL, *invt = NULL, *Rpow = NULL;
static int *stamp = NULL, *fr = NULL, *nx = NULL;
static int S[MAXDEG], Sinv[MAXDEG], bestS[MAXDEG];
static int curstamp = 0;
static double DEADLINE;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

static void free_group(void) {
    free(mt); free(invt); free(Rpow); free(stamp); free(fr); free(nx);
    mt = invt = Rpow = stamp = fr = nx = NULL;
}

static void build_group(int m, int k, int r) {
    M = m; K2 = k; R = r; G = m * k;
    mt = malloc(sizeof(int) * (size_t)G * G);
    invt = malloc(sizeof(int) * (size_t)G);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    stamp = calloc((size_t)2 * G, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * G);
    nx = malloc(sizeof(int) * (size_t)2 * G);
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        for (int y = 0; y < G; y++) {
            int c = y / K2, e = y % K2;
            int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
            int rb = (b + e) % K2;
            mt[(size_t)x * G + y] = ra * K2 + rb;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mt[(size_t)x * G + y] == 0) invt[x] = y;
}

/* Unreached-pair count from A_e (vertex 0) and B_e (vertex G), depth DIAM. */
static long long eval_cost(void) {
    int N = 2 * G;
    long long total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = (src == 0) ? 0 : G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = s0;
        stamp[s0] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                int v = f[q];
                if (v < G) {
                    for (int t = 0; t < DEG; t++) {
                        int w = G + mt[(size_t)v * G + S[t]];
                        if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
                    }
                } else {
                    int x = v - G;
                    for (int t = 0; t < DEG; t++) {
                        int w = mt[(size_t)x * G + Sinv[t]];
                        if (stamp[w] != curstamp) { stamp[w] = curstamp; h[nsz++] = w; }
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

static void random_S(void) {
    for (int t = 0; t < DEG; t++) {
        for (;;) {
            int c = rnd_int(G), ok = 1;
            for (int u = 0; u < t; u++) if (S[u] == c) { ok = 0; break; }
            if (ok) { S[t] = c; break; }
        }
    }
    for (int t = 0; t < DEG; t++) Sinv[t] = invt[S[t]];
}

/* Simulated annealing over the connection set. Best set goes to bestS. */
static long long anneal(void) {
    random_S();
    long long cost = eval_cost(), bc = cost;
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < ITERS && bc > 0; it++) {
        if ((it & 127) == 0 && now() > DEADLINE) break;
        double temp = 2.0 * (1.0 - (double)it / ITERS) + 0.05;
        int pos = rnd_int(DEG);
        int nw = rnd_int(G), dup = 0;
        for (int t = 0; t < DEG; t++) if (S[t] == nw) { dup = 1; break; }
        if (dup) continue;
        int old = S[pos];
        S[pos] = nw; Sinv[pos] = invt[nw];
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bc) {
                bc = cost;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            S[pos] = old; Sinv[pos] = invt[old];
        }
    }
    return bc;
}

/* Haar graph H(G, bestS): A_g = g, B_x = G + x, edges A_g -- B_{g s}. */
static void emit(void) {
    int m = G * DEG;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int g = 0; g < G; g++) {
        for (int t = 0; t < DEG; t++) {
            best_e[idx++] = g;
            best_e[idx++] = G + mt[(size_t)g * G + S[t]];
        }
    }
    best_m = m;
    best_n = 2 * G;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
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
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (now() < DEADLINE) {
        int lo = best_n / 2 + 1;
        if (lo < DEG + 1) lo = DEG + 1;
        if (lo > GMAX) break;
        int span = lo / 12 + 3;
        int g = lo + rnd_int(span);
        if (g > GMAX) g = GMAX;
        int divs[256], nd = 0;
        for (int c = 1; c <= g && nd < 256; c++) if (g % c == 0) divs[nd++] = c;
        int k = divs[rnd_int(nd)];
        int m = g / k, r = 1;
        if (k > 1 && m > 1) {
            int found = 0;
            for (int tr = 0; tr < TRIES_R && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) continue;
        } else if (k > 1) {
            r = 0;
        }
        if (g < DEG + 1 || g > GMAX) continue;
        build_group(m, k, r);
        long long bc = anneal();
        if (bc == 0) {
            memcpy(S, bestS, sizeof(int) * (size_t)DEG);
            for (int t = 0; t < DEG; t++) Sinv[t] = invt[S[t]];
            if (2 * G > best_n) emit();
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
# Safe Python baselines.
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
# Driver: Python baselines first, then the C Haar-graph annealer on semidirect groups.
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

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.5
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
