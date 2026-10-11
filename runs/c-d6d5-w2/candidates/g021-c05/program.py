import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: single-orbit bi-Cayley graphs (generalised Haar graphs).
#
# Group G = Z_M x|_R Z_K, element (a,b) coded as a*K+b, with
#   (a,b)*(c,e) = (a + R^b c, b+e)   and   R^K = 1 (mod M).
# Vertices: A_x = x and B_y = G + y. Connection set S = {s_0..s_{DEG-1}}
# (distinct group elements) gives edges A_x -- B_{x s} for every s in S.
# Each vertex has degree DEG, the graph is bipartite, and left multiplication
# is an automorphism that is transitive on A and on B. So the diameter is at
# most DIAM iff BFS of depth DIAM from A_0 and from B_0 reaches everything.
#
# Search: for a target group order g (with 2g vertices per graph), pick a random
# group of order g (cyclic or semidirect), then anneal the DEG connection
# elements to minimise the number of unreached vertices from A_0 and B_0.
# The target order climbs whenever a zero-cost set is found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 40000
#define SPREAD 4
#define MAXDIV 256

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

static int DEG, DIAM;
static int M, K, R, G;
static int *Rpow = NULL;
static int *stamp = NULL, *fr = NULL, *nx = NULL;
static int curstamp = 0;
static int S[64], Sinv[64];
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_ll(long long b, int e, long long m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

/* Group multiplication (a,b)*(c,e) = (a + R^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K, b = x % K;
    int c = y / K, e = y % K;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = b + e;
    if (rb >= K) rb -= K;
    return ra * K + rb;
}

/* Inverse of (a,b) is (-R^(K-b) a, (K-b) mod K). */
static int ginv(int x) {
    int a = x / K, b = x % K;
    int e = (K - b) % K;
    long long c = (long long)Rpow[e] * a % M;
    c = (M - c) % M;
    return (int)c * K + e;
}

static int in_S(int g, int upto) {
    for (int i = 0; i < upto; i++) if (S[i] == g) return 1;
    return 0;
}

/* Number of vertices within DIAM of src (A-side src < G, B-side src >= G). */
static int bfs_count(int src) {
    if (curstamp >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)(2 * G));
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
            int u = f[q];
            if (u < G) {
                for (int t = 0; t < DEG; t++) {
                    int v = G + gmul(u, S[t]);
                    if (stamp[v] != curstamp) { stamp[v] = curstamp; h[nsz++] = v; }
                }
            } else {
                int y = u - G;
                for (int t = 0; t < DEG; t++) {
                    int v = gmul(y, Sinv[t]);
                    if (stamp[v] != curstamp) { stamp[v] = curstamp; h[nsz++] = v; }
                }
            }
        }
        count += nsz;
        int *tmp = f; f = h; h = tmp;
        fsz = nsz;
    }
    return count;
}

/* Unreached vertices from A_0 plus from B_0. Zero iff the graph has diameter <= DIAM. */
static int eval_cost(void) {
    int c0 = 2 * G - bfs_count(0);
    int c1 = 2 * G - bfs_count(G);
    return c0 + c1;
}

static void alloc_arrays(void) {
    free(Rpow); free(stamp); free(fr); free(nx);
    Rpow = malloc(sizeof(int) * (size_t)K);
    stamp = calloc((size_t)(2 * G), sizeof(int));
    fr = malloc(sizeof(int) * (size_t)(2 * G));
    nx = malloc(sizeof(int) * (size_t)(2 * G));
    curstamp = 0;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

/* Random group of order g: a random divisor split g = M*K, semidirect if a valid R exists. */
static void setup_group(int g) {
    int divs[MAXDIV], nd = 0;
    for (int c = 1; c <= g && nd < MAXDIV; c++) if (g % c == 0) divs[nd++] = c;
    int k = divs[rnd_int(nd)];
    int m = g / k;
    int r = 1;
    if (k > 1 && m > 1) {
        int found = 0;
        for (int tr = 0; tr < 300 && !found; tr++) {
            int cand = 1 + rnd_int(m - 1);
            if (gcd_i(cand, m) == 1 && powmod_ll(cand, k, m) == 1 % m) {
                r = cand;
                found = 1;
            }
        }
        if (!found) { k = 1; m = g; r = 1; }
    }
    M = m; K = k; R = r; G = m * k;
    alloc_arrays();
}

static void random_S(void) {
    for (int t = 0; t < DEG; t++) {
        int g;
        do { g = rnd_int(G); } while (in_S(g, t));
        S[t] = g;
        Sinv[t] = ginv(g);
    }
}

/* Simulated annealing on the connection set; returns the best cost, leaves S at the best state. */
static int run_sa(int iters) {
    int cur = eval_cost();
    int bestc = cur;
    int bestS[64];
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = 2.0 * (1.0 - frac) + 0.1;
        int i = rnd_int(DEG);
        int g = rnd_int(G);
        if (in_S(g, DEG)) continue;
        int old = S[i], oldinv = Sinv[i];
        S[i] = g;
        Sinv[i] = ginv(g);
        int c2 = eval_cost();
        int delta = c2 - cur;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / temp)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            S[i] = old;
            Sinv[i] = oldinv;
        }
    }
    memcpy(S, bestS, sizeof(int) * (size_t)DEG);
    for (int t = 0; t < DEG; t++) Sinv[t] = ginv(S[t]);
    return bestc;
}

static void emit(void) {
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)G * (size_t)DEG);
    int idx = 0;
    for (int x = 0; x < G; x++) {
        for (int t = 0; t < DEG; t++) {
            best_e[idx++] = x;
            best_e[idx++] = G + gmul(x, S[t]);
        }
    }
    best_m = G * DEG;
    best_n = 2 * G;
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
    if (DEG < 1 || DIAM < 1 || DEG > 60) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* A group of order g gives 2g vertices; we need 2g > best_n. */
    int lo = start_n / 2 + 1;
    if (lo < DEG) lo = DEG;

    while (elapsed() < DEADLINE) {
        int g = lo + rnd_int(SPREAD);
        setup_group(g);
        random_S();
        int bc = run_sa(ITERS);
        if (bc == 0 && 2 * G > best_n) {
            emit();
            lo = G + 1;
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
# Safe baseline families (valid for every case, used as fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d; diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Driver: baselines in Python, then the C bi-Cayley annealer.
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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget. Its deadline counts from process
    # start, so leave room for the cached compile, parsing and validation.
    elapsed = time.monotonic() - start
    remaining = 0.9 * time_limit - elapsed - 1.0
    if remaining >= 1.0:
        hard = min(remaining + 3.0, time_limit - elapsed - 1.5)
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
