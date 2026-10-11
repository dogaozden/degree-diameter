import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bipartite Cayley-type graphs (Haar-style lifts) over
# semidirect products Z_m x| Z_k2, with a single base pair (A, B).
#
# Vertices: A_g = g and B_h = G + h, where G = m*k2 is the group order.
# A connection set S = {s_1..s_d} of distinct group elements gives edges
# A_g -- B_{g*s} for every g and every s in S. This is d-regular and simple.
#
# Left multiplication is an automorphism of each side, so diameter <= D iff
# BFS of depth D from A_e and from B_e covers everything. The C engine
# searches over connection sets with tabu search: a move replaces one element
# of S with a sampled non-member, the cost is the number of uncovered vertices
# from the two representatives, and removed elements are tabu for a while.
# Group orders are chosen just above (record / 2), so a success is a strictly
# larger valid graph. This replaces the earlier voltage-annealing search.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <time.h>

#define GMAX 2200
#define DMAX 64
#define NB 80
#define TENURE 6
#define STEPS 3000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;
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

/* Group state: element index a*K2 + b, product (a,b)(c,e) = (a + R^b c, b + e). */
static int G, M, K2, R;
static int *mulT = NULL, *invT = NULL;
static int Rpow[DMAX];

/* Connection set and its inverses. */
static int S[DMAX], Si[DMAX], SD;
static char member[GMAX];
static int tabu_until[GMAX];

static int stamp_arr[2 * GMAX];
static int frbuf[2 * GMAX], nxbuf[2 * GMAX];
static int cur_stamp = 0;

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void setup_group(int m, int k2, int r) {
    M = m; K2 = k2; R = r; G = m * k2;
    Rpow[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        invT[x] = -1;
        for (int y = 0; y < G; y++)
            if (mulT[(size_t)x * G + y] == 0) { invT[x] = y; break; }
    }
}

/* Number of vertices within DIAM of src. Vertices: A_g = g (g < G), B_h = G + h. */
static int bfs_cov(int src) {
    cur_stamp++;
    if (cur_stamp == INT_MAX) {
        memset(stamp_arr, 0, sizeof(stamp_arr));
        cur_stamp = 1;
    }
    int *f = frbuf, *h = nxbuf;
    int fsz = 1, cnt = 1;
    f[0] = src;
    stamp_arr[src] = cur_stamp;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < G) {
                const int *row = mulT + (size_t)v * G;
                for (int t = 0; t < SD; t++) {
                    int u = G + row[S[t]];
                    if (stamp_arr[u] != cur_stamp) {
                        stamp_arr[u] = cur_stamp;
                        h[nsz++] = u;
                    }
                }
            } else {
                const int *row = mulT + (size_t)(v - G) * G;
                for (int t = 0; t < SD; t++) {
                    int u = row[Si[t]];
                    if (stamp_arr[u] != cur_stamp) {
                        stamp_arr[u] = cur_stamp;
                        h[nsz++] = u;
                    }
                }
            }
        }
        cnt += nsz;
        int *tmp = f; f = h; h = tmp;
        fsz = nsz;
    }
    return cnt;
}

static int cost_of(void) {
    return (2 * G - bfs_cov(0)) + (2 * G - bfs_cov(G));
}

/* Tabu search over connection sets of SD distinct elements. Returns 1 on cost 0. */
static int run_tabu(int maxsteps) {
    memset(member, 0, (size_t)G);
    for (int t = 0; t < SD; t++) {
        int x;
        do { x = rnd_int(G); } while (member[x]);
        member[x] = 1;
        S[t] = x;
        Si[t] = invT[x];
    }
    memset(tabu_until, 0, sizeof(int) * (size_t)G);
    int c = cost_of();
    int bestc = c;
    for (int step = 0; step < maxsteps && c > 0; step++) {
        if ((step & 7) == 0 && elapsed() > DEADLINE) return 0;
        int bm = INT_MAX, bp = -1, bx = -1;
        for (int s = 0; s < NB; s++) {
            int p = rnd_int(SD), x = rnd_int(G);
            if (member[x]) continue;
            int old = S[p], oldi = Si[p];
            S[p] = x; Si[p] = invT[x];
            int cc = cost_of();
            S[p] = old; Si[p] = oldi;
            if (tabu_until[x] > step && cc >= bestc) continue;
            if (cc < bm) { bm = cc; bp = p; bx = x; }
        }
        if (bp < 0) continue;
        int out = S[bp];
        member[out] = 0;
        tabu_until[out] = step + TENURE + rnd_int(TENURE + 1);
        S[bp] = bx; Si[bp] = invT[bx]; member[bx] = 1;
        c = bm;
        if (c < bestc) bestc = c;
    }
    return c == 0;
}

static void emit_current(void) {
    int m = G * SD;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int t = 0; t < SD; t++) {
        for (int g = 0; g < G; g++) {
            best_e[idx++] = g;
            best_e[idx++] = G + mulT[(size_t)g * G + S[t]];
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
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    SD = DEG;
    if (DEG < 1 || DEG > DMAX || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    mulT = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    invT = malloc(sizeof(int) * (size_t)GMAX);

    static const int ks[8] = {1, 1, 1, 2, 2, 3, 4, 6};
    while (elapsed() < DEADLINE) {
        int lo = best_n / 2 + 1;
        if (lo < DEG) lo = DEG;
        if (lo < 2) lo = 2;
        int Gc = lo + rnd_int(12);
        if (Gc > GMAX) break;
        int k2 = ks[rnd_int(8)];
        if (Gc % k2 != 0 || Gc / k2 < 2) k2 = 1;
        int m = Gc / k2, r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) { k2 = 1; m = Gc; r = 1; }
        } else {
            m = Gc; r = 1;
        }
        if (m < DEG) continue;
        setup_group(m, k2, r);
        int ok = 0;
        for (int rep = 0; rep < 3 && !ok && elapsed() < DEADLINE; rep++)
            ok = run_tabu(STEPS);
        if (ok && 2 * G > best_n) emit_current();
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
# Driver: baselines in Python, then the C tabu search over Cayley-type lifts.
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

    # Give the C search nearly all of the budget. The margin covers process
    # start, the cached compile step, parsing and validation in Python.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
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
