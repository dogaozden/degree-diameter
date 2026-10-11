import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: Haar (Cayley-bipartite) graphs over semidirect products
# G = Z_M x| Z_K (element a*K+b, (a,b)(c,e) = (a + R^b c, b + e)).
#
# Vertices A_x = x and B_y = H + y, with H = |G|. Connection set S (DEG distinct
# elements) gives edges A_x -- B_{x s} for s in S. Every such graph is biregular
# of degree DEG and bipartite.
#
# Left multiplication is an automorphism that moves A_x to A_{gx} and B_y to
# B_{gy}. So the diameter is <= D iff BFS of depth D from A_0 and from B_0
# reaches every vertex. The cost is the number of unreached (source, target)
# pairs over those two BFS runs, and cost 0 means the graph is valid.
#
# Search: for a random group of order h slightly above the best so far,
# simulated annealing changes one element of S at a time. Success at order h
# raises the target. This is a different search space from voltage lifts.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 20000
#define TSTART 1.5
#define TEND 0.05

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

static int DEG, DIAM;
static int H, K, M, R;
static int *Rpow;
static int *Sel, *Sinv, *bestSel, *winS;
static int *adj;
static int *stamp, *fr, *nx;
static int curstamp;
static int have_win = 0;
static int winH = 0, winK = 1, winM = 0, winR = 1;

static void set_group(int k, int m, int r) {
    K = k; M = m; R = r;
    free(Rpow);
    Rpow = malloc(sizeof(int) * (size_t)K);
    Rpow[0] = 1 % M;
    for (int b = 1; b < K; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * R % M);
}

/* (a,b)*(c,e) = (a + R^b c, b + e), index a*K + b. */
static inline int gmul(int x, int y) {
    int a = x / K, b = x % K;
    int c = y / K, e = y % K;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K;
    return ra * K + rb;
}

/* Inverse of (a,b) is (-R^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    long long ca = (-((long long)Rpow[nb] * a)) % M;
    if (ca < 0) ca += M;
    return (int)ca * K + nb;
}

/* Recompute the edges contributed by connection element i. */
static void set_col(int i) {
    Sinv[i] = ginv(Sel[i]);
    for (int x = 0; x < H; x++) {
        adj[(size_t)x * DEG + i] = H + gmul(x, Sel[i]);
        adj[(size_t)(H + x) * DEG + i] = gmul(x, Sinv[i]);
    }
}

/* Number of vertices not reached from src within DIAM steps. */
static int bfs_unc(int src) {
    int N = 2 * H;
    curstamp++;
    if (curstamp >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)N);
        curstamp = 1;
    }
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
    return N - count;
}

static long long eval_cost(void) {
    return (long long)bfs_unc(0) + (long long)bfs_unc(H);
}

static int in_S(int v) {
    for (int i = 0; i < DEG; i++) if (Sel[i] == v) return 1;
    return 0;
}

/* Simulated annealing over the connection set. Best state goes to bestSel. */
static long long anneal(int iters) {
    long long cur = eval_cost();
    long long best = cur;
    memcpy(bestSel, Sel, sizeof(int) * (size_t)DEG);
    if (best == 0) return 0;
    for (int it = 0; it < iters; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / (double)iters;
        double temp = TSTART * (1.0 - frac) + TEND;
        int i = rnd_int(DEG);
        int nv = rnd_int(H);
        if (in_S(nv)) continue;
        int old = Sel[i];
        Sel[i] = nv;
        set_col(i);
        long long c = eval_cost();
        if (c <= cur || rnd_unit() < exp(-(double)(c - cur) / temp)) {
            cur = c;
            if (c < best) {
                best = c;
                memcpy(bestSel, Sel, sizeof(int) * (size_t)DEG);
                if (best == 0) break;
            }
        } else {
            Sel[i] = old;
            set_col(i);
        }
    }
    return best;
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int bestH = start_n / 2;
    Sel = malloc(sizeof(int) * (size_t)DEG);
    Sinv = malloc(sizeof(int) * (size_t)DEG);
    bestSel = malloc(sizeof(int) * (size_t)DEG);
    winS = malloc(sizeof(int) * (size_t)DEG);
    Rpow = NULL;

    while (elapsed() < DEADLINE) {
        int floorH = bestH + 1;
        if (floorH < DEG + 1) floorH = DEG + 1;
        int span = bestH / 40 + 3;
        int h = floorH + rnd_int(span);

        /* Pick a group of order h: Z_m x| Z_k with a random valid r, or cyclic. */
        int divs[64], nd = 0;
        for (int k = 2; k <= 12 && k <= h; k++)
            if (h % k == 0 && h / k >= 2) divs[nd++] = k;
        int k = 1, m = h, r = 1;
        if (nd > 0 && rnd_unit() < 0.85) {
            int kk = divs[rnd_int(nd)];
            int mm = h / kk;
            int found = 0, rr = 1;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(mm - 1);
                if (gcd_i(cand, mm) == 1 && powmod(cand, kk, mm) == 1 % mm) {
                    rr = cand;
                    found = 1;
                }
            }
            if (found) { k = kk; m = mm; r = rr; }
        }
        set_group(k, m, r);
        H = h;

        adj = malloc(sizeof(int) * (size_t)2 * H * DEG);
        stamp = calloc((size_t)2 * H, sizeof(int));
        fr = malloc(sizeof(int) * (size_t)2 * H);
        nx = malloc(sizeof(int) * (size_t)2 * H);
        curstamp = 0;

        for (int i = 0; i < DEG; i++) {
            int v, ok;
            do {
                v = rnd_int(H);
                ok = 1;
                for (int j = 0; j < i; j++) if (Sel[j] == v) ok = 0;
            } while (!ok);
            Sel[i] = v;
        }
        for (int i = 0; i < DEG; i++) set_col(i);

        long long c = anneal(ITERS);
        if (c == 0) {
            bestH = h;
            have_win = 1;
            winH = h;
            winK = K;
            winM = M;
            winR = R;
            memcpy(winS, bestSel, sizeof(int) * (size_t)DEG);
        }

        free(adj); free(stamp); free(fr); free(nx);
        adj = NULL; stamp = NULL; fr = NULL; nx = NULL;
    }

    if (have_win) {
        set_group(winK, winM, winR);
        H = winH;
        printf("%d %d\n", 2 * H, H * DEG);
        for (int x = 0; x < H; x++)
            for (int i = 0; i < DEG; i++)
                printf("%d %d\n", x, H + gmul(x, winS[i]));
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
# Driver: baselines in Python, then the C Haar-graph search over groups.
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

    # The C deadline starts after compile; reserve 2 s for compile, parsing and
    # validation, and keep the total well under time_limit.
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
