import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs over semidirect products Z_m x| Z_k2.
#
# Group elements are coded as a*K2 + b for (a, b) in Z_M x| Z_K2 with
# (a, b)(c, e) = (a + R^b c, b + e). For a connection set S of DEG distinct
# group elements, the bi-Cayley graph has A-vertices x and B-vertices y, with
# A_x adjacent to B_{x s} for every s in S. Each vertex has degree DEG, and the
# graph is bipartite with 2|G| vertices.
#
# Left multiplication is an automorphism that preserves both sides, so the
# diameter is at most D iff BFS of depth D from A_e and from B_e reaches
# everything. WLOG the identity lies in S (relabel B by a right translation).
#
# Search: for a random group order g in [gmin, gmax], choose a random
# semidirect structure, then run simulated annealing on S. The cost is the
# number of uncovered vertices from the two BFS sources. Cost 0 gives a valid
# graph of order 2g.
#
# This differs from the voltage-lift annealer: the base is one pair of
# vertices, the group is searched directly, and the cost is evaluated with
# two BFS runs per move.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 32
#define ITERS 15000

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
static int G, M, K2, R;
static int *mt = NULL, *iv = NULL, *Rp = NULL;
static int *stamp = NULL, *queue = NULL, *inS = NULL;
static int curst = 0;
static int S[MAXDEG], IS[MAXDEG];

static int best_out = 0;
static int *out_e = NULL;
static int out_m = 0;

/* (a,b)(c,e) = (a + R^b c, b + e), element index a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rp[b] * c) % M);
    return ra * K2 + (b + e) % K2;
}

static void free_group(void) {
    free(mt); free(iv); free(Rp); free(stamp); free(queue); free(inS);
    mt = iv = Rp = stamp = queue = inS = NULL;
}

static void build_group(int m, int k2, int r) {
    free_group();
    M = m; K2 = k2; R = r; G = m * k2;
    Rp = malloc(sizeof(int) * (size_t)K2);
    Rp[0] = 1 % M;
    for (int b = 1; b < K2; b++) Rp[b] = (int)((long long)Rp[b - 1] * R % M);
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[(size_t)x * G + y] = gmul(x, y);
    iv = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        int nb = (K2 - b) % K2;             /* R^{-b} = R^{K2-b} since R^{K2} = 1 */
        int na = (int)((M - (long long)Rp[nb] * a % M) % M);
        iv[x] = na * K2 + nb;
    }
    stamp = calloc((size_t)2 * G, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)2 * G);
    inS = calloc((size_t)G, sizeof(int));
    curst = 0;
}

/* Uncovered vertices after BFS of depth DIAM from src (node ids: A_x = x, B_y = G + y). */
static int bfs_uncov(int src) {
    if (curst > 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)2 * G);
        curst = 0;
    }
    curst++;
    int head = 0, tail = 0;
    queue[tail++] = src;
    stamp[src] = curst;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int levelEnd = tail;
        if (head == levelEnd) break;
        while (head < levelEnd) {
            int v = queue[head++];
            if (v < G) {
                const int *row = mt + (size_t)v * G;
                for (int i = 0; i < DEG; i++) {
                    int w = G + row[S[i]];
                    if (stamp[w] != curst) { stamp[w] = curst; queue[tail++] = w; }
                }
            } else {
                const int *row = mt + (size_t)(v - G) * G;
                for (int i = 0; i < DEG; i++) {
                    int w = row[IS[i]];
                    if (stamp[w] != curst) { stamp[w] = curst; queue[tail++] = w; }
                }
            }
        }
    }
    return 2 * G - tail;
}

static int eval_cost(void) {
    return bfs_uncov(0) + bfs_uncov(G);
}

static void set_elem(int i, int g) {
    S[i] = g;
    IS[i] = iv[g];
}

static void random_set(void) {
    memset(inS, 0, sizeof(int) * (size_t)G);
    set_elem(0, 0);
    inS[0] = 1;
    for (int i = 1; i < DEG; i++) {
        int g;
        do { g = rnd_int(G); } while (inS[g]);
        inS[g] = 1;
        set_elem(i, g);
    }
}

static void emit(const int *Ss) {
    if (2 * G <= best_out) return;
    int m = G * DEG;
    best_out = 2 * G;
    out_m = m;
    free(out_e);
    out_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int x = 0; x < G; x++) {
        for (int i = 0; i < DEG; i++) {
            out_e[idx++] = x;
            out_e[idx++] = G + mt[(size_t)x * G + Ss[i]];
        }
    }
}

/* Simulated annealing over S (identity fixed in slot 0). Returns best uncovered count. */
static int run_group(int iters) {
    random_set();
    int cur = eval_cost();
    int bestc = cur;
    int bestS[MAXDEG];
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 127) == 0 && elapsed() > DEADLINE) break;
        double temp = 1.5 * (1.0 - (double)it / iters) + 0.05;
        int i = 1 + rnd_int(DEG - 1);
        int old = S[i], g;
        do { g = rnd_int(G); } while (inS[g]);
        inS[old] = 0;
        inS[g] = 1;
        set_elem(i, g);
        int c2 = eval_cost();
        int dl = c2 - cur;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / temp)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            inS[g] = 0;
            inS[old] = 1;
            set_elem(i, old);
        }
    }
    if (bestc == 0) emit(bestS);
    return bestc;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed time_limit gmin gmax\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int gmin = atoi(argv[5]), gmax = atoi(argv[6]);
    if (gmin < 2) gmin = 2;
    if (gmax < gmin) gmax = gmin;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int g = gmin + rnd_int(gmax - gmin + 1);
        if (g <= DEG) continue;
        int divs[64], nd = 0;
        for (int c = 1; c <= g && nd < 64; c++)
            if (g % c == 0 && g / c >= 2) divs[nd++] = c;
        if (nd == 0) continue;
        int k2 = divs[rnd_int(nd)];
        int m = g / k2, r = 1;
        if (k2 > 1) {
            for (int tr = 0; tr < 300; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                    r = cand;
                    break;
                }
            }
        }
        build_group(m, k2, r);
        run_group(ITERS);
    }

    if (best_out > 0) {
        printf("%d %d\n", best_out, out_m);
        for (int i = 0; i < out_m; i++)
            printf("%d %d\n", out_e[2 * i], out_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    free_group();
    free(out_e);
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
# Driver: baselines in Python, then the C bi-Cayley search over groups of
# order in a window just below half the target order.
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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    elapsed = time.monotonic() - start
    remaining = 0.9 * time_limit - elapsed - 1.5
    if remaining >= 1.0 and d >= 2:
        # Group orders g give graphs of order 2g. Search a window that starts
        # near the expected record ratio (about 0.44 of the Moore bound) and
        # stays above the current baseline.
        guess = int(0.40 * moore / 2)
        gmin = max(best_n // 2 + 1, guess, d + 1)
        gmax = gmin + gmin // 4 + 3
        hard = min(remaining + 3.0, time_limit - elapsed - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", gmin, gmax],
                            timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
