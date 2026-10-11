import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (Haar-type) graphs over metacyclic groups.
#
# Group G = Z_m x| Z_k with (a,b)(c,e) = (a + r^b c, b + e), order g = m*k.
# Vertices A_x = x and B_y = G + y. Connection set S of DEG distinct group
# elements: A_x ~ B_{x s} for each s in S. This is bipartite and DEG-regular.
#
# Left multiplication is an automorphism that fixes each side, so the diameter
# is at most D iff BFS of depth D from A_1 and from B_1 reaches everything.
# The cost is the number of unreached vertices from those two sources, so one
# evaluation costs about 4*G*DEG operations. Simulated annealing moves one
# element of S at a time. Each run uses a random group whose order sits just
# above the current record (ratchet: the order floor follows the best found).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 16
#define GMAX 1500
#define SA_ITERS 20000

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

static int DEG, DIAM, G, Mm, Kk, Rr;
static int *mulT = NULL, *invT = NULL, *Rpow = NULL;
static int *adj = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int curstamp = 0;
static int S[MAXDEG], invS[MAXDEG], bestS[MAXDEG];
static int start_n, best_n;
static int *best_e = NULL;
static int best_m = 0;

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

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*Kk + b. Identity is 0. */
static int gmul(int x, int y) {
    int a = x / Kk, b = x % Kk, c = y / Kk, e = y % Kk;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % Mm);
    int rb = (b + e) % Kk;
    return ra * Kk + rb;
}

static void free_group(void) {
    free(mulT); free(invT); free(Rpow);
    free(adj); free(stamp); free(fr); free(nx);
    mulT = invT = Rpow = adj = fr = nx = stamp = NULL;
}

static void setup_group(int m, int k, int r) {
    G = m * k; Mm = m; Kk = k; Rr = r;
    Rpow = malloc(sizeof(int) * (size_t)k);
    Rpow[0] = 1 % m;
    for (int b = 1; b < k; b++) Rpow[b] = (int)((long long)Rpow[b - 1] * r % m);
    mulT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[(size_t)x * G + y] = gmul(x, y);
    invT = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        invT[x] = 0;
        for (int y = 0; y < G; y++)
            if (mulT[(size_t)x * G + y] == 0) { invT[x] = y; break; }
    }
    adj = malloc(sizeof(int) * (size_t)2 * G * DEG);
    stamp = calloc((size_t)2 * G, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * G);
    nx = malloc(sizeof(int) * (size_t)2 * G);
    curstamp = 0;
}

static void build_adj(void) {
    for (int x = 0; x < G; x++) {
        for (int i = 0; i < DEG; i++) {
            adj[(size_t)x * DEG + i] = G + mulT[(size_t)x * G + S[i]];
            adj[(size_t)(G + x) * DEG + i] = mulT[(size_t)x * G + invS[i]];
        }
    }
}

static int bfs_count(int src) {
    int N = 2 * G;
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
    return count;
}

static int eval_cost(void) {
    build_adj();
    int N = 2 * G;
    int a = bfs_count(0);
    int b = bfs_count(G);
    return (N - a) + (N - b);
}

static int in_S(int v) {
    for (int j = 0; j < DEG; j++) if (S[j] == v) return 1;
    return 0;
}

static void random_S(void) {
    for (int i = 0; i < DEG; i++) {
        int v = rnd_int(G);
        while (1) {
            int dup = 0;
            for (int j = 0; j < i; j++) if (S[j] == v) { dup = 1; break; }
            if (!dup) break;
            v = rnd_int(G);
        }
        S[i] = v;
        invS[i] = invT[v];
    }
}

static int run_sa(int iters, double t0) {
    random_S();
    int cur = eval_cost();
    int best = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < iters && best > 0; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        double temp = t0 * (1.0 - (double)it / iters) + 0.03;
        int i = rnd_int(DEG);
        int v = rnd_int(G);
        if (in_S(v)) continue;
        int old = S[i], oldinv = invS[i];
        S[i] = v;
        invS[i] = invT[v];
        int c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            S[i] = old;
            invS[i] = oldinv;
        }
    }
    return best;
}

static void emit_best(void) {
    memcpy(S, bestS, sizeof(int) * (size_t)DEG);
    for (int i = 0; i < DEG; i++) invS[i] = invT[S[i]];
    int m = G * DEG;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int x = 0; x < G; x++) {
        for (int i = 0; i < DEG; i++) {
            best_e[idx++] = x;
            best_e[idx++] = G + mulT[(size_t)x * G + S[i]];
        }
    }
    best_m = m;
    best_n = 2 * G;
}

static int divs[GMAX + 2];

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
    start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int gmin = best_n / 2 + 1;
        if (gmin < DEG + 1) gmin = DEG + 1;
        if (gmin > GMAX) break;
        int span = 4 + gmin / 25;
        int g = gmin + rnd_int(span);
        if (g > GMAX) g = GMAX;

        int nd = 0;
        for (int m = 2; m <= g; m++)
            if (g % m == 0) divs[nd++] = m;
        int m = divs[rnd_int(nd)];
        int k = g / m;

        int r = 1;
        if (k > 1 && m > 2 && rnd_unit() < 0.7) {
            for (int tr = 0; tr < 200; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k, m) == 1 % m) {
                    r = cand;
                    break;
                }
            }
        }

        setup_group(m, k, r);
        int bc = run_sa(SA_ITERS, 2.5);
        if (bc == 0 && 2 * G > best_n) emit_best();
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
# Driver: baselines in Python, then the C bi-Cayley search.
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

    # Degree 2: the even cycle C_{2D} has diameter D.
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])

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

    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=max(2.0, 0.95 * time_limit - (time.monotonic() - start)))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
