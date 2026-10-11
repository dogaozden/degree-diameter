import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
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
# C engine: simulated annealing over bi-Cayley graphs with K = 1.
#
# Group G = Z_m semidirect Z_k (action r), coded as a*k+b, with multiplication
# (a,b)(c,d) = (a + r^b c, b + d). Darts s_1..s_d are distinct group elements.
# Vertices: A_g = g and B_h = G + h, with edges A_g -- B_{g s_l}.
# Left multiplication is an automorphism, so only the two identity sources
# (A_e and B_e) need BFS. Cost = unreached vertices within DD steps from both.
# Cost 0 means the graph has diameter <= DD.
#
# Strategy: ramp the order upward. For each order G in a window just above the
# best found, sample a group of that order, anneal the darts, and keep the
# largest order that succeeds.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 16
#define GMAX 2000
#define MAXCAND 8192

typedef struct { int m, k, r; } Grp;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 5;
static double deadline = 0.0;
static int Gn = 1, capG = 0;
static int *MT = NULL, *INV = NULL, *vis = NULL, *qu = NULL;
static int stamp = 0;
static int pw[GMAX + 1];
static int Sv[MAXD];
static Grp cand[MAXCAND];

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod_i(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static void ensure_cap(int G) {
    if (G <= capG) return;
    free(MT);
    free(INV);
    free(vis);
    free(qu);
    capG = G;
    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    vis = calloc((size_t)2 * G, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)2 * G);
    if (!MT || !INV || !vis || !qu) {
        printf("0 0\n");
        exit(0);
    }
}

static void build_group(Grp g) {
    int m = g.m, k = g.k, r = g.r;
    int G = m * k;
    ensure_cap(G);
    Gn = G;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            int aa = (int)(((long long)a1 + (long long)pw[b1] * c) % m);
            int bb = (b1 + d) % k;
            MT[x * G + y] = aa * k + bb;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) {
                INV[x] = y;
                break;
            }
}

/* BFS from src up to DD steps; returns number of unreached vertices among 2G. */
static int bfs_unreached(int src) {
    stamp++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = qu[head++];
            if (u < Gn) {
                const int *row = MT + (size_t)u * Gn;
                for (int l = 0; l < Dd; l++) {
                    int v = Gn + row[Sv[l]];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            } else {
                int h = u - Gn;
                const int *row = MT + (size_t)h * Gn;
                for (int l = 0; l < Dd; l++) {
                    int v = row[INV[Sv[l]]];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
    }
    return 2 * Gn - tail;
}

static int cost(void) {
    return bfs_unreached(0) + bfs_unreached(Gn);
}

static int in_S(int v, int upto) {
    for (int i = 0; i < upto; i++)
        if (Sv[i] == v) return 1;
    return 0;
}

/* Simulated annealing on the darts for at most tb seconds.
   Returns 0 if a valid configuration was reached (state left in Sv). */
static int anneal(double tb) {
    if (Gn < Dd) return 1;
    for (int l = 0; l < Dd; l++) {
        int v;
        do {
            v = rint_(Gn);
        } while (in_S(v, l));
        Sv[l] = v;
    }
    int cur = cost();
    if (cur == 0) return 0;
    double t0 = now_s();
    const double T0 = 2.0, T1 = 0.02;
    double T = T0;
    long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double now = now_s();
            double el = now - t0;
            if (el >= tb || now >= deadline) break;
            double frac = el / tb;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        int l = rint_(Dd);
        int v = rint_(Gn);
        if (in_S(v, Dd)) continue;
        int old = Sv[l];
        Sv[l] = v;
        int c2 = cost();
        int delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur == 0) return 0;
        } else {
            Sv[l] = old;
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int bestG = min_n / 2;   /* need 2G > min_n */
    int have = 0;
    Grp bestg = {1, 1, 1};
    int bestS[MAXD];
    memset(bestS, 0, sizeof(bestS));

    while (now_s() < deadline) {
        int lo = bestG + 1;
        if (lo < Dd) lo = Dd;
        if (lo > GMAX) break;
        int step = lo / 40;
        if (step < 4) step = 4;
        int hi = lo + step;
        if (hi > GMAX) hi = GMAX;
        int G = lo + rint_(hi - lo + 1);

        /* Enumerate groups of order G: cyclic, and Z_m semidirect Z_k. */
        int nc = 0;
        for (int k = 1; k <= G; k++) {
            if (G % k) continue;
            int m = G / k;
            if (k == 1) {
                if (nc < MAXCAND) {
                    cand[nc].m = m;
                    cand[nc].k = 1;
                    cand[nc].r = 1;
                    nc++;
                }
            } else {
                if (m < 2) continue;
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod_i(r, k, m) != 1 % m) continue;
                    if (nc < MAXCAND) {
                        cand[nc].m = m;
                        cand[nc].k = k;
                        cand[nc].r = r;
                        nc++;
                    }
                }
            }
        }
        if (nc == 0) continue;

        Grp g = cand[rint_(nc)];
        double rem = deadline - now_s();
        if (rem <= 0.05) break;
        double tb = rem * 0.25;
        if (tb > 6.0) tb = 6.0;
        if (tb < 0.5) tb = 0.5;
        if (tb > rem) tb = rem;

        build_group(g);
        int res = anneal(tb);
        if (res == 0) {
            bestG = G;
            bestg = g;
            for (int l = 0; l < Dd; l++) bestS[l] = Sv[l];
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    build_group(bestg);
    for (int l = 0; l < Dd; l++) Sv[l] = bestS[l];
    int n = 2 * Gn;
    printf("%d %ld\n", n, (long)Dd * (long)Gn);
    for (int l = 0; l < Dd; l++) {
        for (int g = 0; g < Gn; g++) {
            printf("%d %d\n", g, Gn + MT[g * Gn + Sv[l]]);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(3.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley annealing over semidirect groups, ramping the order upward.
    if d >= 2 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    try:
        if lib.is_valid(best[0], best[1], d, D):
            return best
    except Exception:
        pass
    return lib.haar_graph(d, range(d))
