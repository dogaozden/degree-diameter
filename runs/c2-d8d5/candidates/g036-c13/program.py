"""Abelian bi-Cayley (multi-orbit Haar-type) lift search in C, with exact small constructions as fallbacks."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions for D = 3 and D = 4 (calibration-style cases return fast).
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
# C engine: multi-orbit bi-Cayley lifts over abelian groups Z_a x Z_b.
# Vertices: A_{i,x} = i*N + x, B_{j,y} = P*N + j*N + y.
# Darts (i, j, s): A_{i,x} ~ B_{j,x+s}. Each A-orbit and B-orbit has exactly d darts.
# The graph is vertex-transitive within each orbit, so BFS from one representative
# per orbit decides the diameter. Simulated annealing (time-based schedule) minimises
# unreached pairs plus a penalty for duplicate darts. Successful orders are kept and
# the search climbs to larger N.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 40
#define MAXP 4
#define MAXV 8192
#define MAXND (MAXP * MAXD)

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Abelian group Z_GA x Z_GB of order GN = GA*GB; element u*GB + v. */
static int GA, GB, GN;

static int gadd(int x, int y) {
    int u = x / GB, v = x % GB, s = y / GB, t = y % GB;
    int uu = u + s;
    if (uu >= GA) uu -= GA;
    int vv = v + t;
    if (vv >= GB) vv -= GB;
    return uu * GB + vv;
}

static int gsub(int x, int y) {
    int u = x / GB, v = x % GB, s = y / GB, t = y % GB;
    int uu = u - s;
    if (uu < 0) uu += GA;
    int vv = v - t;
    if (vv < 0) vv += GB;
    return uu * GB + vv;
}

/* Current state. */
static int P;                 /* orbits per side */
static int ND;                /* number of darts = P*d */
static int dj[MAXND], ds[MAXND];
static int bd[MAXP][MAXD];    /* darts ending at B-orbit j */

static void build_bd(void) {
    int cnt[MAXP];
    for (int j = 0; j < P; j++) cnt[j] = 0;
    for (int t = 0; t < ND; t++) {
        int j = dj[t];
        bd[j][cnt[j]++] = t;
    }
}

static int vis[MAXV], vstamp = 0, qu[MAXV];

static int reach_count(int src) {
    int base = P * GN;
    int h = 0, tl = 0, cnt = 1;
    vstamp++;
    qu[tl++] = src;
    vis[src] = vstamp;
    for (int lvl = 0; lvl < D; lvl++) {
        int end = tl;
        if (h == end) break;
        while (h < end) {
            int v = qu[h++];
            if (v < base) {
                int i = v / GN, x = v % GN;
                for (int k = 0; k < d; k++) {
                    int t = i * d + k;
                    int w = base + dj[t] * GN + gadd(x, ds[t]);
                    if (vis[w] != vstamp) {
                        vis[w] = vstamp;
                        qu[tl++] = w;
                        cnt++;
                    }
                }
            } else {
                int r = v - base, j = r / GN, y = r % GN;
                for (int k = 0; k < d; k++) {
                    int t = bd[j][k];
                    int w = (t / d) * GN + gsub(y, ds[t]);
                    if (vis[w] != vstamp) {
                        vis[w] = vstamp;
                        qu[tl++] = w;
                        cnt++;
                    }
                }
            }
        }
    }
    return cnt;
}

static long dup_count(void) {
    long c = 0;
    for (int a = 0; a < ND; a++)
        for (int b = a + 1; b < ND; b++)
            if (a / d == b / d && dj[a] == dj[b] && ds[a] == ds[b]) c++;
    return c;
}

static long cost_eval(void) {
    build_bd();
    int V = 2 * P * GN;
    long un = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = s < P ? s * GN : P * GN + (s - P) * GN;
        un += V - reach_count(src);
    }
    return un + 1000L * dup_count();
}

static void random_state(void) {
    static int L[MAXND];
    int c = 0;
    for (int j = 0; j < P; j++)
        for (int k = 0; k < d; k++) L[c++] = j;
    for (int t = ND - 1; t > 0; t--) {
        int r = rndint(t + 1);
        int s = L[t];
        L[t] = L[r];
        L[r] = s;
    }
    for (int t = 0; t < ND; t++) {
        dj[t] = L[t];
        ds[t] = rndint(GN);
    }
}

static void pick_group(int N) {
    int divs[512], nd2 = 0;
    for (int a = 1; a <= N && nd2 < 512; a++)
        if (N % a == 0) divs[nd2++] = a;
    int a = divs[rndint(nd2)];
    GA = a;
    GB = N / a;
    GN = N;
}

/* Time-scheduled annealing. Returns 1 if a zero-cost (valid) state was reached. */
static int anneal(double slice) {
    double start = now(), stop = start + slice;
    long cost = cost_eval();
    while (cost > 0) {
        double tn = now();
        if (tn > stop) break;
        double frac = (tn - start) / slice;
        double T = 2.0 * (1.0 - frac) + 0.05;
        int mv = rndint(3);
        int t1 = rndint(ND), t2 = rndint(ND);
        int oldv = ds[t1], oj1 = dj[t1], oj2 = dj[t2];
        if (mv < 2) {
            ds[t1] = rndint(GN);
            if (ds[t1] == oldv) continue;
        } else {
            if (dj[t1] == dj[t2]) continue;
            int s = dj[t1];
            dj[t1] = dj[t2];
            dj[t2] = s;
        }
        long nc = cost_eval();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
        } else {
            if (mv < 2) {
                ds[t1] = oldv;
            } else {
                dj[t1] = oj1;
                dj[t2] = oj2;
            }
        }
    }
    return cost == 0;
}

static int best_ok = 0;
static int bestP, bestGA, bestGB, bestN;
static int bestdj[MAXND], bestds[MAXND];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    double moore;
    if (d == 1) {
        moore = 2;
    } else if (d == 2) {
        moore = 2.0 * D;
    } else {
        moore = 0;
        double p = 1;
        for (int i = 0; i < D; i++) {
            moore += p;
            p *= (d - 1);
        }
        moore *= 2;
    }

    long best_n = 0;
    while (now() < t_end) {
        if ((double)best_n + 2 > moore) break;
        int r = rndint(6);
        int p = r < 3 ? 1 : (r < 5 ? 2 : 3);
        long target = best_n + 2;
        long N = (target + 2L * p - 1) / (2L * p) + rndint(3);
        if (N < 1) continue;
        if (2.0 * p * N > moore || 2L * p * N > MAXV) continue;
        P = p;
        ND = p * d;
        pick_group((int)N);
        random_state();
        double remain = t_end - now();
        if (remain <= 0.05) break;
        double slice = remain < 4.0 ? remain : 4.0;
        if (anneal(slice)) {
            best_n = 2L * P * GN;
            bestP = P;
            bestGA = GA;
            bestGB = GB;
            bestN = GN;
            memcpy(bestdj, dj, sizeof(int) * ND);
            memcpy(bestds, ds, sizeof(int) * ND);
            best_ok = 1;
        }
    }

    if (!best_ok) {
        printf("0 0\n");
        return 0;
    }
    P = bestP;
    GA = bestGA;
    GB = bestGB;
    GN = bestN;
    ND = P * d;
    memcpy(dj, bestdj, sizeof(int) * ND);
    memcpy(ds, bestds, sizeof(int) * ND);
    long n = 2L * P * GN, m = (long)ND * GN;
    printf("%ld %ld\n", n, m);
    for (int t = 0; t < ND; t++) {
        int i = t / d;
        for (int x = 0; x < GN; x++) {
            int u = i * GN + x;
            int w = P * GN + dj[t] * GN + gadd(x, ds[t]);
            printf("%d %d\n", u, w);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.85 * time_limit - 3.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if lib.is_prime_power(d - 1):
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except (ValueError, RuntimeError):
                pass
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: abelian multi-orbit bi-Cayley lifts in C.
    c_budget = end - time.monotonic()
    if c_budget > 1.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=None, timeout=c_budget + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
