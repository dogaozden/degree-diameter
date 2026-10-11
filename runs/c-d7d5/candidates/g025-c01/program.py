import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as safe fallbacks and for small calibration cases).
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
# C engine: Cayley-type bipartite search over a broad family of finite groups.
#
# Group G = Z_c x (Z_m semidirect Z_k) with action r, element coded as
# t*(m*k) + a*k + b. The graph has vertices (g,0) = g and (h,1) = n + h, and
# edges (g,0)-(g*s,1) for s in S, |S| = d (distinct). This graph is
# vertex-transitive on each side under left multiplication, so diameter <= D
# holds iff BFS from (e,0) and from (e,1) reaches every vertex within D steps.
# Cost = number of unreached vertices in those two BFS runs. Cost 0 is valid.
#
# Search: sample a group order in a window just above the current best,
# then run simulated annealing over the connection set S. The window slides
# upward each time a solution is found.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <math.h>
#include <time.h>

#define GMAX 1600
#define MAXDEG 64
#define MAXK 40
#define SLICE 0.8
#define STEPS 6000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd_unit(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double deadline = 0.0;

/* ---------------- group tables ---------------- */

static int gn = 1;
static int *mt = NULL;
static int *iv = NULL;
static int mt_cap = 0;
static int pwr[MAXK];

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Element x = t*(m*k) + a*k + b. Product: (t1+t2, a1 + r^b1 * a2, b1+b2). */
static int build_group(int c, int m, int k, int r) {
    if (c < 1 || m < 1 || k < 1 || k > MAXK) return 0;
    int mk = m * k;
    long long nn = (long long)c * (long long)mk;
    if (nn > GMAX) return 0;
    int n = (int)nn;
    if (n > mt_cap) {
        free(mt);
        free(iv);
        mt = malloc(sizeof(int) * (size_t)n * (size_t)n);
        iv = malloc(sizeof(int) * (size_t)n);
        if (!mt || !iv) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        mt_cap = n;
    }
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        pwr[b] = (int)p;
        p = (p * r) % m;
    }
    gn = n;
    for (int x = 0; x < n; x++) {
        int t1 = x / mk, rem1 = x % mk, a1 = rem1 / k, b1 = rem1 % k;
        for (int y = 0; y < n; y++) {
            int t2 = y / mk, rem2 = y % mk, a2 = rem2 / k, b2 = rem2 % k;
            int t = (t1 + t2) % c;
            int a = (int)(((long long)a1 + (long long)pwr[b1] * (long long)a2) % m);
            int b = (b1 + b2) % k;
            mt[x * n + y] = t * mk + a * k + b;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (mt[x * n + y] == 0) iv[x] = y;
    return 1;
}

/* ---------------- group sampling ---------------- */

static const int KF[] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 5, 6, 8, 10, 12, 14, 16, 20, 24};
static const int CF[] = {1, 1, 1, 1, 2, 2, 3, 4, 5, 6, 7, 8};
static int cands[GMAX + 1];

/* Picks c, m, k, r with order n = c*m*k in [lo, hi]. */
static int sample_group(int lo, int hi, int *oc, int *om, int *ok, int *orr) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int nc = (int)(sizeof(CF) / sizeof(CF[0]));
    if (hi > GMAX) hi = GMAX;
    if (lo < 1) lo = 1;
    if (lo > hi) return 0;
    for (int tries = 0; tries < 400; tries++) {
        int c = CF[rnd_int(nc)];
        int k = KF[rnd_int(nk)];
        int ck = c * k;
        int mmin = (lo + ck - 1) / ck;
        if (mmin < 1) mmin = 1;
        int mmax = hi / ck;
        if (mmax < mmin) continue;
        int m = mmin + rnd_int(mmax - mmin + 1);
        int r = 1;
        if (k > 1 && m >= 3 && rnd_int(4) != 0) {
            int cnt = 0;
            for (int cand = 2; cand < m; cand++) {
                if (gcd_i(cand, m) == 1 && powmod_ll(cand, k, m) == 1 % m) {
                    cands[cnt++] = cand;
                }
            }
            if (cnt > 0) r = cands[rnd_int(cnt)];
        }
        *oc = c;
        *om = m;
        *ok = k;
        *orr = r;
        return 1;
    }
    return 0;
}

/* ---------------- cost evaluation ---------------- */

static int *vis = NULL;
static int *qu = NULL;
static int vcap = 0;
static int stamp = 0;

static void ensure_vis(int N) {
    if (N > vcap) {
        free(vis);
        free(qu);
        vis = calloc((size_t)N, sizeof(int));
        qu = malloc(sizeof(int) * (size_t)N);
        if (!vis || !qu) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        vcap = N;
        stamp = 0;
    }
}

/* Number of vertices (of 2n) not reached from src within DD steps. */
static int unreached(const int *S, const int *ivS, int d, int src) {
    int n = gn;
    int N = 2 * n;
    if (++stamp == INT_MAX) {
        memset(vis, 0, sizeof(int) * (size_t)vcap);
        stamp = 1;
    }
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int u = qu[head++];
            if (u < n) {
                const int *row = mt + (size_t)u * (size_t)n;
                for (int j = 0; j < d; j++) {
                    int v = n + row[S[j]];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            } else {
                const int *row = mt + (size_t)(u - n) * (size_t)n;
                for (int j = 0; j < d; j++) {
                    int v = row[ivS[j]];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
    }
    return N - tail;
}

static long long eval_cost(const int *S, int d) {
    int ivS[MAXDEG];
    for (int j = 0; j < d; j++) ivS[j] = iv[S[j]];
    long long c = unreached(S, ivS, d, 0);
    c += unreached(S, ivS, d, gn);
    return c;
}

static int in_set(const int *S, int d, int x) {
    for (int j = 0; j < d; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* Simulated annealing over the d distinct connection elements of the current group.
   Returns 1 and fills outS when a cost-0 set is found before t_end. */
static int sa_group(int d, double t_end, int *outS, long long *used) {
    int cur[MAXDEG];
    int n = gn;
    *used = 0;
    while (now_s() < t_end) {
        for (int j = 0; j < d; j++) {
            int x;
            do {
                x = rnd_int(n);
            } while (in_set(cur, j, x));
            cur[j] = x;
        }
        long long cc = eval_cost(cur, d);
        (*used)++;
        if (cc == 0) {
            memcpy(outS, cur, sizeof(int) * (size_t)d);
            return 1;
        }
        for (int st = 0; st < STEPS; st++) {
            if ((st & 255) == 0 && now_s() > t_end) break;
            double T = 1.5 * (1.0 - (double)st / STEPS) + 0.05;
            int i = rnd_int(d);
            int x;
            do {
                x = rnd_int(n);
            } while (in_set(cur, d, x));
            int old = cur[i];
            cur[i] = x;
            long long c2 = eval_cost(cur, d);
            (*used)++;
            if (c2 <= cc || rnd_unit() < exp(-(double)(c2 - cc) / T)) {
                cc = c2;
                if (cc == 0) {
                    memcpy(outS, cur, sizeof(int) * (size_t)d);
                    return 1;
                }
            } else {
                cur[i] = old;
            }
        }
    }
    return 0;
}

static void print_graph(int d, int bc, int bm, int bk, int br, const int *S) {
    build_group(bc, bm, bk, br);
    int n = gn;
    printf("%d %lld\n", 2 * n, (long long)d * (long long)n);
    for (int j = 0; j < d; j++) {
        for (int g = 0; g < n; g++) {
            printf("%d %d\n", g, n + mt[g * n + S[j]]);
        }
    }
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXDEG || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    deadline = now_s() + tl;
    int lo = min_n / 2;          /* known feasible half-order (graph has 2*lo vertices) */
    int best_G = 0;
    int bc = 1, bm = 1, bk = 1, br = 1;
    int S[MAXDEG];
    int bestS[MAXDEG];

    while (now_s() < deadline) {
        int width = lo / 25 + 3;
        int c, m, k, r;
        if (!sample_group(lo + 1, lo + width, &c, &m, &k, &r)) continue;
        if (!build_group(c, m, k, r)) continue;
        int n = gn;
        if (n < Dd + 1) continue;
        ensure_vis(2 * n);
        double t_end = now_s() + SLICE;
        if (t_end > deadline) t_end = deadline;
        long long used = 0;
        if (sa_group(Dd, t_end, S, &used)) {
            best_G = n;
            bc = c;
            bm = m;
            bk = k;
            br = r;
            memcpy(bestS, S, sizeof(int) * (size_t)Dd);
            lo = n;
        }
    }

    if (best_G == 0) {
        printf("0 0\n");
        return 0;
    }
    print_graph(Dd, bc, bm, bk, br, bestS);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the group-based C search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

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

    # Group-based Cayley-bipartite search in C, seeded with the best known order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
