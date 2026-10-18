"""Multi-orbit group lifts for the bipartite degree-diameter problem.

Construction: pick a finite group G = Z_m x| Z_k (element (a,b) coded as a*k+b, with
r^k = 1 mod m) and a base bipartite multigraph on A + A vertices whose row and column
sums are d. Each base dart (i, j) carries a voltage g in G, and the lift has vertices
(L_i, x) and (R_j, y) with (L_i, x) ~ (R_j, x*g). Voltages on parallel darts from i to j
are distinct, so the lift is simple, d-regular and bipartite with 2*A*|G| vertices.

G acts by right multiplication, transitively on each base class. Diameter <= D is therefore
checked by BFS from the 2A sources (L_i, e) and (R_j, e). Simulated annealing on the
voltages minimises the number of unreached (source, vertex) pairs.

A = 1 is the single-orbit Haar lift; A = 2, 3 are the new multi-orbit family. The C search
only accepts orders above the Python baseline, and Python validates everything.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit group lift search.
 * Usage: prog d D seed time_limit minV     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid lift with n > minV, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXA 3
#define MAXD 32
#define MAXDART (MAXA * MAXD)
#define MAXV (2 * MAXA * MAXN)

typedef struct {
    int m, k, r, A;
    int M[MAXA][MAXA];
    int dv[MAXDART];
} Cfg;

static int d, D, A, N;
static long moore;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int gm = -1, gk = -1, gr = -1;
static int16_t MT[MAXN * MAXN];
static int INVT[MAXN];
static int PWR[MAXN];
static int Ya[MAXN], Ye[MAXN];

/* Element (a, b) is a*k + b. Product (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(int m, int k, int r) {
    if (m == gm && k == gk && r == gr) return;
    gm = m; gk = k; gr = r;
    N = m * k;
    PWR[0] = 1 % m;
    for (int b = 1; b < k; b++) PWR[b] = (int)((long)PWR[b - 1] * r % m);
    for (int y = 0; y < N; y++) { Ya[y] = y / k; Ye[y] = y % k; }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int na = (int)((a + (long)PWR[b] * Ya[y]) % m);
            int nb = (b + Ye[y]) % k;
            MT[x * N + y] = (int16_t)(na * k + nb);
        }
    }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int bp = (k - b) % k;
        int na = (int)((m - ((long)PWR[bp] * a) % m) % m);
        INVT[x] = na * k + bp;
    }
}

/* ------------------------------------------------------------ base graph and voltages */

static int dj[MAXDART];          /* target base vertex of dart q; its left vertex is q / d */
static int rq[MAXA][MAXD];       /* darts entering right vertex j */
static int dv[MAXDART];          /* voltage of each dart */

static void build_darts(int M[MAXA][MAXA]) {
    for (int i = 0; i < A; i++) {
        int s = 0;
        for (int j = 0; j < A; j++)
            for (int t = 0; t < M[i][j]; t++) dj[i * d + s++] = j;
    }
    int cnt[MAXA] = {0};
    for (int q = 0; q < A * d; q++) {
        int j = dj[q];
        rq[j][cnt[j]++] = q;
    }
}

static void random_M(int M[MAXA][MAXA]) {
    for (int attempt = 0; attempt < 2000; attempt++) {
        memset(M, 0, sizeof(int) * MAXA * MAXA);
        int rr[MAXA], cc[MAXA];
        for (int i = 0; i < A; i++) { rr[i] = d; cc[i] = d; }
        int total = A * d;
        while (total > 0) {
            int i, j;
            do { i = rndint(A); } while (rr[i] == 0);
            do { j = rndint(A); } while (cc[j] == 0);
            M[i][j]++;
            rr[i]--;
            cc[j]--;
            total--;
        }
        int ok = 1;
        for (int i = 0; i < A; i++)
            for (int j = 0; j < A; j++)
                if (M[i][j] == 0) ok = 0;
        if (ok) return;
    }
}

/* True if some other dart p < upto in the same left block (p != q) has the same target and voltage g. */
static int conflict(int q, int g, int upto) {
    int i = q / d;
    for (int s = 0; s < d; s++) {
        int p = i * d + s;
        if (p != q && p < upto && dj[p] == dj[q] && dv[p] == g) return 1;
    }
    return 0;
}

static void init_dv(void) {
    for (int q = 0; q < A * d; q++) {
        int g;
        do { g = rndint(N); } while (conflict(q, g, q));
        dv[q] = g;
    }
}

/* ------------------------------------------------------------ cost */

static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Number of vertices NOT within distance D of src. */
static int unreached_from(int src) {
    int AN = A * N;
    int V = 2 * AN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < AN) {
                int i = v / N, x = v % N;
                for (int s = 0; s < d; s++) {
                    int q = i * d + s;
                    int y = MT[x * N + dv[q]];
                    int u = AN + dj[q] * N + y;
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int idx = v - AN;
                int j = idx / N, y = idx % N;
                for (int s = 0; s < d; s++) {
                    int q = rq[j][s];
                    int x = MT[y * N + INVT[dv[q]]];
                    int u = (q / d) * N + x;
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return V - tail;
}

/* Sources: left (i, e) and right (j, e). Every vertex is an image of one of them under the group action. */
static long total_cost(void) {
    long c = 0;
    int AN = A * N;
    for (int s = 0; s < 2 * A; s++) {
        int src = (s < A) ? s * N : AN + (s - A) * N;
        c += unreached_from(src);
    }
    return c;
}

/* Simulated annealing on the voltages. Returns 1 at cost 0, 0 on timeout. */
static int anneal(double slice_len) {
    double start = now();
    double end = start + slice_len;
    long cost = total_cost();
    if (cost == 0) return 1;
    double T0 = 0.05 * (double)cost + 1.0, Te = 0.3;
    int nd = A * d;
    for (;;) {
        double tn = now();
        if (tn >= end || tn >= t_end) return 0;
        double frac = (tn - start) / slice_len;
        double T = T0 * pow(Te / T0, frac);
        int q = rndint(nd);
        int g, tries = 0;
        do { g = rndint(N); tries++; } while (conflict(q, g, nd) && tries < 1000);
        if (tries >= 1000) continue;
        int old = dv[q];
        dv[q] = g;
        long c2 = total_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            dv[q] = old;
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long minV = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    moore = 0;
    {
        long p = 1;
        for (int i = 0; i < D; i++) {
            moore += p;
            if (moore > 100000000L) break;
            p *= (d - 1);
        }
        moore *= 2;
    }

    long bestV = minV;
    int have_best = 0;
    Cfg bestc;
    memset(&bestc, 0, sizeof bestc);

    while (now() < t_end - 0.5) {
        int valid[MAXA], nv = 0;
        for (int a = 1; a <= MAXA; a++) {
            long nmin = bestV / (2L * a) + 1;
            if (nmin < 4L * d) nmin = 4L * d;
            long nmax = moore / (2L * a);
            if (nmax > MAXN) nmax = MAXN;
            if (nmin <= nmax) valid[nv++] = a;
        }
        if (nv == 0) break;

        double r = rnd01();
        int want = r < 0.15 ? 1 : (r < 0.6 ? 2 : 3);
        int ok = 0;
        for (int t = 0; t < nv; t++) if (valid[t] == want) ok = 1;
        A = ok ? want : valid[rndint(nv)];

        long nmin = bestV / (2L * A) + 1;
        if (nmin < 4L * d) nmin = 4L * d;
        long nmax = moore / (2L * A);
        if (nmax > MAXN) nmax = MAXN;
        long span = (nmin + 80 < nmax) ? nmin + 80 : nmax;
        long Nt;
        if (rnd01() < 0.25) Nt = nmin + rndint((int)(span - nmin + 1));
        else Nt = nmin + (long)(rnd01() * rnd01() * (double)(span - nmin + 1));
        if (Nt > span) Nt = span;
        int NN = (int)Nt;

        int divs[64], nd = 0;
        for (int t = 1; t <= NN && nd < 64; t++)
            if (NN % t == 0) divs[nd++] = t;
        int k = divs[rndint(nd)];
        int m = NN / k;
        int rr = 0;
        if (m > 1) {
            rr = 1;
            for (int tr = 0; tr < 300; tr++) {
                int c = 1 + rndint(m - 1);
                if (gcd_i(c, m) == 1 && powmod(c, k, m) == 1) { rr = c; break; }
            }
        }
        set_group(m, k, rr);

        int M[MAXA][MAXA];
        if (A == 1) {
            memset(M, 0, sizeof M);
            M[0][0] = d;
        } else {
            random_M(M);
        }
        build_darts(M);
        init_dv();

        double rem = t_end - now();
        double slice = rem < 3.0 ? rem : 3.0;
        if (slice < 0.2) break;
        if (anneal(slice)) {
            long V = 2L * A * N;
            if (V > bestV) {
                bestV = V;
                have_best = 1;
                bestc.m = m;
                bestc.k = k;
                bestc.r = rr;
                bestc.A = A;
                memcpy(bestc.M, M, sizeof M);
                memcpy(bestc.dv, dv, sizeof dv);
            }
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestc.m, bestc.k, bestc.r);
    A = bestc.A;
    build_darts(bestc.M);
    memcpy(dv, bestc.dv, sizeof dv);
    if (total_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int AN = A * N;
    printf("%d %ld\n", 2 * AN, (long)AN * d);
    for (int i = 0; i < A; i++)
        for (int x = 0; x < N; x++)
            for (int s = 0; s < d; s++) {
                int q = i * d + s;
                int y = MT[x * N + dv[q]];
                printf("%d %d\n", i * N + x, AN + dj[q] * N + y);
            }
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Search: multi-orbit group lifts, only accepting orders above the Python baseline.
    if d >= 2 and D >= 3:
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 3.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
