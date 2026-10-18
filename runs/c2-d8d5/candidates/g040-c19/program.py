"""Single-orbit Haar graph search over finite groups, with two-BFS validity checks.

For a group G and connection set S (|S| = d), the Haar graph has vertices a_g and b_h (g, h in G),
with a_g adjacent to b_{gs} for s in S. Left translation is an automorphism that is transitive on
each side, so the diameter is at most D exactly when BFS from a_e and from b_e reaches everything
within D steps. A simulated-annealing search over S then needs only O(|G| d) work per move.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (kept from the parent; they return instantly).
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
# C engine: Haar graphs over semidirect products Z_m x| Z_k.
# Vertices a_g = g and b_h = N + h. Edge a_g ~ b_{g*s} for s in S (|S| = d).
# Search: for each order N = best+1 (so the graph has 2N > best vertices),
# pick a random group of order N and anneal S until the two-BFS cost is zero.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Haar-graph search over groups.
 * Usage:  prog d D seed time_limit [n0]
 * Output: "n m" plus edges of the largest valid Haar graph found with n > 2*n0,
 *         or "0 0" if none was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3000
#define MAXD 32

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x|_r Z_k, order GN = m*k, element (a,b) coded as a*GK+b. */
static int GN, GM, GK;
static int rp[MAXN];
static uint16_t mt[MAXN * MAXN];   /* mt[x*GN+y] = x*y */
static int ginv[MAXN];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static void make_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            mt[x * GN + y] = (uint16_t)gmul(x, y);
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (mt[x * GN + y] == 0) { ginv[x] = y; break; }
}

static long moore_bound(void) {
    if (d == 1) return 2;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* Uniform random semidirect group of order N (reservoir over all (m,k,r)). */
static int pick_group(int N, int *om, int *ok, int *orr) {
    long cnt = 0;
    for (int k = 1; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { *om = 1; *ok = k; *orr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { *om = m; *ok = k; *orr = r; }
        }
    }
    return cnt > 0;
}

static int S[MAXD], Sinv[MAXD];
static unsigned char inS[MAXN];
static unsigned vis[2 * MAXN];
static unsigned stamp_v = 0;
static int qu[2 * MAXN];

/* Number of vertices within distance D of src (src is a_e = 0 or b_e = GN). */
static int bfs_reach(int src) {
    stamp_v++;
    int lo = 0, hi = 1;
    qu[0] = src;
    vis[src] = stamp_v;
    for (int lev = 0; lev < D; lev++) {
        int nhi = hi;
        for (int i = lo; i < hi; i++) {
            int v = qu[i];
            if (v < GN) {
                const uint16_t *row = mt + (long)v * GN;
                for (int j = 0; j < d; j++) {
                    int u = GN + row[S[j]];
                    if (vis[u] != stamp_v) { vis[u] = stamp_v; qu[nhi++] = u; }
                }
            } else {
                const uint16_t *row = mt + (long)(v - GN) * GN;
                for (int j = 0; j < d; j++) {
                    int u = row[Sinv[j]];
                    if (vis[u] != stamp_v) { vis[u] = stamp_v; qu[nhi++] = u; }
                }
            }
        }
        lo = hi;
        hi = nhi;
        if (lo == hi) break;
    }
    return hi;
}

/* Zero exactly when the Haar graph of (G, S) has diameter <= D. */
static int cost_of(void) {
    return (2 * GN - bfs_reach(0)) + (2 * GN - bfs_reach(GN));
}

static int anneal(int iters, int patience) {
    for (int x = 0; x < GN; x++) inS[x] = 0;
    for (int j = 0; j < d; j++) {
        int x;
        do x = rndint(GN); while (inS[x]);
        inS[x] = 1;
        S[j] = x;
        Sinv[j] = ginv[x];
    }
    int cur = cost_of(), best = cur, last = 0;
    for (int t = 0; t < iters && cur > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > t_end) break;
        double T = 1.0 * (1.0 - (double)t / iters) + 0.05;
        int j = rndint(d);
        int x;
        do x = rndint(GN); while (inS[x]);
        int old = S[j], oldinv = Sinv[j];
        inS[old] = 0;
        inS[x] = 1;
        S[j] = x;
        Sinv[j] = ginv[x];
        int c2 = cost_of();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            if (cur < best) { best = cur; last = t; }
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[j] = old;
            Sinv[j] = oldinv;
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [n0]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int n0 = argc >= 6 ? atoi(argv[5]) : d;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (n0 < d) n0 = d;

    long moore = moore_bound();
    int bestN = n0, bGm = 0, bGk = 0, bGr = 0, have = 0;
    int bestS[MAXD];

    while (now() < t_end) {
        int N = bestN + 1;
        if (N > MAXN || 2L * N > moore) break;
        int m, k, r;
        if (!pick_group(N, &m, &k, &r)) break;
        make_group(m, k, r);
        if (anneal(40000, 8000)) {
            bestN = N;
            bGm = m;
            bGk = k;
            bGr = r;
            memcpy(bestS, S, sizeof(int) * d);
            have = 1;
        }
    }

    if (!have) { printf("0 0\n"); return 0; }
    make_group(bGm, bGk, bGr);
    int N = bestN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, N + (int)mt[g * N + bestS[j]]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold change: Haar graphs over semidirect groups, searched in C.
    # A Haar graph on 2N vertices is bipartite and has degree d; N = best/2 + 1 beats the current best.
    c_budget = end - time.monotonic() - 0.5
    if c_budget > 1.0:
        n0 = max(d, best[0] // 2)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), n0],
                             timeout=c_budget + 8)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
