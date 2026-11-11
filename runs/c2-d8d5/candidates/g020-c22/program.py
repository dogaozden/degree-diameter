"""Haar-graph (bi-Cayley over one group orbit) annealing engine, with exact constructions and a valid fallback."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: Haar graphs H(G, S) over semidirect products G = Z_m x| Z_k.
# Vertices A_g = g and B_h = N + h; A_g ~ B_{g s} for s in S (|S| = d).
# Left multiplication is an automorphism, so the graph has diameter <= D
# iff BFS from A_e and from B_e both reach everything within D.
# S is annealed (S[0] fixed to the identity, which is WLOG).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Haar-graph annealing over semidirect products.
 * Usage: prog d D seed time_limit min_half
 * Output: "2N M" plus edges for the largest valid order N >= min_half found,
 *         or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2048
#define MAXD 32
#define MAXV (2 * MAXG)

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

/* Largest order of one side: sum_{i<D} (d-1)^i (the bipartite Moore half). */
static long moore_half(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return s;
}

/* Group state: element index a*GK+b for (a,b) in Z_GM x| Z_GK, (a,b)(c,e) = (a + r^b c, b+e). */
static int NG, GM, GK;
static int rp[MAXG];
static int MT[MAXG * MAXG];
static int INV[MAXG];

static int S[MAXD];
static int adj[MAXV][MAXD];
static int dist[MAXV];
static int queue[MAXV];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)((a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    NG = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < NG; x++)
        for (int y = 0; y < NG; y++)
            MT[x * NG + y] = gmul(x, y);
    for (int x = 0; x < NG; x++) {
        INV[x] = 0;
        for (int y = 0; y < NG; y++)
            if (MT[x * NG + y] == 0) { INV[x] = y; break; }
    }
}

/* Uniform random semidirect group of order N (reservoir sampling over (m, r)). */
static int pick_group(int N, int *om, int *ok, int *orr) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)(cnt < 2000000000L ? cnt : 2000000000L)) == 0) {
                bm = m; bk = k; br = r;
            }
        }
    }
    if (!cnt) return 0;
    *om = bm; *ok = bk; *orr = br;
    return 1;
}

static int in_S(int x, int count) {
    for (int j = 0; j < count; j++)
        if (S[j] == x) return 1;
    return 0;
}

static void build_adj(void) {
    int N = NG;
    for (int g = 0; g < N; g++) {
        for (int j = 0; j < d; j++) {
            adj[g][j] = N + MT[g * N + S[j]];             /* A_g ~ B_{g s} */
            adj[N + g][j] = MT[g * N + INV[S[j]]];        /* B_g ~ A_{g s^-1} */
        }
    }
}

/* Number of vertices not within distance D of root. */
static long bfs_bad(int root) {
    int V = 2 * NG;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[root] = 0;
    queue[tail++] = root;
    while (head < tail) {
        int v = queue[head++];
        if (dist[v] >= D) continue;
        for (int j = 0; j < d; j++) {
            int u = adj[v][j];
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                queue[tail++] = u;
            }
        }
    }
    return (long)(V - tail);
}

static long cost(void) {
    build_adj();
    return bfs_bad(0) + bfs_bad(NG);
}

/* Anneal S for up to `slice` seconds. Returns 1 if a valid Haar graph was reached. */
static int anneal_run(double slice) {
    double start = now();
    long c = cost();
    double T = 2.0;
    long it = 0;
    while (c > 0) {
        if ((it & 63) == 0) {
            double tn = now();
            double frac = (tn - start) / slice;
            if (frac >= 1.0 || tn > t_end) break;
            T = 2.0 * (1.0 - frac) + 0.05;
        }
        it++;
        int j = 1 + rndint(d - 1);
        int old = S[j];
        int nw;
        do { nw = rndint(NG); } while (in_S(nw, d));
        S[j] = nw;
        long c2 = cost();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            S[j] = old;
        }
    }
    return c == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit min_half\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_half = atol(argv[5]);

    t_end = now() + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    long half = moore_half();
    long lo = min_half;
    if (lo < d + 1) lo = d + 1;

    long bestN = 0;
    int bm = 0, bk = 0, br = 0;
    int bS[MAXD];

    while (now() < t_end) {
        long base = bestN > lo - 1 ? bestN : lo - 1;
        long N = base + 1 + rndint(4);
        if (N > half) N = half;
        if (N > MAXG) N = MAXG;
        if (N <= base) break;

        int m, k, r;
        if (!pick_group((int)N, &m, &k, &r)) continue;
        set_group(m, k, r);

        S[0] = 0;
        for (int j = 1; j < d; j++) {
            int x;
            do { x = rndint(NG); } while (in_S(x, j));
            S[j] = x;
        }

        double slice = t_end - now();
        if (slice > 5.0) slice = 5.0;
        if (slice <= 0.05) break;

        if (anneal_run(slice)) {
            bestN = NG;
            bm = m; bk = k; br = r;
            for (int j = 0; j < d; j++) bS[j] = S[j];
        }
    }

    if (bestN == 0 || bestN < min_half) {
        printf("0 0\n");
        return 0;
    }

    set_group(bm, bk, br);
    int N = (int)bestN;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, N + MT[g * N + bS[j]]);
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
        """Replace the current best if (n, e) is a larger valid graph."""
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

    # Bold search: Haar graphs over many semidirect groups, annealed in C.
    # Only orders above the current best are useful, so ask C for 2N > best.
    if D >= 2 and d >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            min_half = best[0] // 2 + 1
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), min_half],
                                 stdin_graph=None, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
