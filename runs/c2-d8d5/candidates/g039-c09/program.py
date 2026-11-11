"""Cayley-type search: vertex-transitive bi-Cayley graphs over small groups, found by annealing the connection set."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions kept from the previous version (cheap, return fast).
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
# C engine: bi-Cayley graphs over Z_m x|_r Z_k. Vertices A_g = g and B_h = N + h
# with A_g ~ B_{g*s} for s in S (|S| = d). Left multiplication is an automorphism,
# so the graph has diameter <= D iff BFS from A_0 and from B_0 reach everything
# within D steps. Simulated annealing on S, restarts over random groups of order N,
# and a bracket-and-bisect search over N.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2048
#define MAXD 32

typedef struct {
    int m, k, r;
    int rp[MAXG];
} Grp;

static int d, D, N;
static long Nmax;
static double t_end, try_end;

static Grp cur, bestG;
static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int bestN = 0;

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

/* Element x = a*k + b of Z_m x|_r Z_k, product (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(const Grp *G, int x, int y) {
    int k = G->k, m = G->m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int a2 = (a + G->rp[b] * c) % m;
    return a2 * k + (b + e) % k;
}

/* Inverse of (a,b) is (-r^{-b} a, -b), and r^{-b} = r^{(k-b) mod k}. */
static int ginv(const Grp *G, int x) {
    int k = G->k, m = G->m;
    int a = x / k, b = x % k;
    int bb = (k - b) % k;
    int aa = (m - (G->rp[bb] * a) % m) % m;
    return aa * k + bb;
}

/* Uniformly random semidirect group of order n (cyclic and direct products included). */
static int pick_group(int n, Grp *G) {
    long count = 0;
    int pm = 0, pk = 0, pr = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { pm = 1; pk = k; pr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { pm = m; pk = k; pr = r; }
        }
    }
    if (!count) return 0;
    G->m = pm; G->k = pk; G->r = pr;
    G->rp[0] = 1 % pm;
    for (int b = 1; b < pk; b++) G->rp[b] = (int)((long)G->rp[b - 1] * pr % pm);
    return 1;
}

static int qbuf0[2 * MAXG], qbuf1[2 * MAXG];
static int vis[2 * MAXG];
static int stamp = 0;

/* Number of vertices within distance D of src (src included). */
static int bfs_reach(int src) {
    int *cq = qbuf0, *nq = qbuf1;
    stamp++;
    int nc = 1, cnt = 1;
    cq[0] = src;
    vis[src] = stamp;
    for (int lev = 0; lev < D && nc > 0; lev++) {
        int nn = 0;
        for (int i = 0; i < nc; i++) {
            int v = cq[i];
            if (v < N) {
                for (int j = 0; j < d; j++) {
                    int u = N + gmul(&cur, v, S[j]);
                    if (vis[u] != stamp) { vis[u] = stamp; nq[nn++] = u; }
                }
            } else {
                int h = v - N;
                for (int j = 0; j < d; j++) {
                    int u = gmul(&cur, h, Sinv[j]);
                    if (vis[u] != stamp) { vis[u] = stamp; nq[nn++] = u; }
                }
            }
        }
        cnt += nn;
        int *t = cq; cq = nq; nq = t;
        nc = nn;
    }
    return cnt;
}

/* Zero iff the bi-Cayley graph has diameter <= D. */
static long cost_of(void) {
    return (2L * N - bfs_reach(0)) + (2L * N - bfs_reach(N));
}

static int in_set(int x, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == x) return 1;
    return 0;
}

static int anneal(long iters) {
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(N); } while (in_set(x, i));
        S[i] = x;
        Sinv[i] = ginv(&cur, x);
    }
    long c = cost_of();
    for (long t = 0; t < iters && c > 0; t++) {
        if ((t & 255) == 0 && now() > try_end) break;
        double T = 3.0 * pow(0.05, (double)t / (double)iters);
        int i = rndint(d), x = rndint(N);
        if (in_set(x, d)) continue;
        int old = S[i], oldinv = Sinv[i];
        S[i] = x;
        Sinv[i] = ginv(&cur, x);
        long c2 = cost_of();
        if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
            c = c2;
        } else {
            S[i] = old;
            Sinv[i] = oldinv;
        }
    }
    return c == 0;
}

static int attempt(int n, double budget) {
    double until = now() + budget;
    if (until > t_end) until = t_end;
    try_end = until;
    long iters = 2000 + 5L * n;
    while (now() < try_end) {
        if (!pick_group(n, &cur)) return 0;
        N = n;
        if (anneal(iters)) {
            bestN = n;
            bestG = cur;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

static void print_best(void) {
    if (bestN == 0) { printf("0 0\n"); return; }
    long m = (long)bestN * d;
    printf("%d %ld\n", 2 * bestN, m);
    for (int g = 0; g < bestN; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, bestN + gmul(&bestG, g, bestS[j]));
}

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
    t_end = t0 + limit * 0.97;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    /* Moore-type cap on one side: sum_{i<D} (d-1)^i. */
    long s = 0, p = 1;
    for (int i = 0; i < D && s <= MAXG; i++) { s += p; p *= (d - 1); }
    Nmax = s < MAXG ? s : MAXG;
    if (Nmax < d) { printf("0 0\n"); return 0; }

    /* Bracket with doubling, then bisect; retry the upper bound when converged. */
    int lo = 0, hi = 0;
    while (now() < t_end - 0.3) {
        double remaining = t_end - now();
        double budget = remaining * 0.2;
        if (budget < 0.5) budget = 0.5;
        if (budget > 8.0) budget = 8.0;
        long T;
        if (hi == 0) {
            T = (lo == 0) ? d : 2L * lo;
        } else if (hi - lo > 1) {
            T = (lo + hi) / 2;
        } else {
            T = hi;
            budget = remaining * 0.3;
            if (budget < 1.0) budget = 1.0;
            if (budget > 12.0) budget = 12.0;
        }
        if (T > Nmax) T = Nmax;
        if (T <= lo) break;
        if (T < d) T = d;
        int ok = attempt((int)T, budget);
        if (ok) {
            lo = (int)T;
            if (hi <= lo) hi = 0;
        } else if (hi == 0 || T < hi) {
            hi = (int)T;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Keep the new graph if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions (fast).
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
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley graphs over semidirect products, all in C.
    if D >= 2 and d >= 2:
        c_budget = 0.85 * time_limit - 4.0 - (time.monotonic() - t0)
        if c_budget >= 1.0:
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
