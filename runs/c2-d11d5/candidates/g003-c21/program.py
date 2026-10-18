"""Bi-Cayley (Haar-type) search over finite groups for bipartite degree-diameter graphs.

Construction change from the parent: instead of voltage lifts of random multigraph bases,
this searches Cayley-type bipartite graphs B(G, S). The vertices are A_g and B_g for g in a
finite group G of order N, and A_g ~ B_{gs} for each s in a connection set S of size d.
Left multiplication by G is an automorphism that is transitive on A and on B, so the
diameter is at most D exactly when BFS from A_1 and from B_1 both reach all 2N vertices
within depth D. Each evaluation is therefore two bounded BFS runs on an implicit graph.

The search anneals the d elements of S for a fixed group, and grows the group order with an
exponential-then-halving schedule. The group is drawn uniformly from the semidirect
products Z_m x| Z_k (cyclic groups included). Python keeps validated fallbacks (the known start
graph and K_{d,d}) and only accepts a C result that is larger and passes lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley bipartite search: B(G,S) with A_g ~ B_{gs}, s in S, |S| = d.
 *
 * Usage:  prog d D seed time_limit        (stdin ignored)
 * stdout: "n m" + edges of the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 12000
#define MAXD 32

typedef struct {
    int m, k;
    int rp[MAXH];   /* rp[b] = r^b mod m */
    int inv[MAXH];  /* inverse of each element */
} Grp;

static int d, D;
static double t_end;
static Grp G, bestG;
static int N;                         /* current side size = |G| */
static int sel[MAXD];                 /* current connection set S */
static int tmpS[MAXD], bestS[MAXD];
static long bestN = 0;
static int have = 0;
static int tabR[MAXD][MAXH];          /* tabR[t][x] = x * s_t      (A -> B) */
static int tabL[MAXD][MAXH];          /* tabL[t][x] = x * s_t^-1   (B -> A) */
static int vis[2 * MAXH];
static int qu[2 * MAXH];
static int stamp = 0;

/* ------------------------------------------------------------ utilities */

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

/* Largest side size N with 2N <= Moore bound, i.e. N <= sum_{i<D} (d-1)^i. */
static long side_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > 4L * MAXH) break;
        p *= (d - 1);
        if (p > 1000000000L) p = 1000000000L;
    }
    return s;
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int gmul(int x, int y) {
    int a = x / G.k, b = x - a * G.k;
    int c = y / G.k, e = y - c * G.k;
    long first = ((long)a + (long)G.rp[b] * c) % G.m;
    int second = (b + e) % G.k;
    return (int)(first * G.k + second);
}

/* Uniform random (m, k, r) with m*k = n, gcd(r,m)=1, r^k=1 mod m. Fills G. */
static int random_group(int n) {
    long count = 0;
    int bm = 1, bk = n, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    G.m = bm;
    G.k = bk;
    G.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G.rp[b] = (int)((long)G.rp[b - 1] * br % bm);
    for (int x = 0; x < n; x++) {
        int a = x / bk, b = x - a * bk;
        int e = (bk - b) % bk;                           /* inverse has second coord -b */
        long c = ((long)(bm - a) % bm) * G.rp[e] % bm;   /* -a * r^{-b} */
        G.inv[x] = (int)c * bk + e;
    }
    return 1;
}

/* ------------------------------------------------------------ connection set */

static int in_sel(int g, int cnt) {
    for (int t = 0; t < cnt; t++)
        if (sel[t] == g) return 1;
    return 0;
}

static void set_row(int t) {
    int s = sel[t];
    int si = G.inv[s];
    for (int x = 0; x < N; x++) {
        tabR[t][x] = gmul(x, s);
        tabL[t][x] = gmul(x, si);
    }
}

/* Number of vertices within distance D of src in the bipartite graph B(G,S). */
static int bfs_count(int src) {
    if (++stamp == 0x7fffffff) { memset(vis, 0, sizeof vis); stamp = 1; }
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            if (v < N) {
                for (int t = 0; t < d; t++) {
                    int w = N + tabR[t][v];
                    if (vis[w] != stamp) { vis[w] = stamp; qu[tail++] = w; }
                }
            } else {
                int h = v - N;
                for (int t = 0; t < d; t++) {
                    int w = tabL[t][h];
                    if (vis[w] != stamp) { vis[w] = stamp; qu[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs from A_1 and from B_1; zero means diameter <= D. */
static long eval_cost(void) {
    long c1 = 2L * N - bfs_count(0);
    long c2 = 2L * N - bfs_count(N);
    return c1 + c2;
}

/* Anneal S over a random group of order n for at most tlim seconds.
 * Returns 1 and writes S to outS on success. */
static int attempt(int n, double tlim, int *outS) {
    if (!random_group(n)) return 0;
    N = n;
    for (int t = 0; t < d; t++) {
        int g;
        do { g = rndint(N); } while (in_sel(g, t));
        sel[t] = g;
    }
    for (int t = 0; t < d; t++) set_row(t);
    long cost = eval_cost();
    double T0 = 1.0 + 0.05 * (double)cost;
    const double Tf = 0.05;
    double t0 = now();
    double tend = t0 + tlim;
    if (tend > t_end) tend = t_end;
    while (cost > 0) {
        double tn = now();
        if (tn >= tend) break;
        double frac = (tn - t0) / (tend - t0);
        double T = Tf + (T0 - Tf) * (1.0 - frac);
        int t = rndint(d);
        int g = rndint(N);
        if (in_sel(g, d)) continue;
        int old = sel[t];
        sel[t] = g;
        set_row(t);
        long nc = eval_cost();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
        } else {
            sel[t] = old;
            set_row(t);
        }
    }
    if (cost != 0) return 0;
    memcpy(outS, sel, sizeof(int) * d);
    return 1;
}

/* Grow the side size: exponential steps on success, halving on failure. */
static void search(void) {
    long smax = side_bound();
    if (smax > MAXH) smax = MAXH;
    long delta = 1;
    while (now() < t_end) {
        long target;
        if (!have) {
            target = d;
        } else {
            if (bestN >= smax) break;
            target = bestN + delta;
            if (target > smax) target = smax;
        }
        if (target > smax) break;
        double remaining = t_end - now();
        if (remaining <= 0) break;
        double slice = remaining * 0.12;
        if (slice < 2.0) slice = 2.0;
        if (slice > remaining) slice = remaining;
        if (attempt((int)target, slice, tmpS)) {
            bestN = target;
            have = 1;
            memcpy(bestS, tmpS, sizeof(int) * d);
            bestG = G;
            delta *= 2;
            if (delta > smax) delta = smax;
        } else {
            if (delta > 1) delta /= 2;
        }
    }
}

static void print_best(void) {
    if (!have) { printf("2 1\n0 1\n"); return; }
    G = bestG;
    N = (int)bestN;
    long m = (long)N * d;
    printf("%d %ld\n", 2 * N, m);
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", x, N + gmul(x, bestS[t]));
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) {
        printf("2 1\n0 1\n");   /* a single edge is valid for D >= 1 */
        return 0;
    }
    search();
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Safe fallback: a single edge is valid for any D >= 1 and d >= 1.
    best = (2, [(0, 1)])

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None

    candidates = []
    if start is not None:
        candidates.append(start)
    if D >= 2 and d >= 1:
        candidates.append(lib.haar_graph(d, range(d)))   # K_{d,d}, valid for D >= 2
    for n, edges in candidates:
        try:
            ok = lib.is_valid(n, edges, d, D)
        except Exception:
            ok = False
        if ok and n > best[0]:
            best = (n, edges)

    budget = 0.9 * time_limit - 2.0 - (time.monotonic() - t0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine

    if budget > 0.5 and D >= 2 and d >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 8.0)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass   # keep the valid fallback

    return best
