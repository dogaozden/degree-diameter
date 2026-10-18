"""Program: abelian voltage lifts searched by annealing with fibre-representative BFS.

Different construction from the earlier semidirect-product search:
  * Lifts over abelian groups Z_m1 x Z_m2 (cyclic when m1 = 1), with p = 1..4 base
    vertices per side and a random d-regular base made of d permutations.
  * Voltages are annealed. A move changes one voltage; the cost is the number of
    (fibre representative, vertex) pairs at distance > D, found by BFS from the 2p
    fibre representatives only. Translations are automorphisms of the lift, so
    bad == 0 proves the whole lift has diameter <= D.
  * Adjacency is kept as per-dart slot arrays, so BFS does no division.
  * Order grows by one fibre step at a time, aiming just above the best order found.

Safety: Python checks every result with lib.is_valid and falls back to the best
construction it already holds (a Moore/record graph, or K_{d,d}). The C side checks
its final graph with a full all-pairs validator and falls back to K_{d,d} on failure.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 20000
#define MAXD 16
#define MAXP 4
#define MAXE (MAXV * MAXD / 2)

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ full validator */

/* Simple, degree <= d, bipartite, every pair within D. Used for input and final output. */
static int full_valid(int n, int m, const int *eu, const int *ev) {
    static int deg[MAXV];
    static int adj[MAXV][MAXD];
    static int col[MAXV], q[MAXV], dist[MAXV];
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return 0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] == v) return 0;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int h = 0, tl = 0;
        col[s] = 0;
        q[tl++] = s;
        while (h < tl) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (col[u] < 0) { col[u] = 1 - col[v]; q[tl++] = u; }
                else if (col[u] == col[v]) return 0;
            }
        }
    }
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, tl = 0, reached = 1;
        dist[s] = 0;
        q[tl++] = s;
        while (h < tl) {
            int v = q[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    reached++;
                    q[tl++] = u;
                }
            }
        }
        if (reached != n) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ best graph */

static int best_n = 0, best_m = 0;
static int best_eu[MAXE], best_ev[MAXE];

static void read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return;
    static int eu[MAXE], ev[MAXE];
    for (int e = 0; e < m; e++)
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) return;
    if (full_valid(n, m, eu, ev)) {
        best_n = n;
        best_m = m;
        memcpy(best_eu, eu, sizeof(int) * (size_t)m);
        memcpy(best_ev, ev, sizeof(int) * (size_t)m);
    }
}

static void set_complete(void) {
    best_n = 2 * d;
    best_m = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            best_eu[best_m] = a;
            best_ev[best_m] = d + b;
            best_m++;
        }
}

static void print_best(void) {
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", best_eu[e], best_ev[e]);
}

/* ------------------------------------------------------------ abelian lifts */

/* Group Z_m1 x Z_m2, element a*m2 + b. Base: p A-vertices, p B-vertices, d darts
 * per A-vertex given by d permutations perm[t]; dart (t,i) joins A_i to B_{perm[t][i]}
 * with voltage volt[t][i]. Vertex ids: A (i,x) -> i*N + x; B (j,y) -> P*N + j*N + y. */
static int P_, N_, m1_, m2_, NV;
static int perm[MAXD][MAXP];
static int volt[MAXD][MAXP];
static int nbr[MAXV][MAXD]; /* nbr[v][t] = neighbour of v through dart slot t */

static int gadd(int x, int g) {
    int a = x / m2_, b = x % m2_, c = g / m2_, e = g % m2_;
    int s = a + c;
    if (s >= m1_) s -= m1_;
    int r = b + e;
    if (r >= m2_) r -= m2_;
    return s * m2_ + r;
}

static void apply_volt(int t, int i, int g) {
    volt[t][i] = g;
    int j = perm[t][i];
    int A = i * N_, B = P_ * N_ + j * N_;
    for (int x = 0; x < N_; x++) {
        int a = A + x;
        int b = B + gadd(x, g);
        nbr[a][t] = b;
        nbr[b][t] = a;
    }
}

/* A dart voltage must differ from the voltages of other darts between the same pair. */
static int volt_ok(int t, int i, int g) {
    int j = perm[t][i];
    for (int u = 0; u < d; u++)
        if (u != t && perm[u][i] == j && volt[u][i] == g) return 0;
    return 1;
}

static int setup_lift(int p, int N, int m1, int m2) {
    P_ = p;
    N_ = N;
    m1_ = m1;
    m2_ = m2;
    NV = 2 * p * N;
    for (int t = 0; t < d; t++) {
        int a[MAXP];
        for (int i = 0; i < p; i++) a[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = a[i];
            a[i] = a[j];
            a[j] = s;
        }
        for (int i = 0; i < p; i++) perm[t][i] = a[i];
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) volt[t][i] = -1;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) {
            int ok = 0;
            for (int tries = 0; tries < 2000 && !ok; tries++) {
                int g = rndint(N);
                if (volt_ok(t, i, g)) {
                    volt[t][i] = g;
                    ok = 1;
                }
            }
            if (!ok) return 0;
        }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) apply_volt(t, i, volt[t][i]);
    return 1;
}

/* Sum over the 2p fibre representatives of the number of vertices NOT within D.
 * Translations are automorphisms, so 0 means the whole lift has diameter <= D. */
static long lift_bad(void) {
    static int vis[MAXV], q[MAXV];
    static int stamp = 0;
    long bad = 0;
    int PN = P_ * N_;
    for (int s = 0; s < 2 * P_; s++) {
        int src = s < P_ ? s * N_ : PN + (s - P_) * N_;
        stamp++;
        int h = 0, tl = 0;
        vis[src] = stamp;
        q[tl++] = src;
        for (int lev = 0; lev < D && h < tl; lev++) {
            int end = tl;
            while (h < end) {
                int v = q[h++];
                for (int k = 0; k < d; k++) {
                    int u = nbr[v][k];
                    if (vis[u] != stamp) {
                        vis[u] = stamp;
                        q[tl++] = u;
                    }
                }
            }
        }
        bad += NV - tl;
    }
    return bad;
}

/* Simulated annealing on the voltages until bad == 0 or time runs out. */
static int anneal(double until) {
    long bad = lift_bad();
    if (bad == 0) return 1;
    double ts = now();
    double span = until - ts;
    if (span <= 0) return 0;
    double T = 1.0;
    long s = 0;
    for (;;) {
        if ((s & 31) == 0) {
            double tn = now();
            if (tn >= until) return 0;
            T = 0.05 + (1.0 - (tn - ts) / span);
        }
        s++;
        int t = rndint(d), i = rndint(P_);
        int old = volt[t][i];
        int g = rndint(N_);
        if (g == old || !volt_ok(t, i, g)) continue;
        apply_volt(t, i, g);
        long nb = lift_bad();
        double delta = (double)(nb - bad) / N_;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            bad = nb;
            if (bad == 0) return 1;
        } else {
            apply_volt(t, i, old);
        }
    }
}

/* The current lift is valid (bad == 0 was reached). Copy it into the best graph. */
static void store_lift(void) {
    int m = 0;
    int A = P_ * N_;
    for (int a = 0; a < A; a++)
        for (int k = 0; k < d; k++) {
            best_eu[m] = a;
            best_ev[m] = nbr[a][k];
            m++;
        }
    best_n = NV;
    best_m = m;
}

static void search(double until, long cap) {
    int cur[MAXP + 1];
    for (int p = 0; p <= MAXP; p++) cur[p] = 0;
    int overflow = 0;
    while (now() < until) {
        if (best_n >= cap) break;
        int p = 1 + rndint(MAXP);
        int base = best_n / (2 * p);
        int N = (cur[p] > base ? cur[p] : base) + 1;
        if (N < d) N = d;
        if (2L * p * N > cap || 2 * p * N > MAXV) {
            if (++overflow > 200) break;
            continue;
        }
        overflow = 0;
        int dv[256], nd = 0;
        for (int k = 1; k <= N && nd < 256; k++)
            if (N % k == 0) dv[nd++] = k;
        int m1 = (rnd01() < 0.4) ? 1 : dv[rndint(nd)];
        int m2 = N / m1;
        double left = until - now();
        double slice = left * 0.1;
        if (slice < 0.3) slice = 0.3;
        double att = now() + slice;
        if (att > until) att = until;
        if (!setup_lift(p, N, m1, m2)) continue;
        if (anneal(att)) {
            cur[p] = N;
            store_lift();
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.8;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("1 0\n");
        return 0;
    }
    if (D == 1) {
        printf("2 1\n0 1\n");
        return 0;
    }

    read_start();
    long cap = moore_bound();
    if (cap > MAXV) cap = MAXV;
    if (best_n < cap) search(t_end, cap);
    if (best_n == 0 || !full_valid(best_n, best_m, best_eu, best_ev)) set_complete();
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


def _fallback(d, D):
    """A graph that is always valid for d >= 1, D >= 1: K_{d,d} when D >= 2, else K_2."""
    if D >= 2:
        g = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
        if lib.is_valid(*g, d, D):
            return g
    return (2, [(0, 1)]) if d >= 1 and D >= 1 else (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else _fallback(d, D)
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
