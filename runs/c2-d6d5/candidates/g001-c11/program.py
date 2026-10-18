"""Vertex-transitive bi-Cayley search for the degree-diameter problem.

Construction: for a group G of order N and a connection set S of d distinct elements,
join a_x to b_{xs} for s in S. This gives a bipartite d-regular graph on 2N vertices.
Left multiplication by G is an automorphism group that is transitive on each side, so
diameter <= D reduces to two BFS runs, one from a_e and one from b_e. That makes each
evaluation O(N d), and simulated annealing over S can afford many more steps than
generic edge-swap search. The C engine climbs the order N one step at a time from K_{d,d},
so it always has a valid graph to return.

Groups are semidirect products Z_m x| Z_k with r^k = 1 mod m. Small cases and
Moore-type targets are handled in Python without the C run.
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

#define MAXG 1100
#define MAXN (2 * MAXG)
#define MAXD 64
#define MAXW (MAXN / 64 + 1)

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

/* ------------------------------------------------------------ graph storage */

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, element (a, b) coded a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int N;
static int Gm, Gk, Gr;
static int rp[MAXG], rpinv[MAXG];

static inline int gmul(int x, int y) {
    int a = x / Gk, b = x - a * Gk;
    int c = y / Gk, e = y - c * Gk;
    int t = (int)(((long)a + (long)rp[b] * c) % Gm);
    int f = b + e;
    if (f >= Gk) f -= Gk;
    return t * Gk + f;
}

static int ginv(int x) {
    int a = x / Gk, b = x - a * Gk;
    int nb = (Gk - b) % Gk;
    long c = ((long)(Gm - a) % Gm) * rpinv[b] % Gm;
    return (int)c * Gk + nb;
}

static void set_group(int m, int k, int r) {
    Gm = m; Gk = k; Gr = r; N = m * k;
    int rinv = 0;
    if (m > 1)
        for (int t = 1; t < m; t++)
            if ((long)r * t % m == 1) { rinv = t; break; }
    rp[0] = 1 % m;
    rpinv[0] = 1 % m;
    for (int b = 1; b < k; b++) {
        rp[b] = (int)((long)rp[b - 1] * r % m);
        rpinv[b] = (int)((long)rpinv[b - 1] * rinv % m);
    }
}

/* Uniform random semidirect group of order n (reservoir sampling over (m, k, r)). */
static void random_group(int n) {
    int cm = 1, ck = n, cr = 0;
    long cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { cm = 1; ck = k; cr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { cm = m; ck = k; cr = r; }
        }
    }
    set_group(cm, ck, cr);
}

/* ------------------------------------------------------------ connection set */

static int S[MAXD], Si[MAXD];

static int in_set(int g, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == g) return 1;
    return 0;
}

static void random_S(void) {
    for (int i = 0; i < d; i++) {
        int g;
        do { g = rndint(N); } while (in_set(g, i));
        S[i] = g;
        Si[i] = ginv(g);
    }
}

/* ------------------------------------------------------------ fast evaluation */

static int dist_[MAXN], que[MAXN], stamp_[MAXN], stampv = 0;

/* BFS from src (A index x < N, B index N + y) up to radius D.
 * Counts the A-vertices and B-vertices reached. */
static void bfs(int src, int *cntA, int *cntB) {
    stampv++;
    int head = 0, tail = 0, ca = 0, cb = 0;
    stamp_[src] = stampv;
    dist_[src] = 0;
    que[tail++] = src;
    while (head < tail) {
        int v = que[head++];
        int dv = dist_[v];
        if (v < N) ca++; else cb++;
        if (dv >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int w = N + gmul(v, S[i]);
                if (stamp_[w] != stampv) {
                    stamp_[w] = stampv;
                    dist_[w] = dv + 1;
                    que[tail++] = w;
                }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int w = gmul(y, Si[i]);
                if (stamp_[w] != stampv) {
                    stamp_[w] = stampv;
                    dist_[w] = dv + 1;
                    que[tail++] = w;
                }
            }
        }
    }
    *cntA = ca;
    *cntB = cb;
}

/* Zero iff diameter <= D. Vertex transitivity: a_e must reach everything,
 * and b_e must reach every B-vertex. */
static long cost_of(void) {
    int ca, cb, ca2, cb2;
    bfs(0, &ca, &cb);
    bfs(N, &ca2, &cb2);
    return (long)(2 * N - ca - cb) + (long)(N - cb2);
}

/* Simulated annealing over S for the current group. Returns the final cost. */
static long anneal(int maxit) {
    long cur = cost_of();
    for (int it = 0; it < maxit && cur > 0; it++) {
        if ((it & 127) == 0 && now() > t_end) break;
        double T = 2.0 * (1.0 - (double)it / maxit) + 0.15;
        int i = rndint(d);
        int old = S[i], oldi = Si[i];
        int g;
        do { g = rndint(N); } while (in_set(g, d));
        S[i] = g;
        Si[i] = ginv(g);
        long c = cost_of();
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) {
            cur = c;
        } else {
            S[i] = old;
            Si[i] = oldi;
        }
    }
    return cur;
}

/* Explicit bi-Cayley graph for the current group and S. */
static void graph_from_S(Graph *g) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + gmul(x, S[i]));
}

/* ------------------------------------------------------------ main */

static Graph best, cand;
static int bestN;

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (D < 2) {
        if (d >= 1 && D >= 1) printf("2 1\n0 1\n");
        else printf("1 0\n");
        return 0;
    }
    if (d < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }

    /* Start from K_{d,d}, the bi-Cayley graph of Z_d with S = Z_d. */
    set_group(1, d, 0);
    for (int i = 0; i < d; i++) {
        S[i] = i;
        Si[i] = ginv(i);
    }
    graph_from_S(&best);
    bestN = d;

    /* Climb the group order one step at a time. Every success is a valid fallback. */
    while (now() < t_end) {
        int target = bestN + 1;
        if (target > MAXG || 2L * target > moore_bound()) break;
        random_group(target);
        random_S();
        long c = anneal(40000);
        if (c == 0) {
            graph_from_S(&cand);
            if (cand.n > best.n && bad_pairs(&cand) == 0) {
                best = cand;
                bestN = target;
            }
        }
    }
    print_graph(&best);
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


def _complete_bipartite(d):
    return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]


def _even_cycle(n):
    return n, [(i, (i + 1) % n) for i in range(n)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D <= 0 or d <= 0:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])
    if d == 1:
        return (2, [(0, 1)])

    start = known_start(d, D)
    if start is None:
        if d == 2:
            start = _even_cycle(2 * D)       # C_{2D}: bipartite, diameter D
        else:
            start = _complete_bipartite(d)   # diameter 2, always valid for D >= 2
    best = start
    if not lib.is_valid(best[0], best[1], d, D):
        best = _complete_bipartite(d)

    if best[0] >= lib.moore_bound(d, D):
        return best
    if d == 2:
        return best

    budget = 0.85 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
