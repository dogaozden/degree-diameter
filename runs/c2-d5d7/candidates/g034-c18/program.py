"""Frobenius-biased bi-Cayley lift search for the d=5, D=7 target.

Previous approach: start from the Hexagon incidence graph H(4) (order 2730, degree 5, diameter 6)
and grow it with pairs or random semidirect bi-Cayley lifts. This version changes the group family.
Records of this size often factor as 2 * (group order), and 3110 = 2 * 5 * 311 with 311 = 1 mod 5,
which is exactly the order of the Frobenius group Z_311 x| Z_5. So the C engine now searches
bi-Cayley graphs BCG(G, S) over Frobenius groups Z_p x| Z_k (N = p*k, k | p-1, k >= 2, action of
order k), chosen with probability 0.7 when available. Otherwise it falls back to random
non-abelian semidirect products. Each bi-Cayley graph has 2N vertices, degree d, and is bipartite
by construction. A voltage set S = {g_0 = e, g_1, ..., g_{d-1}} is annealed until the orbit BFS from
a_e and b_e reaches every vertex within D. The C engine verifies every candidate by full bitset
check before it is accepted. The search keeps the incumbent order window [best/2 + 1, ...], so it
only accepts strictly larger graphs. The start graph is an algebraic fallback, and build() validates
the output with lib.is_valid before returning it.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search with Frobenius-biased group choice.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXH 2048
#define BC_SPAN 200
#define BC_STEPS 6000
#define BC_ATTEMPTS 4
#define BC_GROUPS 6
#define FROB_PROB 0.7

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered vertex pairs at distance > D (bitset closure). */
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

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

static int is_prime_int(int x) {
    if (x < 2) return 0;
    for (int f = 2; f * f <= x; f++)
        if (x % f == 0) return 0;
    return 1;
}

/* Smallest primitive root modulo the prime p (p >= 3). */
static int primitive_root(int p) {
    int m0 = p - 1;
    for (int g = 2; g < p; g++) {
        int ok = 1, m = m0;
        for (int f = 2; f <= m && ok; f++) {
            if (m % f == 0) {
                if (powmod(g, (p - 1) / f, p) == 1) ok = 0;
                while (m % f == 0) m /= f;
            }
        }
        if (ok) return g;
    }
    return 2;
}

/* Number of primes p with N = p*k, k >= 2 and k | p-1 (Frobenius group Z_p x| Z_k). */
static int frob_count(int N) {
    int c = 0;
    for (int p = 3; p <= N; p++) {
        if (N % p) continue;
        int k = N / p;
        if (k >= 2 && (p - 1) % k == 0 && is_prime_int(p)) c++;
    }
    return c;
}

/* Random Frobenius group Z_p x| Z_k of order N, with the generator acting with order exactly k. */
static int frob_group(int N, Grp *G) {
    int cand[64], nc = 0;
    for (int p = 3; p <= N && nc < 64; p++) {
        if (N % p) continue;
        int k = N / p;
        if (k >= 2 && (p - 1) % k == 0 && is_prime_int(p)) cand[nc++] = p;
    }
    if (!nc) return 0;
    int p = cand[rndint(nc)];
    int k = N / p;
    int g = primitive_root(p);
    int j;
    do { j = 1 + rndint(k - 1); } while (gcd(j, k) != 1);
    long r = powmod(g, (long)((p - 1) / k) * j, p);
    G->m = p;
    G->k = k;
    G->r = (int)r;
    G->rp[0] = 1 % p;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % p);
    return 1;
}

/* Frobenius group with probability FROB_PROB when available, otherwise a non-abelian semidirect product. */
static int pick_group(int N, Grp *G) {
    if (rnd01() < FROB_PROB && frob_count(N) > 0) return frob_group(N, G);
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

/* ---------------- bi-Cayley lift search ----------------
 * Vertices: a_x = x (side 0), b_x = N + x (side 1), x in G.
 * Edges: a_x -- b_{x * g_t} for t = 0..d-1, with g_0 = e and distinct g_t.
 * Left multiplication is transitive on each side, so BFS from a_e and b_e suffices. */

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int NN;
static int dist_bc[2 * MAXH], seen_bc[2 * MAXH], q_bc[2 * MAXH];
static int stamp_bc = 0;

static void setup_group(int N, const Grp *G) {
    NN = N;
    for (int x = 0; x < N; x++) {
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) row[y] = gmul(G, x, y);
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

/* Number of (source, vertex) pairs at distance > D, sources a_e and b_e. */
static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_bc++;
        seen_bc[src] = stamp_bc;
        dist_bc[src] = 0;
        q_bc[tail++] = src;
        while (head < tail) {
            int v = q_bc[head++];
            int dv = dist_bc[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MTAB + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            } else {
                const int *row = MTAB + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_bc[u] != stamp_bc) {
                        seen_bc[u] = stamp_bc;
                        dist_bc[u] = dv + 1;
                        q_bc[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage search; gv[0] = 0 stays fixed.
 * Phase 0 cools from 2.0 to 0.2 over BC_STEPS moves. If defects remain, phase 1 reheats from the
 * best voltage set at T = 0.6 for BC_STEPS/2 moves. Returns the best objective seen. */
static long climb(int *gv, int *bestgv, double until) {
    long bad = eval_bad(gv);
    long bestb = bad;
    memcpy(bestgv, gv, sizeof(int) * d);
    for (int phase = 0; phase < 2 && bestb > 0; phase++) {
        long steps = phase == 0 ? BC_STEPS : BC_STEPS / 2;
        double T = phase == 0 ? 2.0 : 0.6;
        const double alpha = pow(0.1, 1.0 / (double)steps);
        if (phase == 1) {
            memcpy(gv, bestgv, sizeof(int) * d);
            bad = bestb;
        }
        for (long s = 0; s < steps && bad > 0; s++) {
            if ((s & 127) == 0 && now() > until) break;
            int t = 1 + rndint(d - 1);
            int old = gv[t], nv;
            do { nv = rndint(NN); } while (used_upto(gv, d, nv));
            gv[t] = nv;
            long nb = eval_bad(gv);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
                if (bad < bestb) {
                    bestb = bad;
                    memcpy(bestgv, gv, sizeof(int) * d);
                }
            } else {
                gv[t] = old;
            }
            T *= alpha;
            if (T < 0.2) T = 0.2;
        }
        if (now() > until) break;
    }
    return bestb;
}

static void build_bc(Graph *g, int N, const int *gv) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MTAB[(size_t)x * N + gv[t]]);
}

/* Search bi-Cayley lifts of order 2N > best->n, raising the bar after each success. */
static void bicayley_search(Graph *best, double until) {
    static int gv[MAXD], bestgv[MAXD], elite[MAXD];
    static Grp G;
    static Graph cand;
    int Nlo = best->n / 2 + 1;
    if (Nlo < d + 1) Nlo = d + 1;
    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXH) Nmax_l = MAXH;
    if (Nmax_l > MAXN / 2) Nmax_l = MAXN / 2;
    int Nmax = (int)Nmax_l;
    while (now() < until && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > BC_SPAN) span = BC_SPAN;
        /* Bias toward the lowest open orders, which are the likeliest to succeed. */
        double u = rnd01();
        int N = Nlo + (int)(u * sqrt(u) * span);
        if (N > Nlo + span - 1) N = Nlo + span - 1;
        int success = 0;
        for (int grp = 0; grp < BC_GROUPS && now() < until && !success; grp++) {
            if (!pick_group(N, &G)) break;
            setup_group(N, &G);
            long elite_bad = -1;
            for (int att = 0; att < BC_ATTEMPTS && now() < until; att++) {
                if (elite_bad >= 0 && rnd01() < 0.6) {
                    memcpy(gv, elite, sizeof(int) * d);
                    int t = 1 + rndint(d - 1);
                    int nv;
                    do { nv = rndint(N); } while (used_upto(gv, d, nv));
                    gv[t] = nv;
                } else {
                    gv[0] = 0;
                    for (int t = 1; t < d; t++) {
                        int nv;
                        do { nv = rndint(N); } while (used_upto(gv, t, nv));
                        gv[t] = nv;
                    }
                }
                long b = climb(gv, bestgv, until);
                if (b == 0) {
                    build_bc(&cand, N, bestgv);
                    if (cand.n > best->n && is_valid(&cand)) {
                        copy_graph(best, &cand);
                        success = 1;
                        break;
                    }
                    continue;
                }
                if (elite_bad < 0 || b < elite_bad) {
                    elite_bad = b;
                    memcpy(elite, bestgv, sizeof(int) * d);
                }
            }
        }
        if (success) Nlo = N + 1;
    }
}

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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && d >= 3 && best.n < moore_bound())
        bicayley_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    try:
        for cand in known_starts(d, D):
            n, e = cand
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    except Exception:
        pass

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
