"""Multi-fibre voltage-lift search for the d=5, D=7 target.

Start: the incidence graph of the split Cayley hexagon H(q), q = d-1 in {2, 4}. It is bipartite,
degree d, diameter 6, so it is valid for D = 7 (K_{d,d} is the fallback).

Main change in this version: the C engine searches voltage lifts of a random d-regular bipartite
base multigraph on p + p fibres (p = 1..6) over a random admissible semidirect product Z_m x|_r Z_k
of order N, with 2pN just above the incumbent. Lifts are evaluated without building the graph:
each fibre is transitive under left multiplication, so one BFS per fibre (2p BFS runs) gives the
exact all-pairs diameter check. Voltages are annealed against that count. Successful lifts are
rebuilt explicitly, checked with is_valid, and become the new incumbent. Failed runs restart from
their best voltage set with one voltage re-drawn, or from fresh random darts.

Safety: every candidate is checked in C and again in Python with lib.is_valid. The start graph is
returned unchanged if the search finds nothing larger, so every case still returns a valid graph.
"""
import time
import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Voltage-lift search for bipartite degree-diameter graphs.
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

#define MAXN 8192
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXP 6
#define MAXND (MAXP * MAXD)
#define ATTEMPTS 4
#define ANNEAL_STEPS 3000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

typedef struct {
    int m, k, r;
    int rp[MAXN];   /* rp[b] = r^b mod m */
} Grp;

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
    long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        pw *= (d - 1);
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
static int badv[MAXN];

/* Exact count of unordered vertex pairs at distance > D (bitset BFS). */
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
        badv[v] = n - c;
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

/* ---------------- groups: Z_m x|_r Z_k, element a*k + b ----------------
 * (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is index 0. */

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long t = (long)G->rp[nb] * a % G->m;
    int c = (int)((G->m - t) % G->m);
    return c * G->k + nb;
}

/* Uniform random admissible semidirect product of order N (reservoir sampling over (m, r)). */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rnd() % (uint64_t)count == 0) { G->m = 1; G->k = N; G->r = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rnd() % (uint64_t)count == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    if (count == 0) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ---------------- base multigraph and voltages ---------------- */

/* Random connected d-regular bipartite base multigraph on p + p fibres.
 * Fills dt with d*p darts (g = -1, to be assigned) and returns d*p, or 0 on failure. */
static int make_darts(int p, Dart *dt) {
    int M[MAXP][MAXP];
    int ok = 0;
    for (int tries = 0; tries < 1000 && !ok; tries++) {
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP], st[2 * MAXP], top = 0, ns = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = (v < p) ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * p) ok = 1;
    }
    if (!ok) return 0;
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = -1;
                nd++;
            }
    return nd;
}

/* Random voltage for dart skip that avoids the voltages of the other darts on the same (i,j). */
static int fresh_voltage(const Dart *dt, int nd, int skip, int N) {
    int i = dt[skip].i, j = dt[skip].j;
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int s = 0; s < nd; s++)
            if (s != skip && dt[s].i == i && dt[s].j == j && dt[s].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* ---------------- fast lift evaluation ----------------
 * Fibre f < p is A-side, f >= p is B-side. Edge (i,x)--(p+j, x*g) for each dart (i,j,g).
 * Left multiplication is an automorphism, so BFS from (f, identity) for each fibre f gives
 * the exact all-pairs distance information. Return the total number of unreached pairs. */

static int NBF[2 * MAXP][MAXD];
static int NBG[2 * MAXP][MAXD];
static int lseen[MAXN], ldist[MAXN], lq[MAXN];
static int lstamp = 0;

static long lift_eval(int p, int N, const Grp *G, const Dart *dt, int nd) {
    int c[2 * MAXP];
    for (int f = 0; f < 2 * p; f++) c[f] = 0;
    for (int t = 0; t < nd; t++) {
        int a = dt[t].i, b = p + dt[t].j, g = dt[t].g;
        NBF[a][c[a]] = b;
        NBG[a][c[a]] = g;
        c[a]++;
        NBF[b][c[b]] = a;
        NBG[b][c[b]] = ginv(G, g);
        c[b]++;
    }
    int V = 2 * p * N;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        lstamp++;
        int head = 0, tail = 0;
        lseen[src] = lstamp;
        ldist[src] = 0;
        lq[tail++] = src;
        while (head < tail) {
            int v = lq[head++];
            int dv = ldist[v];
            if (dv >= D) continue;
            int f = v / N, x = v - f * N;
            for (int t = 0; t < d; t++) {
                int u = NBF[f][t] * N + gmul(G, x, NBG[f][t]);
                if (lseen[u] != lstamp) {
                    lseen[u] = lstamp;
                    ldist[u] = dv + 1;
                    lq[tail++] = u;
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Anneal the voltages of a fixed base. Returns the best objective seen; bdt receives its darts. */
static long anneal(int p, int N, const Grp *G, Dart *dt, int nd, int steps, double until, Dart *bdt) {
    long bad = lift_eval(p, N, G, dt, nd);
    long bestb = bad;
    memcpy(bdt, dt, sizeof(Dart) * nd);
    double T0 = 1.0 + 0.02 * (double)bad;
    double Tend = 0.05;
    double alpha = exp(log(Tend / T0) / (double)steps);
    double T = T0;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, N);
        long nb = lift_eval(p, N, G, dt, nd);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(bdt, dt, sizeof(Dart) * nd);
            }
        } else {
            dt[t].g = old;
        }
        T *= alpha;
    }
    return bestb;
}

static void build_lift_graph(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, (p + dt[t].j) * N + gmul(G, x, dt[t].g));
}

/* Search lifts of order 2pN > best->n, keeping only graphs that pass the full check. */
static void lift_search(Graph *best, double until) {
    static Dart dt[MAXND], bdt[MAXND], elite[MAXND];
    static Grp G;
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int p = 1 + rndint(MAXP);
        int Nmin = best->n / (2 * p) + 1;
        if (Nmin < d + 2) Nmin = d + 2;
        int N = Nmin + rndint(3);
        if ((long)2 * p * N > moore || 2 * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        int have_elite = 0;
        for (int att = 0; att < ATTEMPTS && now() < until; att++) {
            int nd;
            if (have_elite && rnd01() < 0.5) {
                nd = d * p;
                memcpy(dt, elite, sizeof(Dart) * nd);
                int t = rndint(nd);
                dt[t].g = fresh_voltage(dt, nd, t, N);
            } else {
                nd = make_darts(p, dt);
                if (nd == 0) break;
                for (int t = 0; t < nd; t++) dt[t].g = fresh_voltage(dt, nd, t, N);
            }
            long b = anneal(p, N, &G, dt, nd, ANNEAL_STEPS, until, bdt);
            if (b == 0) {
                build_lift_graph(&cand, p, N, &G, bdt, nd);
                if (cand.n > best->n && is_valid(&cand)) {
                    copy_graph(best, &cand);
                    break;
                }
            } else {
                memcpy(elite, bdt, sizeof(Dart) * nd);
                have_elite = 1;
            }
        }
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
    read_start(&best);
    if (d < 2 || d > MAXD || D < 2) {
        print_graph(&best);
        return 0;
    }
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);
    if (best.n < moore_bound()) lift_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


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


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        try:
            out.append(lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            out.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
