"""Bold variant for the d=5, D=7 target: fibre-lift search with p = 2..6 base fibres.

Changes versus the parent:
  * The C engine no longer relies on the one-fibre-per-attempt lift search, which stalled. Its
    main phase is a new voltage search over lifts of a d-regular bipartite base multigraph with
    p fibres per side (2p fibres total), over admissible semidirect groups Z_N x| Z_k. The base is
    kept implicit, and the diameter objective counts unreachable (source fibre, vertex) pairs for
    2p fibre representatives. Left multiplication is transitive on each fibre, so these sources
    suffice. Voltages are annealed, and the search aims for orders just above the current best.
    For d=5 the target 3110 = 2 * 5 * 311 corresponds to p=5, N=311.
  * A short bi-Cayley phase (25% of the engine budget) runs first, so the parent's 2842 is kept
    as a floor. The remaining budget goes to the fibre-lift search.
  * Algebraic starts (hexagon incidence H(q), W(q), PG(2,q), Araujo-Lopez) are unchanged and
    remain the fallback. Every result is checked with lib.is_valid before it is returned.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (fibre-lift + bi-Cayley).
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
#define MAXP 8
#define MAXG 2048
#define MAXDARTS (MAXP * MAXD)
#define BC_SPAN 60
#define BC_STEPS 20000
#define BC_ATTEMPTS 4
#define BC_GROUPS 6
#define LIFT_STEPS 16000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXG];
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
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
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
            if (rndint((int)count) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* Prefer a non-abelian choice (r != 1, k > 1) when one is sampled quickly. */
static int pick_group_bc(int N, Grp *G) {
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

/* Shared multiplication table of the current group (order GN). */
static int GN;
static int MT[MAXG * MAXG];
static int INV[MAXG];

static void setup_group(int N, const Grp *G) {
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* ---------------- fibre-lift search ----------------
 * Base: d-regular bipartite multigraph on p + p fibres (darts i -> j).
 * Lift: fibre A_i element x joins fibre B_j element x*g for each dart (i,j,g).
 * Vertices: A_i,x -> i*N + x; B_j,y -> p*N + j*N + y. Degree d everywhere.
 * Orbit objective: unreached (source fibre rep, vertex) pairs within distance D. */

static int P_, N_, nd_;
static int dI[MAXDARTS], dJ[MAXDARTS], dG[MAXDARTS];
static int outA[MAXP][MAXD], nOut[MAXP], inB[MAXP][MAXD], nIn[MAXP];
static int vmark[MAXN], bq[MAXN], bdist[MAXN];
static int vstamp = 0;

static int make_base(int p) {
    for (int attempt = 0; attempt < 200; attempt++) {
        nd_ = 0;
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) {
                dI[nd_] = i; dJ[nd_] = perm[i]; dG[nd_] = -1; nd_++;
            }
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, cnt = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int t = 0; t < nd_; t++) {
                int a = dI[t], b = p + dJ[t];
                if (a == v && !seen[b]) { seen[b] = 1; cnt++; st[top++] = b; }
                else if (b == v && !seen[a]) { seen[a] = 1; cnt++; st[top++] = a; }
            }
        }
        if (cnt == 2 * p) {
            for (int i = 0; i < p; i++) { nOut[i] = 0; nIn[i] = 0; }
            for (int t = 0; t < nd_; t++) {
                outA[dI[t]][nOut[dI[t]]++] = t;
                inB[dJ[t]][nIn[dJ[t]]++] = t;
            }
            return 1;
        }
    }
    return 0;
}

/* True if giving dart t the voltage g duplicates another dart on the same fibre pair. */
static int clash(int t, int g) {
    for (int s = 0; s < nd_; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == g) return 1;
    return 0;
}

static long orbit_bad(void) {
    int p = P_, N = N_, V = 2 * p * N, PN = p * N;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s < p ? s * N : PN + (s - p) * N;
        vstamp++;
        int head = 0, tail = 0;
        vmark[src] = vstamp;
        bdist[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            int dv = bdist[v];
            if (dv >= D) continue;
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < nOut[i]; k++) {
                    int t = outA[i][k];
                    int u = PN + dJ[t] * N + MT[x * N + dG[t]];
                    if (vmark[u] != vstamp) { vmark[u] = vstamp; bdist[u] = dv + 1; bq[tail++] = u; }
                }
            } else {
                int w = v - PN, j = w / N, y = w - j * N;
                for (int k = 0; k < nIn[j]; k++) {
                    int t = inB[j][k];
                    int u = dI[t] * N + MT[y * N + INV[dG[t]]];
                    if (vmark[u] != vstamp) { vmark[u] = vstamp; bdist[u] = dv + 1; bq[tail++] = u; }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static long anneal_lift(long steps, double until) {
    long bad = orbit_bad();
    double T = 3.0, f = pow(0.1, 1.0 / (double)steps);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd_);
        int old = dG[t];
        int ng = rndint(N_);
        if (ng == old || clash(t, ng)) { T *= f; continue; }
        dG[t] = ng;
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dG[t] = old;
        T *= f;
    }
    return bad;
}

static void build_lift(Graph *g) {
    int p = P_, N = N_;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, p * N + dJ[t] * N + MT[x * N + dG[t]]);
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    static const int PCH[6] = {2, 3, 4, 5, 5, 6};
    long moore = moore_bound();
    while (now() < until) {
        int p = PCH[rndint(6)];
        long target = best->n + 1;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2 * p * N > MAXN || N > MAXG) continue;
        if (!random_group(N, &G)) continue;
        setup_group(N, &G);
        P_ = p; N_ = N;
        if (!make_base(p)) continue;
        for (int t = 0; t < nd_; t++) {
            do { dG[t] = rndint(N); } while (clash(t, dG[t]));
        }
        long bad = anneal_lift(LIFT_STEPS, until);
        if (bad == 0) {
            build_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- bi-Cayley lift search ----------------
 * a_x = x (side 0), b_x = N + x (side 1); edges a_x -- b_{x*g_t}, g_0 = e. */

static int bcmark[MAXN], bcdist[MAXN], bcq[MAXN];
static int bcstamp = 0;

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

static long eval_bad_bc(const int *gv) {
    int N = GN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INV[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        bcstamp++;
        bcmark[src] = bcstamp;
        bcdist[src] = 0;
        bcq[tail++] = src;
        while (head < tail) {
            int v = bcq[head++];
            int dv = bcdist[v];
            if (dv >= D) continue;
            for (int t = 0; t < d; t++) {
                int u = v < N ? N + MT[v * N + gv[t]] : MT[(v - N) * N + gi[t]];
                if (bcmark[u] != bcstamp) {
                    bcmark[u] = bcstamp;
                    bcdist[u] = dv + 1;
                    bcq[tail++] = u;
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static long climb_bc(int *gv, double until) {
    long bad = eval_bad_bc(gv);
    double T = 2.0;
    for (long s = 0; s < BC_STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(GN); } while (used_upto(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad_bc(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[t] = old;
        T *= 0.9997;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

static void build_bc(Graph *g, int N, const int *gv) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MT[x * N + gv[t]]);
}

static void bicayley_search(Graph *best, double until) {
    static int gv[MAXD];
    static Grp G;
    static Graph bc;
    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXG) Nmax_l = MAXG;
    if (Nmax_l > MAXN / 2) Nmax_l = MAXN / 2;
    int Nmax = (int)Nmax_l;
    int Nlo = best->n / 2 + 1;
    if (Nlo < d + 1) Nlo = d + 1;
    while (now() < until && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > BC_SPAN) span = BC_SPAN;
        double u = rnd01();
        int N = Nlo + (int)(u * u * span);
        if (N > Nmax) N = Nmax;
        int success = 0;
        for (int grp = 0; grp < BC_GROUPS && now() < until && !success; grp++) {
            if (!pick_group_bc(N, &G)) break;
            setup_group(N, &G);
            for (int att = 0; att < BC_ATTEMPTS && now() < until; att++) {
                gv[0] = 0;
                for (int t = 1; t < d; t++) {
                    do { gv[t] = rndint(N); } while (used_upto(gv, t, gv[t]));
                }
                if (climb_bc(gv, until) != 0) continue;
                build_bc(&bc, N, gv);
                if (bc.n > best->n && is_valid(&bc)) {
                    copy_graph(best, &bc);
                    Nlo = N + 1;
                    success = 1;
                    break;
                }
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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double L = t_end - t0;
    long moore = moore_bound();
    if (D >= 2 && d >= 3 && best.n < moore) {
        bicayley_search(&best, t0 + L * 0.25);
        if (best.n < moore) lift_search(&best, t_end);
    }
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 3)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
