"""Multi-fibre bi-Cayley lift search for the degree-diameter bipartite problem.

Bold change from the parent: instead of one orbit per side (bi-Cayley), each side gets p in {1,2,3}
fibres. A base d-regular bipartite multigraph on p+p fibres is lifted over a random semidirect
product Z_m x|_r Z_k of order N, giving 2pN vertices. Voltages are annealed against an orbit
objective: left multiplication is an automorphism, so one BFS per fibre representative decides
diameter. Pair growth and ruin-and-recreate are dropped. The hexagon / projective-plane / W(q)
starts stay as the valid fallback, and every result is checked in C and again with lib.is_valid.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre lift search for bipartite degree-diameter graphs.
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
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 8192
#define MAXP 3
#define MAXDART (MAXD * MAXP)
#define BC_SPAN 200
#define BC_STEPS 4000
#define BC_ATTEMPTS 6
#define BC_GROUPS 4

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

/* Number of unordered vertex pairs at distance > D (bitset BFS from every vertex). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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

/* ---------------- semidirect groups Z_m x|_r Z_k ----------------
 * Element a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is index 0. */
typedef struct {
    int m, k, r;
    int rp[MAXG];
} Grp;
static Grp G;

static int gmul(int x, int y) {
    int a = x / G.k, b = x - a * G.k, c = y / G.k, e = y - c * G.k;
    return (int)(((long)a + (long)G.rp[b] * c) % G.m) * G.k + (b + e) % G.k;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / G.k, b = x - a * G.k;
    int nb = (G.k - b) % G.k;
    long v = (long)G.rp[nb] * a % G.m;
    int na = (int)((G.m - v) % G.m);
    return na * G.k + nb;
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
static int random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                bm = m; bk = k; br = r;
            }
        }
    }
    G.m = bm; G.k = bk; G.r = br;
    G.rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) G.rp[b] = (int)((long)G.rp[b - 1] * G.r % G.m);
    return count > 0;
}

/* Prefer a non-abelian choice (m > 1, k > 1, r != 1) when one is sampled quickly. */
static void pick_group(int N) {
    for (int t = 0; t < 8; t++) {
        random_group(N);
        if (G.m > 1 && G.k > 1 && G.r != 1) return;
    }
}

/* ---------------- multi-fibre base and lift ----------------
 * p A-fibres (0..p-1) and p B-fibres (p..2p-1), each of size N.
 * Darts t: A-fibre Di[t] -- B-fibre Dj[t] with voltage Dg[t]; Dinv[t] = Dg[t]^{-1}.
 * Vertex (fibre f, element x) has id f*N + x. Edge: A(i,x) -- B(j, x*g) for each dart (i,j,g). */
static int Di[MAXDART], Dj[MAXDART], Dg[MAXDART], Dinv[MAXDART];
static int ND, P_, N_;
static int Adart[MAXP][MAXD], Bdart[MAXP][MAXD];

/* Random d-regular bipartite base multigraph on p+p fibres, connected. */
static void make_base(int p) {
    int M[MAXP][MAXP];
    for (;;) {
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * p) break;
    }
    ND = 0;
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                Di[ND] = i;
                Dj[ND] = j;
                Adart[i][ca[i]++] = ND;
                Bdart[j][cb[j]++] = ND;
                ND++;
            }
}

static int clash_upto(int t, int g, int lim) {
    for (int s = 0; s < lim; s++)
        if (s != t && Di[s] == Di[t] && Dj[s] == Dj[t] && Dg[s] == g) return 1;
    return 0;
}

static void refresh_inv(void) {
    for (int t = 0; t < ND; t++) Dinv[t] = ginv(Dg[t]);
}

/* Random voltages keeping parallel darts (same fibre pair) distinct. */
static int init_voltages(void) {
    for (int t = 0; t < ND; t++) {
        int ok = 0;
        for (int tr = 0; tr < 4000; tr++) {
            int g = rndint(N_);
            if (!clash_upto(t, g, t)) { Dg[t] = g; ok = 1; break; }
        }
        if (!ok) return 0;
    }
    refresh_inv();
    return 1;
}

static void build_lift(Graph *g) {
    int p = P_, N = N_;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, Di[t] * N + x, (p + Dj[t]) * N + gmul(x, Dg[t]));
}

/* Orbit objective: sum over fibre representatives (identity element) of unreached vertices
 * beyond distance D. Zero iff the lift has diameter <= D. */
static int bq_d[MAXN], bq_s[MAXN], bq_q[MAXN];
static int bq_stamp = 0;

static long eval_bad(void) {
    int p = P_, N = N_, V = 2 * p * N;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int head = 0, tail = 0, src = s * N;
        bq_stamp++;
        bq_s[src] = bq_stamp;
        bq_d[src] = 0;
        bq_q[tail++] = src;
        while (head < tail) {
            int v = bq_q[head++];
            int dv = bq_d[v];
            if (dv >= D) continue;
            int f = v / N, x = v - f * N;
            if (f < p) {
                for (int t = 0; t < d; t++) {
                    int tt = Adart[f][t];
                    int u = (p + Dj[tt]) * N + gmul(x, Dg[tt]);
                    if (bq_s[u] != bq_stamp) {
                        bq_s[u] = bq_stamp;
                        bq_d[u] = dv + 1;
                        bq_q[tail++] = u;
                    }
                }
            } else {
                int j = f - p;
                for (int t = 0; t < d; t++) {
                    int tt = Bdart[j][t];
                    int u = Di[tt] * N + gmul(x, Dinv[tt]);
                    if (bq_s[u] != bq_stamp) {
                        bq_s[u] = bq_stamp;
                        bq_d[u] = dv + 1;
                        bq_q[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage hill-climb over the current base and group.
 * Temperature cools geometrically from 2.0 to 0.2 over BC_STEPS moves.
 * bestdg receives the voltages with the lowest objective seen. */
static long climb(int *bestdg, double until) {
    long bad = eval_bad();
    long bestb = bad;
    memcpy(bestdg, Dg, sizeof(int) * ND);
    double T = 2.0;
    const double alpha = pow(0.1, 1.0 / BC_STEPS);
    for (long s = 0; s < BC_STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(ND);
        int old = Dg[t], oldinv = Dinv[t];
        int nv = old, found = 0;
        for (int tr = 0; tr < 100; tr++) {
            nv = rndint(N_);
            if (nv != old && !clash_upto(t, nv, ND)) { found = 1; break; }
        }
        if (!found) { T *= alpha; if (T < 0.2) T = 0.2; continue; }
        Dg[t] = nv;
        Dinv[t] = ginv(nv);
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(bestdg, Dg, sizeof(int) * ND);
            }
        } else {
            Dg[t] = old;
            Dinv[t] = oldinv;
        }
        T *= alpha;
        if (T < 0.2) T = 0.2;
    }
    return bestb;
}

/* Search lifts of order 2pN strictly larger than the incumbent, over p in {1,2,3}.
 * On each success the bar is raised and the search continues from the new incumbent. */
static Graph cand;

static void lift_search(Graph *best, double until) {
    static int bestdg[MAXDART], elite[MAXDART];
    long moore = moore_bound();
    while (now() < until) {
        int ps[MAXP], np = 0;
        for (int p = 1; p <= MAXP; p++) {
            long Nlo = best->n / (2 * p) + 1;
            if (Nlo < d) Nlo = d;
            long Nmax = moore / (2 * p);
            if (Nmax > MAXG) Nmax = MAXG;
            if (Nmax > MAXN / (2 * p)) Nmax = MAXN / (2 * p);
            if (Nlo <= Nmax) ps[np++] = p;
        }
        if (!np) return;
        int p = ps[rndint(np)];
        long Nlo = best->n / (2 * p) + 1;
        if (Nlo < d) Nlo = d;
        long Nmax = moore / (2 * p);
        if (Nmax > MAXG) Nmax = MAXG;
        if (Nmax > MAXN / (2 * p)) Nmax = MAXN / (2 * p);
        long span = Nmax - Nlo + 1;
        if (span > BC_SPAN) span = BC_SPAN;
        /* Bias toward the lowest open orders, while still reaching the upper window. */
        double u = rnd01();
        long N = Nlo + (long)(u * sqrt(u) * span);
        if (N > Nmax) N = Nmax;

        int improved = 0;
        for (int grp = 0; grp < BC_GROUPS && now() < until && !improved; grp++) {
            pick_group((int)N);
            P_ = p;
            N_ = (int)N;
            make_base(p);
            long elite_bad = -1;
            for (int att = 0; att < BC_ATTEMPTS && now() < until; att++) {
                if (elite_bad >= 0 && rnd01() < 0.6) {
                    memcpy(Dg, elite, sizeof(int) * ND);
                    refresh_inv();
                    int t = rndint(ND), nv = 0, tr = 0;
                    do { nv = rndint(N_); tr++; } while (clash_upto(t, nv, ND) && tr < 4000);
                    if (!clash_upto(t, nv, ND)) { Dg[t] = nv; Dinv[t] = ginv(nv); }
                } else {
                    if (!init_voltages()) break;
                }
                long b = climb(bestdg, until);
                if (b == 0) {
                    memcpy(Dg, bestdg, sizeof(int) * ND);
                    refresh_inv();
                    build_lift(&cand);
                    if (cand.n > best->n && is_valid(&cand)) {
                        copy_graph(best, &cand);
                        improved = 1;
                        break;
                    }
                    continue;
                }
                if (elite_bad < 0 || b < elite_bad) {
                    elite_bad = b;
                    memcpy(elite, bestdg, sizeof(int) * ND);
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
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) lift_search(&best, t_end);

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
    builders = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        builders.append(lambda: lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        builders.append(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        builders.append(lambda: _hexagon_incidence(d - 1))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            builders.append(lambda: _gq_w(q))
    out = []
    for make in builders:
        try:
            out.append(make())
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    # Leave room for the one-off C compile and the Python overhead.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
