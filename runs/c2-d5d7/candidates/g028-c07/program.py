"""d=5, D=7 search via multi-fibre voltage lifts (new construction).

Start: incidence graph of the split Cayley hexagon H(4) (2730 vertices, diameter 6, so valid
for D=7), or K_{d,d} / projective-plane incidence if that fails.

C engine: a lift with p fibres on each side (p = 1..4) over a random admissible semidirect
product G = Z_m x| Z_k of order N. The base is d random perfect matchings between the fibres
(a d-regular bipartite base multigraph). Each dart (i,k) carries a voltage g in G, joining
A(i,x) to B(j, x*g). Left multiplication is an automorphism that is transitive on each fibre,
so the diameter test only needs BFS from one vertex per fibre (2p BFS runs). Simulated annealing
over voltages minimises the number of unreached (source, vertex) pairs. The target order 2pN is
just above the incumbent. Every candidate is re-checked with the full bitset diameter test in C
and again with lib.is_valid in Python. Otherwise the previous valid graph is returned.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
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
#define MAXP 4
#define ATT 4
#define STEPS 10000
#define WIN 8

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXH];
} Grp;

static int d, D;
static double t_end;
static Graph best, cand;
static Grp G;
static int NG, PF;
static int JJ[MAXP][MAXD], GG[MAXP][MAXD];
static int RI[MAXP][MAXD], RK[MAXP][MAXD];
static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int stv[MAXN], dist_v[MAXN], qv[MAXN];
static int stc = 0;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

/* Number of unordered vertex pairs at distance > D (bitset BFS). */
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

/* Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k, b = x % g->k, c = y / g->k, e = y % g->k;
    return (int)((a + (long)g->rp[b] * c) % g->m) * g->k + (b + e) % g->k;
}

static int random_group(int N, Grp *g) {
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
                g->m = m; g->k = k; g->r = r;
            }
        }
    }
    if (!count) return 0;
    g->rp[0] = 1 % g->m;
    for (int b = 1; b < g->k; b++) g->rp[b] = (int)((long)g->rp[b - 1] * g->r % g->m);
    return 1;
}

/* Prefer a non-abelian group when one is sampled quickly. */
static int pick_group(int N, Grp *g) {
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, g)) return 0;
        if (g->m > 1 && g->k > 1 && g->r != 1) return 1;
    }
    return 1;
}

static void setup_group(int N) {
    NG = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MTAB[(size_t)x * N + y] = gmul(&G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MTAB[(size_t)x * N + y] == 0) { INVT[x] = y; break; }
}

/* Base: d random permutations of the PF fibres; dart (i,k) goes from A_i to B_{JJ[i][k]}. */
static int base_connected(void) {
    int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, cnt = 1;
    seen[0] = 1;
    st[top++] = 0;
    while (top) {
        int v = st[--top];
        if (v < PF) {
            for (int k = 0; k < d; k++) {
                int u = PF + JJ[v][k];
                if (!seen[u]) { seen[u] = 1; cnt++; st[top++] = u; }
            }
        } else {
            int j = v - PF;
            for (int t = 0; t < d; t++) {
                int u = RI[j][t];
                if (!seen[u]) { seen[u] = 1; cnt++; st[top++] = u; }
            }
        }
    }
    return cnt == 2 * PF;
}

static void new_base(void) {
    for (;;) {
        for (int k = 0; k < d; k++) {
            int perm[MAXP];
            for (int i = 0; i < PF; i++) perm[i] = i;
            for (int i = PF - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < PF; i++) JJ[i][k] = perm[i];
        }
        int cnt[MAXP] = {0, 0, 0, 0};
        for (int i = 0; i < PF; i++)
            for (int k = 0; k < d; k++) {
                int j = JJ[i][k];
                RI[j][cnt[j]] = i;
                RK[j][cnt[j]] = k;
                cnt[j]++;
            }
        if (base_connected()) return;
    }
}

/* Voltage for dart (i,k), avoiding a repeat of an earlier dart with the same target fibre. */
static int fresh_g(int i, int k) {
    for (;;) {
        int g = rndint(NG), clash = 0;
        for (int k2 = 0; k2 < d; k2++)
            if (k2 != k && JJ[i][k2] == JJ[i][k] && GG[i][k2] == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Number of (source, vertex) pairs unreached within distance D; sources are one vertex
 * per fibre, which suffices because left multiplication is transitive on each fibre. */
static long eval_lift(void) {
    const int pn = PF * NG, V = 2 * pn;
    long bad = 0;
    for (int f = 0; f < 2 * PF; f++) {
        int src = f * NG;
        int head = 0, tail = 0;
        stc++;
        stv[src] = stc;
        dist_v[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = dist_v[v];
            if (dv >= D) continue;
            if (v < pn) {
                int i = v / NG, x = v - i * NG;
                const int *row = MTAB + (size_t)x * NG;
                for (int k = 0; k < d; k++) {
                    int u = (PF + JJ[i][k]) * NG + row[GG[i][k]];
                    if (stv[u] != stc) { stv[u] = stc; dist_v[u] = dv + 1; qv[tail++] = u; }
                }
            } else {
                int j = v / NG - PF, y = v - (PF + j) * NG;
                const int *row = MTAB + (size_t)y * NG;
                for (int t = 0; t < d; t++) {
                    int i = RI[j][t], k = RK[j][t];
                    int u = i * NG + row[INVT[GG[i][k]]];
                    if (stv[u] != stc) { stv[u] = stc; dist_v[u] = dv + 1; qv[tail++] = u; }
                }
            }
        }
        bad += V - tail;
    }
    return bad;
}

static int anneal_attempt(long steps) {
    new_base();
    for (int i = 0; i < PF; i++)
        for (int k = 0; k < d; k++) GG[i][k] = -1;
    for (int i = 0; i < PF; i++)
        for (int k = 0; k < d; k++) GG[i][k] = fresh_g(i, k);
    long bad = eval_lift();
    const double T0 = 1.5, T1 = 0.12;
    double T = T0, alpha = pow(T1 / T0, 1.0 / (double)steps);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        int i = rndint(PF), k = rndint(d);
        int old = GG[i][k];
        GG[i][k] = fresh_g(i, k);
        long nb = eval_lift();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else GG[i][k] = old;
        T *= alpha;
    }
    return bad == 0;
}

static int try_accept(void) {
    int pn = PF * NG;
    cand.n = 2 * pn;
    for (int v = 0; v < cand.n; v++) { cand.deg[v] = 0; cand.side[v] = v >= pn; }
    for (int i = 0; i < PF; i++)
        for (int x = 0; x < NG; x++)
            for (int k = 0; k < d; k++)
                add_edge(&cand, i * NG + x,
                         pn + JJ[i][k] * NG + MTAB[(size_t)x * NG + GG[i][k]]);
    if (cand.n <= best.n) return 0;
    if (!is_valid(&cand)) return 0;
    copy_graph(&best, &cand);
    return 1;
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

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    if (d < 3) { print_graph(&best); return 0; }

    long moore = moore_bound();
    while (now() < t_end) {
        if (best.n + 2 > moore) break;
        int r = rndint(10);
        PF = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : 4;
        int Nmin = best.n / (2 * PF) + 1;
        if (Nmin < d) Nmin = d;
        int N = Nmin + rndint(WIN);
        if (N > MAXH || 2L * PF * N > MAXN || 2L * PF * N > moore) continue;
        if (!pick_group(N, &G)) continue;
        setup_group(N);
        for (int a = 0; a < ATT && now() < t_end; a++)
            if (anneal_attempt(STEPS) && try_accept()) break;
    }
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
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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
    try:
        starts = known_starts(d, D)
    except Exception:
        starts = []
    for n, e in starts:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
