"""Bold variant for the d=5, D=7 target: bipartite double covers of Cayley graphs.

Construction: for a group G of order N and a symmetric connection set S (|S| = d), the bipartite
double cover of Cay(G, S) has vertices (x, 0), (x, 1) with (x, p) ~ (x*s, 1-p) for s in S.
It is bipartite, d-regular, has 2N vertices, and is vertex-transitive, so diameter <= D can be
checked by one BFS from (e, 0). The C engine searches for groups and sets S by simulated annealing
on the number of unreached states, and raises N whenever a valid cover is found. The record
(3110) is not guaranteed to be beaten; if the search fails, the algebraic start from the
Python side (the H(4) hexagon incidence graph) is returned, which is below the record, so this
variant is a high-risk experiment. Every C output is checked again in Python with lib.is_valid.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bipartite double covers of Cayley graphs, searched by annealing.
 * Usage:   prog d D seed limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
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
#define MAXH 2048
#define MAXW (MAXN / 64)
#define STEPS 3000
#define FAIL_BUDGET 2.0
#define GROUP_TRIES 20

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
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
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

/* ---------------- groups Z_m x|_r Z_k, element a*k+b, identity 0 ---------------- */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

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

/* Multiplication table and inverses, plus the involution list. */
static int NN;
static int MTAB[MAXH * MAXH];
static int INVT[MAXH], INVOL[MAXH], ninvol;

static void setup_group(int N, const Grp *G) {
    NN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MTAB[(size_t)x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MTAB[(size_t)x * N + y] == 0) { INVT[x] = y; break; }
    ninvol = 0;
    for (int x = 1; x < N; x++)
        if (INVT[x] == x) INVOL[ninvol++] = x;
}

/* ---------------- double-cover objective ----------------
 * States: side 0 = x, side 1 = N + x. (x, p) ~ (x*s, 1-p) for s in S (right multiplication).
 * Left multiplication is an automorphism, so BFS from state 0 = (e, 0) decides diameter.
 * Returns the number of states not reached within D steps. */
static int vis[2 * MAXH], qb[2 * MAXH], stampc = 0;
static int Sg[MAXD];

static long eval_bad(void) {
    int N = NN;
    stampc++;
    int head = 0, tail = 0;
    vis[0] = stampc;
    qb[tail++] = 0;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        while (head < end) {
            int v = qb[head++];
            int p = v >= N;
            int x = p ? v - N : v;
            const int *row = MTAB + (size_t)x * N;
            int base = p ? 0 : N;
            for (int t = 0; t < d; t++) {
                int u = base + row[Sg[t]];
                if (vis[u] != stampc) { vis[u] = stampc; qb[tail++] = u; }
            }
        }
    }
    return (long)(2 * N - tail);
}

static int in_set(const int *S, int cnt, int x) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Fill S[slot], S[slot+1] with a fresh pair {x, x^-1}, x not an involution. Zeros are empty. */
static int fresh_pair(int *S, int slot) {
    for (int tries = 0; tries < 4000; tries++) {
        int x = 1 + rndint(NN - 1);
        int y = INVT[x];
        if (y == x) continue;
        if (in_set(S, d, x) || in_set(S, d, y)) continue;
        S[slot] = x;
        S[slot + 1] = y;
        return 1;
    }
    return 0;
}

static int fresh_inv(int *S, int slot) {
    if (ninvol == 0) return 0;
    for (int tries = 0; tries < 4000; tries++) {
        int t = INVOL[rndint(ninvol)];
        if (!in_set(S, d, t)) { S[slot] = t; return 1; }
    }
    return 0;
}

static int random_S(int *S) {
    for (int i = 0; i < d; i++) S[i] = 0;
    for (int u = 0; u < d / 2; u++)
        if (!fresh_pair(S, 2 * u)) return 0;
    if (d & 1)
        if (!fresh_inv(S, d - 1)) return 0;
    return 1;
}

/* Replace one unit (a pair or the involution) by a fresh one. Restores S on failure. */
static int mutate(int *S) {
    int k = d / 2;
    int units = k + (d & 1);
    int u = rndint(units);
    if (u < k) {
        int slot = 2 * u, a = S[slot], b = S[slot + 1];
        S[slot] = 0;
        S[slot + 1] = 0;
        if (fresh_pair(S, slot)) return 1;
        S[slot] = a;
        S[slot + 1] = b;
        return 0;
    }
    int old = S[d - 1];
    S[d - 1] = 0;
    if (fresh_inv(S, d - 1)) return 1;
    S[d - 1] = old;
    return 0;
}

static int S_out[MAXD];

/* Anneal connection sets in several groups of order N. Returns 1 and sets S_out on success;
 * MTAB and NN then describe the group of the successful set. */
static int search_order(int N, double until) {
    static Grp G;
    static int S[MAXD];
    if (N < d + 2 || N > MAXH) return 0;
    while (now() < until) {
        int ok = 0;
        for (int tries = 0; tries < GROUP_TRIES && !ok; tries++) {
            if (!random_group(N, &G)) return 0;
            setup_group(N, &G);
            if (!(d & 1) || ninvol > 0) ok = 1;
        }
        if (!ok) return 0;
        double gu = now() + (until - now()) / 3.0;
        if (gu > until) gu = until;
        while (now() < gu) {
            if (!random_S(S)) break;
            memcpy(Sg, S, sizeof(int) * d);
            long cur = eval_bad();
            double T = 3.0;
            const double alpha = pow(0.1, 1.0 / STEPS);
            for (int s = 0; s < STEPS && cur > 0; s++) {
                if ((s & 63) == 0 && now() > gu) break;
                int old[MAXD];
                memcpy(old, S, sizeof(int) * d);
                if (!mutate(S)) continue;
                memcpy(Sg, S, sizeof(int) * d);
                long nb = eval_bad();
                if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
                else memcpy(S, old, sizeof(int) * d);
                T *= alpha;
                if (T < 0.3) T = 0.3;
            }
            if (cur == 0) {
                memcpy(S_out, S, sizeof(int) * d);
                return 1;
            }
        }
    }
    return 0;
}

/* Vertices: x (side 0) and N + x (side 1); edge x -- N + x*s for s in S. */
static void build_cover(Graph *g, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MTAB[(size_t)x * N + S[t]]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed limit < start_graph\n", argv[0]);
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

    static Graph best, cand;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    if (d >= 3 && D >= 2) {
        int N = best.n / 2 + 1;
        while (now() < t_end && 2L * N <= moore && 2 * N <= MAXN && N <= MAXH) {
            double rem = t_end - now();
            double bud = rem < FAIL_BUDGET ? rem : FAIL_BUDGET;
            if (search_order(N, now() + bud)) {
                build_cover(&cand, N, S_out);
                if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
            }
            N++;
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    The caller validates the result with lib.is_valid.
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
