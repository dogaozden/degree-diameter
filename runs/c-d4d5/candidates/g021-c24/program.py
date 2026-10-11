"""Bi-Cayley search with a general-graph annealing finisher (new construction family).

The C engine treats the target as a bi-Cayley graph over a random group G of order N:
A-vertices x and B-vertices y, with x adjacent to y whenever x^-1 y lies in a d-element set S.
Left multiplication is an automorphism, so validity needs only two BFS runs (from A_e and B_e).
For each N it hill-climbs S over random semidirect groups Z_m x| Z_k. If that fails, it anneals
degree-preserving double-edge swaps on the near-miss graph. Starts are the algebraic graphs from
Python (PG(2,q), W(q), Araujo-Pardo-Lopez) or K_{d,d}, so every returned graph is valid.
"""
import itertools
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

#define MAXN 1024
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXG (MAXN / 2)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end_global;

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

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
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

/* Number of unordered vertex pairs at distance > D (bitset all-pairs). */
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

/* Adding an A-B edge between two vertices with spare degree never increases a distance. */
static int saturate(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0 || g->deg[a] >= d) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
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

/* ---------- groups Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e) ---------- */
typedef struct {
    int m, k, r;
    int rp[MAXG];
} Grp;

static int MT[MAXG][MAXG];

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    long t = ((long)a + (long)G->rp[b] * c) % G->m;
    return (int)t * G->k + (b + e) % G->k;
}

/* Pick a random semidirect group of order N and fill the multiplication table MT. */
static void make_group(int N, Grp *G) {
    long count = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    G->m = bm; G->k = bk; G->r = br;
    G->rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G->rp[b] = (int)((long)G->rp[b - 1] * br % bm);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x][y] = gmul(G, x, y);
}

/* ---------- bi-Cayley graphs: A_x ~ B_{x*s} for s in S, |S| = d ---------- */
static void bc_build(Graph *g, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + MT[x][S[i]]);
}

static int bfs_q[MAXN], bfs_dist[MAXN];

/* Vertices not within distance D of src. */
static long unreached(const Graph *g, int src) {
    int n = g->n, head = 0, tail = 0;
    for (int v = 0; v < n; v++) bfs_dist[v] = -1;
    bfs_dist[src] = 0;
    bfs_q[tail++] = src;
    while (head < tail) {
        int v = bfs_q[head++];
        if (bfs_dist[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (bfs_dist[u] < 0) {
                bfs_dist[u] = bfs_dist[v] + 1;
                bfs_q[tail++] = u;
            }
        }
    }
    return n - tail;
}

static void random_S(int N, int *S) {
    for (int i = 0; i < d; i++) {
        int s;
        for (;;) {
            s = rndint(N);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == s) { dup = 1; break; }
            if (!dup) break;
        }
        S[i] = s;
    }
}

static Graph tmpG;

/* Zero iff the bi-Cayley graph has diameter <= D (left-translation symmetry). */
static long bc_cost_of(int N, const int *S) {
    bc_build(&tmpG, N, S);
    return unreached(&tmpG, 0) + unreached(&tmpG, N);
}

/* Hill-climb the connection set S for the current group. Leaves S in the state of the returned cost. */
static long hill_climb(int N, int *S, long steps, double until) {
    random_S(N, S);
    long cur = bc_cost_of(N, S);
    double T = 2.0;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int i = rndint(d), old = S[i], ns;
        for (;;) {
            ns = rndint(N);
            int dup = 0;
            for (int j = 0; j < d; j++)
                if (S[j] == ns) { dup = 1; break; }
            if (!dup) break;
        }
        S[i] = ns;
        long nb = bc_cost_of(N, S);
        if (nb <= cur || rnd01() < exp(-(double)(nb - cur) / T)) cur = nb;
        else S[i] = old;
        T *= 0.999;
        if (T < 0.2) T = 0.2;
    }
    return cur;
}

static Graph nearG;
static long nearCost;
static int nearN;

/* Stage A: bi-Cayley hill-climbing over random groups of order N. Returns 1 on success. */
static int stageA(Graph *best, int N, double until) {
    Grp G;
    int S[MAXD];
    nearN = N;
    nearCost = -1;
    while (now() < until) {
        make_group(N, &G);
        for (int rep = 0; rep < 40 && now() < until; rep++) {
            long c = hill_climb(N, S, 4000, until);
            if (nearCost < 0 || c < nearCost) {
                nearCost = c;
                bc_build(&nearG, N, S);
            }
            if (c == 0) {
                bc_build(&tmpG, N, S);
                if (is_valid(&tmpG) && tmpG.n > best->n) {
                    copy_graph(best, &tmpG);
                    return 1;
                }
            }
        }
    }
    return 0;
}

/* Stage B: anneal degree-preserving double-edge swaps on the near-miss bi-Cayley graph. */
static int stageB(Graph *best, int N, double until) {
    static Graph g;
    if (nearN != N || nearCost < 0) {
        Grp G;
        int S[MAXD];
        make_group(N, &G);
        random_S(N, S);
        bc_build(&nearG, N, S);
    }
    copy_graph(&g, &nearG);
    long bad = bad_pairs(&g);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 127) == 0 && now() > until) return 0;
        if (it % 300000 == 0) T = 1.0;
        T *= 0.99998;
        if (T < 0.12) T = 0.12;
        int a = rndint(N);
        int b = g.adj[a][rndint(g.deg[a])];
        int c = rndint(N);
        if (c == a) continue;
        int e = g.adj[c][rndint(g.deg[c])];
        if (has_edge(&g, a, e) || has_edge(&g, c, b)) continue;
        del_edge(&g, a, b);
        del_edge(&g, c, e);
        add_edge(&g, a, e);
        add_edge(&g, c, b);
        long nb = bad_pairs(&g);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
            bad = nb;
        } else {
            del_edge(&g, a, e);
            del_edge(&g, c, b);
            add_edge(&g, a, b);
            add_edge(&g, c, e);
        }
    }
    if (is_valid(&g) && g.n > best->n) {
        copy_graph(best, &g);
        return 1;
    }
    return 0;
}

static void search(Graph *best) {
    long moore = moore_bound();
    while (now() < t_end_global) {
        int N = best->n / 2 + 1;
        if (N <= d || 2L * N > moore || 2 * N > MAXN) break;
        double rem = t_end_global - now();
        double until = now() + rem * 0.4;
        if (stageA(best, N, until)) continue;
        if (!stageB(best, N, t_end_global)) break;
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
    t_end_global = now() + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }

    static Graph best;
    read_start(&best);
    if (best.n > 0) saturate(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2) search(&best);

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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
