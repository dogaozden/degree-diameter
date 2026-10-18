"""Bi-Cayley lift search for the weakest parent case (d=11, D=5).

Construction: a d-regular base multigraph with p <= 4 vertices per side, lifted over a
random finite group G = Z_m x| Z_k of order N. Each dart (i -> j, g) gives the edges
(i,x)-(j,x*g) for all x in G. The lift is bipartite, d-regular, and has 2pN vertices.
Left multiplication by G preserves sides and is transitive on each side's p orbits,
so the diameter is at most D exactly when the 2p BFS balls from the orbit
representatives cover everything within depth D. Simulated annealing on the dart
group elements minimises the number of unreached (representative, vertex) pairs.

Python keeps validated fallbacks (a Moore graph or Araujo-Lopez start when available,
K_{d,d}, or a single edge) and only accepts a C result that is larger and passes
lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search for bipartite degree-diameter graphs.
 *
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" + m edges of a known valid start graph, or "0 0".
 * stdout: "n m" + edges of the largest valid graph found.
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
#define MAXP 4
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];  /* rp[b] = r^b mod m */
    int inv[MAXN]; /* inverse of each element */
} Grp;

static int d, D;
static double t_end;

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

/* ------------------------------------------------------------ graph basics */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ full checks */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. Zero means diameter <= D (and connected). */
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

/* Read "n m" + edges from stdin and 2-colour. Leaves g->n = 0 if absent or invalid. */
static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x - a * G->k;
    int c = y / G->k, e = y - c * G->k;
    int first = (int)(((long)a + (long)G->rp[b] * c) % G->m);
    int second = (b + e) % G->k;
    return first * G->k + second;
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. Fills tables. */
static int random_group(int N, Grp *G) {
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
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    G->m = bm; G->k = bk; G->r = br;
    G->rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G->rp[b] = (int)((long)G->rp[b - 1] * br % bm);
    for (int x = 0; x < N; x++) {
        int a = x / bk, b = x - a * bk;
        int e = (bk - b) % bk;                           /* inverse has second coord -b */
        long c = ((long)(bm - a) % bm) * G->rp[e] % bm;  /* -a * r^{-b} */
        G->inv[x] = (int)c * bk + e;
    }
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley lifts */

static int gP, gN, gV;
static const Grp *CG;
static int nd;                                   /* number of darts = sum of base edges */
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART], dGi[MAXDART];
static int rowD[MAXP][MAXD], colD[MAXP][MAXD];   /* darts leaving row i / entering col j */
static int tabF[MAXDART][MAXN], tabB[MAXDART][MAXN];

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP], stack[2 * MAXP], top = 0, nseen = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = (v < p) ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* True if another dart (other than skip) already uses the same (i, j, g). */
static int dart_clash(int i, int j, int g, int skip) {
    for (int t = 0; t < nd; t++)
        if (t != skip && dI[t] == i && dJ[t] == j && dG[t] == g) return 1;
    return 0;
}

static void rebuild_rows(void) {
    int rc[MAXP] = {0}, cc[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        rowD[dI[t]][rc[dI[t]]++] = t;
        colD[dJ[t]][cc[dJ[t]]++] = t;
    }
}

static void set_dart_table(int t) {
    for (int x = 0; x < gN; x++) {
        tabF[t][x] = gmul(CG, x, dG[t]);
        tabB[t][x] = gmul(CG, x, dGi[t]);
    }
}

/* Number of vertices within distance D of source s (BFS, bounded depth). */
static int bfs_reach(int s) {
    static int q[MAXN];
    static int vis[MAXN];
    static int stamp = 0;
    stamp++;
    if (stamp == 0x7fffffff) { memset(vis, 0, sizeof vis); stamp = 1; }
    const int N = gN, PN = gP * gN;
    int head = 0, tail = 0;
    q[tail++] = s;
    vis[s] = stamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = q[head++];
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int c = 0; c < d; c++) {
                    int t = rowD[i][c];
                    int w = PN + dJ[t] * N + tabF[t][x];
                    if (vis[w] != stamp) { vis[w] = stamp; q[tail++] = w; }
                }
            } else {
                int u = v - PN, j = u / N, y = u - j * N;
                for (int c = 0; c < d; c++) {
                    int t = colD[j][c];
                    int w = dI[t] * N + tabB[t][y];
                    if (vis[w] != stamp) { vis[w] = stamp; q[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Total unreached (representative, vertex) pairs; zero means the lift has diameter <= D. */
static long eval_cost(void) {
    long cost = 0;
    for (int i = 0; i < gP; i++) {
        cost += gV - bfs_reach(i * gN);
        cost += gV - bfs_reach(gP * gN + i * gN);
    }
    return cost;
}

/* Anneal the dart group elements of one random base over group G (order N).
 * On success, out holds the valid lift with 2pN vertices. */
static int attempt(int p, int N, const Grp *G, long maxEval, Graph *out) {
    int M[MAXP][MAXP];
    gP = p; gN = N; gV = 2 * p * N; CG = G;
    make_base(p, M);
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                int g;
                do { g = rndint(N); } while (dart_clash(i, j, g, -1));
                dI[nd] = i; dJ[nd] = j; dG[nd] = g; dGi[nd] = G->inv[g];
                nd++;
            }
    for (int t = 0; t < nd; t++) set_dart_table(t);
    rebuild_rows();
    long cost = eval_cost();
    double c0 = (double)(cost > 1 ? cost : 1);
    for (long it = 0; it < maxEval && cost > 0; it++) {
        if ((it & 31) == 0 && now() > t_end) break;
        /* Temperature scales with the starting cost and cools linearly to 0.5. */
        double frac = 1.0 - (double)it / (double)maxEval;
        double T = 0.01 * c0 * frac;
        if (T < 0.5) T = 0.5;

        int t = rndint(nd);
        int g;
        do { g = rndint(N); } while (dart_clash(dI[t], dJ[t], g, t));
        int og = dG[t], ogi = dGi[t];
        dG[t] = g; dGi[t] = G->inv[g];
        set_dart_table(t);
        long nc = eval_cost();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
        else { dG[t] = og; dGi[t] = ogi; set_dart_table(t); }
    }
    if (cost != 0) return 0;
    out->n = gV;
    for (int v = 0; v < gV; v++) { out->deg[v] = 0; out->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(out, dI[t] * N + x, p * N + dJ[t] * N + tabF[t][x]);
    return is_valid(out);
}

/* Grow the order adaptively: try random (p, group) lifts with order near best + delta. */
static void search(Graph *best) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    long delta = best->n / 16 > 2 ? best->n / 16 : 2;
    int fails = 0;
    while (now() < t_end) {
        long room = moore - best->n;
        if (room < 2) break;
        if (delta > room) delta = room;
        if (delta < 2) delta = 2;
        long target = best->n + delta;
        int p = 1 + rndint(MAXP);
        long N = (target + 2L * p - 1) / (2L * p);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2L * p * N > MAXN) {
            p = 1;
            N = (target + 1) / 2;
            if (N < d + 1) N = d + 1;
            if (2L * N > moore || 2L * N > MAXN) { delta = 2; continue; }
        }
        if (!random_group((int)N, &G)) continue;
        long V = 2L * p * N;
        long ops = 2L * p * V * d;
        long maxEval = 400000000L / ops;
        if (maxEval < 300) maxEval = 300;
        if (attempt(p, (int)N, &G, maxEval, &cand) && cand.n > best->n) {
            copy_graph(best, &cand);
            fails = 0;
            delta = best->n / 16 > 2 ? best->n / 16 : 2;
        } else if (++fails % 6 == 0 && delta > 2) {
            delta /= 2;
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (D < 2 || d < 1 || d > MAXD) {
        printf("2 1\n0 1\n");   /* a single edge is valid for D >= 1 */
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore_bound()) search(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
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
    candidates.append(lib.haar_graph(d, range(d)))   # K_{d,d}, valid for D >= 2
    for n, edges in candidates:
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    budget = 0.9 * time_limit - 2.0 - (time.monotonic() - t0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine

    if budget > 0.5 and D >= 2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 8.0)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass   # keep the valid fallback

    return best
