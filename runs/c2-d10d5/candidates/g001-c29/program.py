"""Combined program: bi-Cayley lift annealing in C over semidirect groups, seeded by the best known start.

Python builds the known start (projective plane or Araujo-Lopez) when D = 3 and calls the C engine.
C anneals layered bi-Cayley lifts over Z_m x| Z_k (d-regular, bipartite by construction) with
defect-targeted voltage moves, layer swaps, stagnation restarts and a bandit over base sizes.
Every improvement is re-verified exactly before it is kept, and Python re-checks the output.
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

#define MAXN 16384
#define MAXD 16
#define MAXK 4
#define MAXW (MAXN / 64)
#define ITERS 3000
#define PATIENCE 900
#define PEN 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static int d, D;
static double t_end;
static long moore_b;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long compute_moore(void) {
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

static void graph_clear(Graph *g, int n) {
    g->n = n;
    for (int v = 0; v < n; v++) g->deg[v] = 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[(size_t)MAXN * MAXW], RB[(size_t)MAXN * MAXW];

/* Number of unordered pairs at distance > D. */
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

/* Full check: simple, symmetric, bipartite, degree <= d, diameter <= D. */
static int validate(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    static int col[MAXN], stk[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            int ok = 0;
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == v) { ok = 1; break; }
            if (!ok) return 0;
        }
    }
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        int top = 0;
        col[s] = 0;
        stk[top++] = s;
        while (top) {
            int v = stk[--top];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (col[u] == -1) {
                    col[u] = 1 - col[v];
                    stk[top++] = u;
                } else if (col[u] == col[v]) {
                    return 0;
                }
            }
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXN || m < 0) return;
    graph_clear(g, n);
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { g->n = 0; return; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= d || g->deg[v] >= d) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    if (!validate(g)) g->n = 0;
}

static void complete_bipartite(Graph *g) {
    graph_clear(g, 2 * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
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

/* ------------------------------------------------------------ group Z_gm x| Z_gk */

/* Element (a,b) is the int a*gk+b; (a,b)(c,e) = (a + r^b c mod gm, b+e mod gk). */
static int gm, gk, gr, G, K;
static int rp[MAXN];
static int sinv[MAXN];

static int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int s = (int)(((long)a + (long)rp[b] * c) % gm);
    int t = b + e;
    if (t >= gk) t -= gk;
    return s * gk + t;
}

static int ginv(int x) {
    int c = x / gk, e = x - c * gk;
    int b = (gk - e) % gk;
    long a = (-((long)rp[b] * c)) % gm;
    if (a < 0) a += gm;
    return (int)a * gk + b;
}

static int setup_group(long target) {
    static const int ks[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int k2 = ks[rndint(18)];
    long m = (target + k2 - 1) / k2;
    if (m < 1) m = 1;
    if (m * k2 > MAXN / 2) return 0;
    gm = (int)m;
    gk = k2;
    gr = 1 % gm;
    if (gk > 1 && gm > 1) {
        for (int tries = 0; tries < 60; tries++) {
            int r = tries == 0 ? gm - 1 : 1 + rndint(gm - 1);
            if (gcd_i(r, gm) != 1) continue;
            if (powmod(r, gk, gm) != 1 % gm) continue;
            gr = r;
            break;
        }
    }
    G = gm * gk;
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
    for (int s = 0; s < G; s++) sinv[s] = ginv(s);
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley lift state */

/* A-block i, element g  -> vertex i*G+g.  B-block j, element h -> vertex (K+j)*G+h.
 * Layer l joins A_{i,g} to B_{lay[l][i], g*vol[l][i]}. Each layer is a permutation of blocks,
 * so every vertex gets exactly one neighbour per layer. */
static int lay[MAXD][MAXK];
static int inl[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t rch[MAXN], rsave[MAXN];
static uint64_t bufA[MAXN], bufB[MAXN];

static void init_random(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l][i] = perm[i];
            inl[l][perm[i]] = i;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rndint(G);
    }
}

static void build_nbr(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = lay[l][i], s = vol[l][i];
            for (int g = 0; g < G; g++) {
                int A = i * G + g;
                int B = (K + j) * G + gmul(g, s);
                nbr[l][A] = B;
                nbr[l][B] = A;
            }
        }
}

/* Pairs of layers that give the same edge (same block pair and same voltage). */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && vol[l][i] == vol[l2][i]) c++;
    return c;
}

/* Sum over all vertices v of the number of block representatives farther than D from v.
 * Left multiplication is an automorphism, so representatives (block b, identity) suffice. */
static long unreached(void) {
    int N = 2 * K * G;
    uint64_t *cur = bufA, *nx = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nx[v] = x;
        }
        uint64_t *t = cur;
        cur = nx;
        nx = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        rch[v] = cur[v];
        bad += 2 * K - __builtin_popcountll(cur[v]);
    }
    return bad;
}

static long evaluate(void) {
    build_nbr();
    long u = unreached();
    return u + PEN * dup_count();
}

static int search_lift(long iters, long patience, double deadline) {
    init_random();
    int N = 2 * K * G;
    uint64_t full = (1ULL << (2 * K)) - 1;
    long cost = evaluate();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        memcpy(rsave, rch, sizeof(uint64_t) * (size_t)N);
        int kind = 1, l = 0, i = 0, i2 = 0, old = 0;
        if (K >= 2 && rnd01() < 0.25) {
            kind = 0;
            l = rndint(d);
            i = rndint(K);
            i2 = rndint(K - 1);
            if (i2 >= i) i2++;
            int a = lay[l][i], b = lay[l][i2];
            lay[l][i] = b;
            lay[l][i2] = a;
            inl[l][b] = i;
            inl[l][a] = i2;
        } else {
            int found = -1;
            if (rnd01() < 0.4) {
                for (int tr = 0; tr < 30; tr++) {
                    int v = rndint(N);
                    if (rsave[v] != full) { found = v; break; }
                }
            }
            if (found >= 0) {
                int blk = found / G;
                l = rndint(d);
                i = (blk < K) ? blk : inl[l][blk - K];
            } else {
                l = rndint(d);
                i = rndint(K);
            }
            old = vol[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            vol[l][i] = nv;
        }
        long c2 = evaluate();
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            if (kind == 0) {
                int a = lay[l][i], b = lay[l][i2];
                lay[l][i] = b;
                lay[l][i2] = a;
                inl[l][b] = i;
                inl[l][a] = i2;
            } else {
                vol[l][i] = old;
            }
            memcpy(rch, rsave, sizeof(uint64_t) * (size_t)N);
            build_nbr();
        }
    }
    return cost == 0;
}

static void lift_to_graph(Graph *g) {
    int N = 2 * K * G;
    graph_clear(g, N);
    for (int l = 0; l < d; l++)
        for (int v = 0; v < K * G; v++)
            add_edge(g, v, nbr[l][v]);
}

/* ------------------------------------------------------------ outer search */

static Graph best, cand, start;
static long trials[MAXK + 1], wins[MAXK + 1];

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

static void lift_phase(void) {
    while (now() < t_end) {
        if (best.n + 2 > moore_b) break;
        int k = pick_k();
        long need = best.n + 2;
        long base = (need + 2 * k - 1) / (2 * k);
        long extra = base / 8 + 1;
        long target = base + rndint((int)extra);
        if (!setup_group(target)) continue;
        K = k;
        long N = 2L * K * G;
        if (N > moore_b || N > MAXN || N <= best.n) continue;
        trials[k]++;
        if (search_lift(ITERS, PATIENCE, t_end)) {
            lift_to_graph(&cand);
            if (cand.n > best.n && validate(&cand)) {
                best = cand;
                wins[k]++;
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
    t_end = t0 + limit * 0.88;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (D == 1) {
        printf("2 1\n0 1\n");
        return 0;
    }
    moore_b = compute_moore();
    read_start(&start);
    if (start.n > 0) best = start;
    else complete_bipartite(&best);

    if (best.n < moore_b) lift_phase();

    if (!validate(&best)) complete_bipartite(&best);
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
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    # Moore graphs cannot be beaten; very large degrees are outside the C engine's storage.
    if best[0] >= lib.moore_bound(d, D) or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 5.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
