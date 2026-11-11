"""Fibre-transitive voltage-lift search over semidirect groups, run in C.

A lift over a group G with p base vertices per side has automorphisms given by left
multiplication, so the diameter is at most D exactly when every one of the 2p fibre
representatives reaches all vertices within D steps. Each annealing step therefore costs
2p BFS passes over a precomputed neighbour table, not a full all-pairs bitset check.
Growth goes by adaptive jumps in order, and a validated fallback is always returned.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: fibre-transitive lift search, then grow-by-two annealing.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 *
 * Lifts: base has p vertices per side, each side-A vertex has d darts
 * (one per permutation sig[t]), dart (t,i) carries voltage vg[t][i] in G.
 * A(i,x) ~ B(sig[t][i], x*vg[t][i]). Left multiplication is an automorphism,
 * so the lift has diameter <= D iff every fibre representative reaches all
 * vertices within D steps.
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
#define MAXP 8
#define PEN 20

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

/* ---------------- groups Z_m x|_r Z_k, element a*k+b ---------------- */

typedef struct {
    int m, k, r;
    long rp[MAXN];   /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    long aa = (a + (long)G->rp[b] * c) % G->m;
    return (int)(aa * G->k + (b + e) % G->k);
}

static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long ia = (G->m - (long)G->rp[nb] * a % G->m) % G->m;
    return (int)(ia * G->k + nb);
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
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = G->rp[b - 1] * G->r % G->m;
    return 1;
}

/* ---------------- lifts ---------------- */

typedef struct {
    int p, N;
    int sig[MAXD][MAXP];
    int sinv[MAXD][MAXP];
    int vg[MAXD][MAXP];
} LiftS;

static int nbtab[MAXN][MAXD];
static int vis[MAXN];
static int vstamp = 0;
static int bq[MAXN];

static void set_sinv(LiftS *L, int t) {
    for (int i = 0; i < L->p; i++) L->sinv[t][L->sig[t][i]] = i;
}

static void lift_init(LiftS *L, int p, int N) {
    L->p = p;
    L->N = N;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < p; i++) L->sig[t][i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = L->sig[t][i]; L->sig[t][i] = L->sig[t][j]; L->sig[t][j] = s;
        }
        set_sinv(L, t);
        for (int i = 0; i < p; i++) L->vg[t][i] = rndint(N);
    }
}

/* Neighbours of lift vertex v (A fibres first, then B fibres). */
static void lnb(const LiftS *L, const Grp *G, int v, int *out) {
    int p = L->p, N = L->N;
    if (v < p * N) {
        int i = v / N, x = v % N;
        for (int t = 0; t < d; t++) {
            int j = L->sig[t][i];
            out[t] = (p + j) * N + gmul(G, x, L->vg[t][i]);
        }
    } else {
        int w = v - p * N, j = w / N, y = w % N;
        for (int t = 0; t < d; t++) {
            int i = L->sinv[t][j];
            out[t] = i * N + gmul(G, y, ginv(G, L->vg[t][i]));
        }
    }
}

/* Cost = sum over the 2p fibre representatives of unreached vertices, plus duplicate-dart penalty. */
static long lift_cost(const LiftS *L, const Grp *G) {
    int p = L->p, N = L->N, n = 2 * p * N;
    long cost = 0;
    for (int i = 0; i < p; i++)
        for (int t = 0; t < d; t++)
            for (int u = 0; u < t; u++)
                if (L->sig[t][i] == L->sig[u][i] && L->vg[t][i] == L->vg[u][i]) cost += PEN;
    for (int v = 0; v < n; v++) lnb(L, G, v, nbtab[v]);
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N, head = 0, tail = 0;
        vstamp++;
        vis[src] = vstamp;
        bq[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            for (; head < end; head++) {
                const int *nb = nbtab[bq[head]];
                for (int t = 0; t < d; t++) {
                    int u = nb[t];
                    if (vis[u] != vstamp) { vis[u] = vstamp; bq[tail++] = u; }
                }
            }
        }
        cost += n - tail;
    }
    return cost;
}

static long lift_anneal(LiftS *L, const Grp *G, int maxit, double until) {
    int p = L->p;
    long cur = lift_cost(L, G);
    for (int it = 0; it < maxit && cur > 0; it++) {
        if ((it & 31) == 0 && now() > until) break;
        double temp = 0.2 + 1.5 * (1.0 - (double)it / maxit);
        int t = rndint(d), i = rndint(p);
        if (rnd01() < 0.7) {
            int old = L->vg[t][i];
            int ng = rndint(L->N);
            if (ng == old) continue;
            L->vg[t][i] = ng;
            long c2 = lift_cost(L, G);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else L->vg[t][i] = old;
        } else {
            int i2 = rndint(p);
            if (i2 == i) continue;
            int s = L->sig[t][i]; L->sig[t][i] = L->sig[t][i2]; L->sig[t][i2] = s;
            set_sinv(L, t);
            long c2 = lift_cost(L, G);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) cur = c2;
            else {
                s = L->sig[t][i]; L->sig[t][i] = L->sig[t][i2]; L->sig[t][i2] = s;
                set_sinv(L, t);
            }
        }
    }
    return cur;
}

static void lift_to_graph(const LiftS *L, const Grp *G, Graph *g) {
    int p = L->p, N = L->N, n = 2 * p * N;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    int nb[MAXD];
    for (int v = 0; v < p * N; v++) {
        lnb(L, G, v, nb);
        for (int t = 0; t < d; t++) add_edge(g, v, nb[t]);
    }
}

static const int PSET[8] = {1, 1, 2, 2, 3, 4, 5, 6};

static void lift_search(Graph *best, double until) {
    static Grp G;
    static LiftS L;
    static Graph cand;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    long jump = best->n / 16 > 2 ? best->n / 16 : 2;
    while (now() < until) {
        if (best->n + 2 > cap) break;
        long target = best->n + jump;
        if (target > cap) target = cap;
        int p = PSET[rndint(8)];
        long N = (target + 2L * p - 1) / (2L * p);
        if (N < 1) N = 1;
        N += rndint(2);
        if (2L * p * N > cap) {
            p = 1;
            N = (target + 1) / 2 + rndint(2);
            if (2L * N > cap) N = cap / 2;
            if (N < 1) continue;
        }
        if (!random_group((int)N, &G)) continue;
        lift_init(&L, p, (int)N);
        double until2 = now() + 2.5;
        if (until2 > until) until2 = until;
        long c = lift_anneal(&L, &G, 20000, until2);
        if (c == 0) {
            lift_to_graph(&L, &G, &cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                jump = jump * 3 / 2 + 1;
            } else if (jump > 2) {
                jump = jump * 3 / 4;
            }
        } else if (jump > 2) {
            jump = jump * 3 / 4;
        }
        if (jump < 2) jump = 2;
    }
}

/* ---------------- grow-by-two annealing (full check) ---------------- */

static int cbad[MAXN];
static int blist[MAXN];

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    memcpy(cbad, badv, sizeof(int) * work->n);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int nbl = 0;
        for (int w = 0; w < work->n; w++)
            if (cbad[w]) blist[nbl++] = w;
        if (nbl == 0) break;
        int v = rnd01() < 0.8 ? blist[rndint(nbl)] : rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            memcpy(cbad, badv, sizeof(int) * work->n);
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Lift search and growth in C, starting from the best graph so far.
    if D >= 2 and d <= 30:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
