"""Combined search: exact constructions, then a C engine that anneals voltage lifts over small
semidirect groups (cost = unreached pairs from block representatives), then grows the best graph."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine. Phase 1: simulated annealing over voltage lifts of base multigraphs
# with p vertices per side (p = 1..6), each layer a permutation, voltages in a
# random group Z_m x| Z_k. Cost = unreached pairs from the 2p block
# representatives (exact, by group transitivity on blocks) plus duplicate darts.
# Phase 2: grow-by-two with edge-swap repair targeted at bad pairs.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
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
#define MAXP 6
#define MAXG 2048
#define PEN 30

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

/* Number of unordered pairs at distance > D. Fills badv[v] = bad partners of v. */
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

/* ---------------- groups Z_m x|_r Z_k, element (a,b) = a*k+b ---------------- */

typedef struct { int N, m, k; int rp[8]; } Grp;

static int MT[MAXG * MAXG];   /* MT[x*N+y] = x*y */
static int INV[MAXG];
static int GN = 1;

static int gmul_raw(int m, int k, const int *rp, int x, int y) {
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
}

static void build_tables(const Grp *G) {
    int N = G->N;
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gmul_raw(G->m, G->k, G->rp, x, y);
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
    }
}

/* Random group of order about target (>= target), returns 0 on failure. */
static int sample_group(long target, Grp *G) {
    static const int ks[9] = {1, 1, 2, 2, 3, 4, 5, 6, 8};
    for (int att = 0; att < 400; att++) {
        int k = ks[rndint(9)];
        long m = (target + k - 1) / k;
        if (m < 2) m = 2;
        m += rndint((int)(m / 40 + 2));
        if (m * k > MAXG) continue;
        int mi = (int)m;
        int r = 1 % mi;
        if (k > 1) {
            if (rnd01() < 0.3) r = mi - 1;
            else r = 1 + rndint(mi - 1);
            if (gcd(r, mi) != 1 || powmod(r, k, mi) != 1 % mi) continue;
        }
        G->N = mi * k;
        G->m = mi;
        G->k = k;
        G->rp[0] = 1 % mi;
        for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % mi);
        return 1;
    }
    return 0;
}

/* ---------------- lifts: p base vertices per side, d layers ---------------- */

typedef struct {
    int p, N, d;
    int perm[MAXD][MAXP];   /* layer t: A_i joined to B_{perm[t][i]} */
    int inv[MAXD][MAXP];
    int volt[MAXD][MAXP];   /* A_{i,x} ~ B_{perm[t][i], x*volt} */
} Lift;

/* Neighbour of vertex v in layer t. A_i,x = i*N+x ; B_j,y = p*N + j*N + y. */
static int lnb(const Lift *L, int v, int t) {
    int N = L->N, pN = L->p * N;
    if (v < pN) {
        int i = v / N, x = v % N;
        int j = L->perm[t][i];
        int y = MT[x * N + L->volt[t][i]];
        return pN + j * N + y;
    }
    int w = v - pN;
    int j = w / N, y = w % N;
    int i = L->inv[t][j];
    int x = MT[y * N + INV[L->volt[t][i]]];
    return i * N + x;
}

static int bq[MAXN];
static unsigned int bseen[MAXN];
static unsigned int bstamp = 0;

/* Vertices NOT within distance D of src. */
static long unreached_from(const Lift *L, int src) {
    int Nn = 2 * L->p * L->N;
    bstamp++;
    int head = 0, tail = 0;
    bq[tail++] = src;
    bseen[src] = bstamp;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int stop = tail;
        while (head < stop) {
            int v = bq[head++];
            for (int t = 0; t < L->d; t++) {
                int u = lnb(L, v, t);
                if (bseen[u] != bstamp) { bseen[u] = bstamp; bq[tail++] = u; }
            }
        }
    }
    return Nn - tail;
}

static long lift_unreached(const Lift *L) {
    long tot = 0;
    int pN = L->p * L->N;
    for (int i = 0; i < L->p; i++) tot += unreached_from(L, i * L->N);
    for (int j = 0; j < L->p; j++) tot += unreached_from(L, pN + j * L->N);
    return tot;
}

/* Duplicate darts: same A_i, same target B_j and same voltage in two layers. */
static long lift_cost(const Lift *L) {
    long dup = 0;
    for (int i = 0; i < L->p; i++)
        for (int t1 = 1; t1 < L->d; t1++)
            for (int t2 = 0; t2 < t1; t2++)
                if (L->perm[t1][i] == L->perm[t2][i] && L->volt[t1][i] == L->volt[t2][i])
                    dup++;
    return lift_unreached(L) + PEN * dup;
}

static void lift_random(Lift *L) {
    for (int t = 0; t < L->d; t++) {
        for (int i = 0; i < L->p; i++) L->perm[t][i] = i;
        for (int i = L->p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = L->perm[t][i];
            L->perm[t][i] = L->perm[t][j];
            L->perm[t][j] = s;
        }
        for (int i = 0; i < L->p; i++) L->inv[t][L->perm[t][i]] = i;
        for (int i = 0; i < L->p; i++) L->volt[t][i] = rndint(L->N);
    }
}

static int lift_anneal(Lift *L, long steps, double deadline) {
    lift_random(L);
    long cur = lift_cost(L);
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 31) == 0 && now() > deadline) return 0;
        double T = 2.0 * pow(0.01, (double)s / (double)steps) + 0.05;
        int t = rndint(L->d);
        if (L->p >= 2 && rndint(4) == 0) {
            int i1 = rndint(L->p), i2 = rndint(L->p);
            if (i1 == i2) continue;
            int a = L->perm[t][i1], b = L->perm[t][i2];
            L->perm[t][i1] = b;
            L->perm[t][i2] = a;
            L->inv[t][b] = i1;
            L->inv[t][a] = i2;
            long c2 = lift_cost(L);
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) {
                cur = c2;
            } else {
                L->perm[t][i1] = a;
                L->perm[t][i2] = b;
                L->inv[t][a] = i1;
                L->inv[t][b] = i2;
            }
        } else {
            int i = rndint(L->p);
            int old = L->volt[t][i];
            int nv = rndint(L->N);
            if (nv == old) continue;
            L->volt[t][i] = nv;
            long c2 = lift_cost(L);
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) cur = c2;
            else L->volt[t][i] = old;
        }
    }
    return cur == 0;
}

static void lift_to_graph(const Lift *L, Graph *g) {
    int N = L->N, pN = L->p * N;
    g->n = 2 * pN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= pN; }
    for (int t = 0; t < L->d; t++)
        for (int i = 0; i < L->p; i++)
            for (int x = 0; x < N; x++)
                add_edge(g, i * N + x,
                         pN + L->perm[t][i] * N + MT[x * N + L->volt[t][i]]);
}

static void lift_search(Graph *best, double until) {
    static Lift L;
    static Grp G;
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        long bn = best->n;
        if (bn + 2 > moore || bn + 2 > MAXN) return;
        int r = rndint(12);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : r < 10 ? 4 : r < 11 ? 5 : 6;
        long extra = bn / 40 + 2;
        long total = bn + 2 + rndint((int)extra);
        long N = (total + 2L * p - 1) / (2L * p);
        if (N < 2) N = 2;
        if (N > MAXG) continue;
        if (!sample_group(N, &G)) continue;
        long tot = 2L * p * G.N;
        if (tot <= bn || tot > moore || tot > MAXN) continue;
        build_tables(&G);
        L.p = p;
        L.N = G.N;
        L.d = d;
        if (lift_anneal(&L, 4000, until)) {
            lift_to_graph(&L, &cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- grow-by-two with targeted repair ---------------- */

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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.6);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
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
        """Replace best with (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

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

    # C engine: voltage-lift annealing, then grow-by-two from the best graph.
    if D >= 2:
        c_budget = end - time.monotonic() - 1.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
