"""Orbit-representative bi-Cayley annealing in C, then grow-by-two.

New in this version: the C engine searches d-regular bi-Cayley lifts over Z_m x| Z_q
with P base vertices per side. Each layer is a permutation of the base vertices
plus one voltage per base vertex. Left multiplication by the group is an
automorphism that is transitive on each block, so the diameter condition only
needs BFS balls from the 2P block representatives. This cost is about n/(2P)
times cheaper than the full all-pairs check and is evaluated as bitmask
propagation. The annealer moves voltages and layer swaps, guided toward
vertices that miss some representative. The best order is climbed by a bandit
over P. Python supplies exact constructions (projective planes, Araujo-Lopez,
W(q)) as the start graph and a validated fallback.
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
# C engine: orbit-representative bi-Cayley annealing, then grow-by-two.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage: prog d D seed time_limit [mode] < start_graph
 * mode: "both" (default), "orbit" (only the lift search), or "grow" (only grow-by-two).
 * stdin: "n m" + m edge lines (valid start), or "0 0".
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
#define MAXP 4
#define PEN 100000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

/* Z_m x|_r Z_q: element a*q+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod q). */
typedef struct {
    int m, q, r;
    int rp[MAXN];
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

/* Number of unordered pairs at distance > D (full all-pairs check). */
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

/* ---------------- groups ---------------- */

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->q, b = x % G->q, c = y / G->q, e = y % G->q;
    long t = ((long)a + (long)G->rp[b] * c) % G->m;
    int ee = (b + e) % G->q;
    return (int)(t * G->q + ee);
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(const Grp *G, int x) {
    int a = x / G->q, b = x % G->q;
    int nb = (G->q - b) % G->q;
    long na = (G->m - ((long)G->rp[nb] * a) % G->m) % G->m;
    return (int)(na * G->q + nb);
}

/* Pick a random semidirect product of order N (uniform over (m, r) pairs). */
static int random_group(int N, Grp *G) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int q = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, q, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) {
                G->m = m; G->q = q; G->r = r;
                found = 1;
            }
        }
    }
    if (!found) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->q; b++)
        G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ---------------- bi-Cayley layered lifts ----------------
 * Vertices: A_{i,g} = i*N+g (i < P), B_{j,h} = (P+j)*N+h.
 * Layer l pairs A_i with B_{lay[l][i]} via A_{i,g} ~ B_{j, g*sv[l][i]}.
 * Every layer is a perfect matching, so the graph is d-regular.
 */
static int P, NG;
static Grp GR;
static int lay[MAXD][MAXP];
static int sv[MAXD][MAXP];
static int nbr[MAXD][MAXN];

static void build_layer(int l) {
    int N = NG;
    for (int i = 0; i < P; i++) {
        int j = lay[l][i], s = sv[l][i];
        int si = ginv(&GR, s);
        for (int g = 0; g < N; g++) {
            int h = gmul(&GR, g, s);
            nbr[l][i * N + g] = (P + j) * N + h;
            nbr[l][(P + j) * N + h] = i * N + gmul(&GR, h, si);
        }
    }
}

/* Duplicate (i, j, s) darts: these would create repeated edges. */
static int dupcount(void) {
    int c = 0, F = d * P;
    for (int f = 0; f < F; f++) {
        int l = f / P, i = f % P;
        for (int f2 = 0; f2 < f; f2++) {
            int l2 = f2 / P, i2 = f2 % P;
            if (i2 == i && lay[l2][i2] == lay[l][i] && sv[l2][i2] == sv[l][i]) {
                c++;
                break;
            }
        }
    }
    return c;
}

/* Representative reach. Bit b of out[v] is set when dist(v, rep_b) <= D, where
 * rep_b = b*N + 0 (group identity in block b). By transitivity inside each block,
 * this covers all pairs. Returns the number of unreached (rep, vertex) pairs. */
static uint64_t WA[MAXN], WB[MAXN];
static long orbit_eval(uint64_t *out) {
    int N = NG, V = 2 * P * N, nbits = 2 * P;
    uint64_t *cur = WA, *nxt = WB;
    for (int v = 0; v < V; v++) cur[v] = 0;
    for (int b = 0; b < nbits; b++) cur[b * N] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < V; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long reached = 0;
    for (int v = 0; v < V; v++) {
        reached += __builtin_popcountll(cur[v]);
        out[v] = cur[v];
    }
    return (long)nbits * V - reached;
}

static uint64_t RX[MAXN], RY[MAXN];

/* Simulated annealing over layer permutations and voltages for the current P, NG.
 * Returns 1 when the lift is d-regular, duplicate-free and has all representatives within D. */
static int orbit_anneal(int iters, int patience, double until) {
    int N = NG, V = 2 * P * N;
    uint64_t full = (1ULL << (2 * P)) - 1;
    uint64_t *cur = RX, *trial = RY, *tmp;
    for (int l = 0; l < d; l++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < P; i++) { lay[l][i] = perm[i]; sv[l][i] = rndint(N); }
        build_layer(l);
    }
    long cost = orbit_eval(cur) + PEN * dupcount();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;
    for (int t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if (t - last > patience) return 0;
        if ((t & 31) == 0 && now() > until) return 0;
        double T = 0.5 + 0.01 * c0 * (1.0 - (double)t / iters);

        int l, i, i2 = -1, mv, old_s = 0;
        if (P >= 2 && rnd01() < 0.2) {
            mv = 0;
            l = rndint(d);
            i = rndint(P);
            i2 = rndint(P - 1);
            if (i2 >= i) i2++;
            int s = lay[l][i]; lay[l][i] = lay[l][i2]; lay[l][i2] = s;
            build_layer(l);
        } else {
            mv = 1;
            l = rndint(d);
            i = rndint(P);
            if (rnd01() < 0.5) {
                /* Guided: pick a vertex that misses some representative and
                 * change the voltage of the layer block that touches it. */
                int v = -1;
                for (int tr = 0; tr < 20 && v < 0; tr++) {
                    int w = rndint(V);
                    if (cur[w] != full) v = w;
                }
                if (v >= 0) {
                    int beta = v / N;
                    if (beta < P) i = beta;
                    else {
                        for (int k = 0; k < P; k++)
                            if (lay[l][k] == beta - P) { i = k; break; }
                    }
                }
            }
            old_s = sv[l][i];
            int nv = rndint(N);
            if (nv == old_s) continue;
            sv[l][i] = nv;
            build_layer(l);
        }

        long nc = orbit_eval(trial) + PEN * dupcount();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
            cost = nc;
            tmp = cur; cur = trial; trial = tmp;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            if (mv == 0) {
                int s = lay[l][i]; lay[l][i] = lay[l][i2]; lay[l][i2] = s;
            } else {
                sv[l][i] = old_s;
            }
            build_layer(l);
        }
    }
    return cost == 0;
}

static void graph_from_state(Graph *g) {
    int N = NG, A = P * N;
    g->n = 2 * A;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= A; }
    for (int l = 0; l < d; l++)
        for (int v = 0; v < A; v++) add_edge(g, v, nbr[l][v]);
}

/* Climb the order ladder: each success must exceed the current best order. */
static void orbit_search(Graph *best, double until) {
    static Graph cand;
    int tries[MAXP + 1], wins[MAXP + 1];
    memset(tries, 0, sizeof tries);
    memset(wins, 0, sizeof wins);
    long moore = moore_bound();
    while (now() < until) {
        if ((long)best->n + 2 > moore || best->n + 2 > MAXN) break;
        int p = 1;
        if (rnd01() < 0.2) p = 1 + rndint(MAXP);
        else {
            double bs = -1.0;
            for (int c = 1; c <= MAXP; c++) {
                double sc = (wins[c] + 1.0) / (tries[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; p = c; }
            }
        }
        long base = (long)best->n / (2 * p);
        long N = base + 1 + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > MAXN || 2L * p * N > moore) continue;
        if (!random_group((int)N, &GR)) continue;
        NG = (int)N;
        P = p;
        tries[p]++;
        if (orbit_anneal(30000, 3000, until)) {
            wins[p]++;
            graph_from_state(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- grow by two ---------------- */

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
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [mode] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    const char *mode = argc > 5 ? argv[5] : "both";
    int do_orbit = strcmp(mode, "grow") != 0;
    int do_grow = strcmp(mode, "orbit") != 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2) {
        double split = do_grow ? t0 + (t_end - t0) * 0.7 : t_end;
        if (do_orbit && best.n < moore_bound()) orbit_search(&best, split);
        if (do_grow && best.n + 2 <= MAXN) grow_search(&best, t_end);
    }
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

    # C engine: orbit-representative lift search, then grow-by-two.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
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
