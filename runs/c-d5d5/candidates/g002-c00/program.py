"""Bi-Cayley voltage lifts plus prune-and-refill, searched in one C engine.

Pipeline (C engine, all search):
  1. Lift climb: simulated annealing over voltages of layered bi-Cayley lifts over
     metacyclic groups Z_m x| Z_k. Diameter is checked from the 2k orbit representatives
     only, since left translations are automorphisms. Each accepted lift is valid and
     larger than the best so far.
  2. Prune-and-refill: anneal a lift a few vertices larger than the best (cost = unreached
     pairs, not required to be zero), convert it to a simple graph, remove the worst
     vertices by bad-pair count, refill degree slots and anneal 2-switches.
  3. Grow by two: insert one vertex per side and anneal edge swaps until valid.

Python builds a known start graph (projective plane / Araujo-Lopez for D = 3), falls back
to K_{d,d}, runs the C engine, and returns only graphs that pass lib.is_valid.
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

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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
static long rndlong(long k) { return (long)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
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

/* Remove vertex v (its edges first), moving the last vertex into slot v. */
static void remove_vertex(Graph *g, int v) {
    while (g->deg[v] > 0) {
        int u = g->adj[v][0];
        del_edge(g, v, u);
    }
    int last = g->n - 1;
    if (v != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int u = g->adj[last][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == last) { g->adj[u][j] = v; break; }
        }
        g->deg[v] = g->deg[last];
        g->side[v] = g->side[last];
        memcpy(g->adj[v], g->adj[last], sizeof(int) * g->deg[last]);
    }
    g->deg[last] = 0;
    g->n--;
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Unordered pairs at distance > D (0 means diameter <= D). Also sets badv[v]. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------ input / output */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ metacyclic groups */

/* Z_m x|_r Z_k with element (a,b) coded a*k+b; (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int grp_mul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    int na = (int)(((long long)a + (long long)G->rp[b] * c) % G->m);
    return na * G->k + (b + e) % G->k;
}

static int grp_inv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long long na = (-(long long)G->rp[nb] * a) % G->m;
    if (na < 0) na += G->m;
    return (int)na * G->k + nb;
}

/* Uniform-ish random (m, k, r) with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
static void random_group(int N, Grp *G) {
    long cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (pmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndlong(cnt) == 0) {
                G->m = m;
                G->k = k;
                G->r = r;
            }
        }
    }
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++)
        G->rp[b] = (int)((long long)G->rp[b - 1] * G->r % G->m);
}

/* ------------------------------------------------------------ layered voltage lifts */
/* Vertices: A_{i,x} = i*G + x (i < k), B_{j,h} = (k+j)*G + h.
   Layer l is a permutation dj[l*k+i] of B indices; dart (l,i) has voltage ds[l*k+i].
   Edge A_{i,x} -- B_{dj, x*ds}. Each vertex gets one neighbour per layer: degree d. */

typedef struct {
    int k, d, G, N;
    Grp grp;
    int dj[MAXD * MAXK];
    int ds[MAXD * MAXK];
    int dsi[MAXD * MAXK];
    int adj[MAXN * MAXD];
} Lift;

static int LVIS[MAXN], LQ[MAXN], lstamp = 0;

static void lift_build_adj(Lift *L) {
    int k = L->k, d = L->d, G = L->G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            int j = L->dj[idx], s = L->ds[idx], si = L->dsi[idx];
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                L->adj[a * d + l] = (k + j) * G + grp_mul(&L->grp, x, s);
                int b = (k + j) * G + x;
                L->adj[b * d + l] = i * G + grp_mul(&L->grp, x, si);
            }
        }
    }
}

static void lift_random_init(Lift *L) {
    int k = L->k, d = L->d;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            int idx = l * k + i;
            L->dj[idx] = perm[i];
            L->ds[idx] = rndint(L->G);
            L->dsi[idx] = grp_inv(&L->grp, L->ds[idx]);
        }
    }
}

/* Cost = unreached (representative, vertex) pairs + N per duplicate dart pair.
   Zero means a valid simple lift with diameter <= diam. */
static long lift_cost(Lift *L, int diam) {
    int k = L->k, d = L->d, G = L->G, N = L->N;
    long cost = 0;
    for (int l = 0; l < d; l++)
        for (int l2 = l + 1; l2 < d; l2++)
            for (int i = 0; i < k; i++) {
                int a = l * k + i, b = l2 * k + i;
                if (L->dj[a] == L->dj[b] && L->ds[a] == L->ds[b]) cost += N;
            }
    lift_build_adj(L);
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = rep * G;
        if (++lstamp >= 0x3fffffff) {
            memset(LVIS, 0, sizeof LVIS);
            lstamp = 1;
        }
        int head = 0, tail = 0;
        LQ[tail++] = src;
        LVIS[src] = lstamp;
        for (int depth = 0; depth < diam && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = LQ[head++];
                const int *au = L->adj + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = au[t];
                    if (LVIS[v] != lstamp) {
                        LVIS[v] = lstamp;
                        LQ[tail++] = v;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

/* Metropolis annealing over voltages and B-targets. Returns the final cost
   (zero means valid). The state's adjacency may be stale, so callers that
   use it must call lift_build_adj first. */
static long lift_anneal(Lift *L, int diam, long iters, double T0, double T1, double tend) {
    int k = L->k, d = L->d, G = L->G;
    long cost = lift_cost(L, diam);
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 63) == 0 && now() > tend) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (k >= 2 && rnd01() < 0.3) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int a = l * k + i1, b = l * k + i2;
            int t = L->dj[a];
            L->dj[a] = L->dj[b];
            L->dj[b] = t;
            long c2 = lift_cost(L, diam);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = L->dj[a];
                L->dj[a] = L->dj[b];
                L->dj[b] = t;
            }
        } else {
            int idx = rndint(d * k);
            int os = L->ds[idx], osi = L->dsi[idx];
            int ns = rndint(G);
            if (ns == os) continue;
            L->ds[idx] = ns;
            L->dsi[idx] = grp_inv(&L->grp, ns);
            long c2 = lift_cost(L, diam);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                L->ds[idx] = os;
                L->dsi[idx] = osi;
            }
        }
    }
    return cost;
}

/* Convert the lift to a simple Graph (duplicate darts are skipped). */
static void lift_to_graph(Lift *L, Graph *g) {
    int k = L->k, d = L->d, G = L->G;
    lift_build_adj(L);
    g->n = 2 * k * G;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= k * G);
    }
    for (int a = 0; a < k * G; a++)
        for (int l = 0; l < d; l++) {
            int b = L->adj[a * d + l];
            if (!has_edge(g, a, b)) add_edge(g, a, b);
        }
}

/* Climb: lifts strictly larger than best, each fully valid. */
static void lift_phase(Graph *best, double until) {
    static Lift L;
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n >= moore) return;
        int k = 1 + rndint(MAXK);
        int Gmin = best->n / (2 * k) + 1;
        if (Gmin < 2) Gmin = 2;
        int G = Gmin + rndint(Gmin / 12 + 2);
        long N = 2L * k * G;
        if (N > MAXN || N > moore) {
            if (++fails > 500) return;
            continue;
        }
        L.k = k;
        L.d = d;
        L.G = G;
        L.N = (int)N;
        random_group(G, &L.grp);
        lift_random_init(&L);
        long cost = lift_anneal(&L, D, 60000, 3.0, 0.15, until);
        if (cost == 0) {
            lift_to_graph(&L, &cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ prune and refill */

/* Greedily add edges between deficient opposite-side vertices. */
static void fill_pass(Graph *g) {
    static int LA[MAXN], LB[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] >= d) continue;
        if (g->side[v] == 0) LA[na++] = v; else LB[nb++] = v;
    }
    for (int i = na - 1; i > 0; i--) { int j = rndint(i + 1); int t = LA[i]; LA[i] = LA[j]; LA[j] = t; }
    for (int i = nb - 1; i > 0; i--) { int j = rndint(i + 1); int t = LB[i]; LB[i] = LB[j]; LB[j] = t; }
    for (int i = 0; i < na; i++) {
        int a = LA[i];
        for (int j = 0; j < nb && g->deg[a] < d; j++) {
            int b = LB[j];
            if (g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
        }
    }
}

/* Degree-preserving 2-switch with Metropolis acceptance on bad pairs. */
static void switch_move(Graph *g, long *bad, double T) {
    int n = g->n;
    int v = rndint(n);
    if (g->deg[v] == 0) return;
    int u = g->adj[v][rndint(g->deg[v])];
    int s = rndint(n);
    if (s == v || g->side[s] != g->side[v] || g->deg[s] == 0) return;
    int t = g->adj[s][rndint(g->deg[s])];
    if (t == u || has_edge(g, v, t) || has_edge(g, s, u)) return;
    del_edge(g, v, u);
    del_edge(g, s, t);
    add_edge(g, v, t);
    add_edge(g, s, u);
    long nb = bad_pairs(g);
    if (nb <= *bad || rnd01() < exp((double)(*bad - nb) / T)) {
        *bad = nb;
    } else {
        del_edge(g, v, t);
        del_edge(g, s, u);
        add_edge(g, v, u);
        add_edge(g, s, t);
    }
}

/* Vertex on the given side with the most bad pairs (ties random; sometimes uniform). */
static int worst_on(const Graph *g, int side) {
    if (rnd01() < 0.2) {
        for (int tries = 0; tries < 1000; tries++) {
            int v = rndint(g->n);
            if (g->side[v] == side) return v;
        }
    }
    int best = -1;
    long bv = -1;
    int ties = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->side[v] != side) continue;
        if ((long)badv[v] > bv) { bv = badv[v]; best = v; ties = 1; }
        else if ((long)badv[v] == bv) { ties++; if (rndint(ties) == 0) best = v; }
    }
    return best;
}

static void prune_round(const Graph *start, Graph *best, double until) {
    static Graph w;
    copy_graph(&w, start);
    long bad = bad_pairs(&w);
    while (bad > 0 && now() < until && w.n - 2 > best->n) {
        fill_pass(&w);
        bad = bad_pairs(&w);
        if (bad == 0) break;
        for (int it = 0; it < 300 && bad > 0; it++) switch_move(&w, &bad, 0.6);
        if (bad == 0) break;
        bad = bad_pairs(&w);
        int a = worst_on(&w, 0), b = worst_on(&w, 1);
        if (a < 0 || b < 0 || a == b) break;
        int hi = a > b ? a : b, lo = a > b ? b : a;
        remove_vertex(&w, hi);
        remove_vertex(&w, lo);
        bad = bad_pairs(&w);
    }
    fill_pass(&w);
    bad = bad_pairs(&w);
    if (bad == 0 && w.n > best->n && is_valid(&w)) copy_graph(best, &w);
}

static void prune_phase(Graph *best, double until) {
    static Lift L;
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int k = 1 + rndint(MAXK);
        int extra = 4 + 2 * rndint(6);
        long G = ((long)best->n + extra + 2L * k - 1) / (2L * k);
        if (G < 2) G = 2;
        long N = 2L * k * G;
        if (N > MAXN || N > (long)best->n + 40 || N > moore) {
            if (++fails > 500) return;
            continue;
        }
        L.k = k;
        L.d = d;
        L.G = (int)G;
        L.N = (int)N;
        random_group((int)G, &L.grp);
        lift_random_init(&L);
        lift_anneal(&L, D, 20000, 2.0, 0.1, until);
        lift_to_graph(&L, &cand);
        prune_round(&cand, best, until);
    }
}

/* ------------------------------------------------------------ grow by two */

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
    for (int c = 0, tries = 0; c < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        c++;
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
    while (now() < until) {
        if (best->n + 2 > moore_bound() || best->n + 2 > MAXN) return;
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rng_state ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    int had_start = best.n > 0;
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    if (best.n < moore) {
        double span = t_end - t0;
        lift_phase(&best, t0 + span * (had_start ? 0.25 : 0.40));
        prune_phase(&best, t0 + span * 0.70);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))             # K_{d,d}: valid for D >= 2
    start = known_start(d, D)
    best = start if start is not None else fallback
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback

    if best[0] >= lib.moore_bound(d, D):
        return best

    elapsed = time.monotonic() - t0
    budget = 0.88 * time_limit - elapsed - 2.0
    if budget > 0.5:
        try:
            text = lib.run_c(
                C_SOURCE,
                [d, D, seed, f"{budget:.2f}"],
                stdin_graph=best,
                timeout=max(2.0, 0.95 * time_limit - (time.monotonic() - t0) - 3.0),
            )
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
