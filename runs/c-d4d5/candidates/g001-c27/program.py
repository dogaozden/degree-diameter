"""Bi-Cayley / voltage-lift search over semidirect groups, with a BFS-based energy.

Main change: each base vertex class of a lift is vertex-transitive under left
multiplication by the group, so the diameter of a lift over a group of order N
is determined by eccentricities of 2p source vertices (the identity of each
class). Simulated annealing over base-graph darts and voltages minimises the
number of vertex pairs at distance > D from those sources. Energy 0 gives a
valid lift. A bitset check validates every candidate. If nothing beats the
start graph, Python returns the start graph, so a failure cannot lower the score.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley / voltage-lift annealer with a source-only energy, plus grow-by-two.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * A lift: base p A-vertices and p B-vertices, d darts per vertex (d random
 * permutations). Dart (i, j, g) joins (i, x) to (j, x*g) for all x in group G.
 * Left multiplication by G is an automorphism, so the energy only needs BFS
 * from the identities (A_i, e) and (B_j, e).
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
#define MAXG 1024
#define MAXDART (MAXP * MAXD)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static double deadline;

/* ------------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ bitset check */

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

/* ------------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* ------------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a, b) = a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXG];
} Grp;

static int MT[MAXG][MAXG]; /* multiplication table of the current group */
static int INV[MAXG];      /* inverses */
static int GN;             /* current group order */

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
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
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

static void build_tables(const Grp *G, int N) {
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x][y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------------------------ lifts */

static int BP, NG, nd;                       /* base size, group order, number of darts */
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];
static int aL[MAXP][MAXD], aC[MAXP], bL[MAXP][MAXD], bC[MAXP];
static int distv[MAXN], qv[MAXN];

static void rebuild_lists(void) {
    for (int i = 0; i < BP; i++) { aC[i] = 0; bC[i] = 0; }
    for (int t = 0; t < nd; t++) {
        aL[dI[t]][aC[dI[t]]++] = t;
        bL[dJ[t]][bC[dJ[t]]++] = t;
    }
}

/* No two darts may have the same (i, j, g): that would give a duplicate edge. */
static int darts_ok(void) {
    for (int t = 0; t < nd; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dG[t] == dG[u]) return 0;
    return 1;
}

/* Number of (source, vertex) pairs with distance > D, over the 2p class identities. */
static long lift_energy(void) {
    int N = NG, pN = BP * N, V = 2 * pN;
    long bad = 0;
    for (int s = 0; s < 2 * BP; s++) {
        int src = s < BP ? s * N : pN + (s - BP) * N;
        for (int v = 0; v < V; v++) distv[v] = -1;
        int head = 0, tail = 0;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            if (distv[v] >= D) continue;
            int nxt = distv[v] + 1;
            if (v < pN) {
                int i = v / N, x = v % N;
                for (int k = 0; k < aC[i]; k++) {
                    int t = aL[i][k];
                    int w = pN + dJ[t] * N + MT[x][dG[t]];
                    if (distv[w] < 0) { distv[w] = nxt; qv[tail++] = w; }
                }
            } else {
                int off = v - pN, j = off / N, z = off % N;
                for (int k = 0; k < bC[j]; k++) {
                    int t = bL[j][k];
                    int w = dI[t] * N + MT[z][INV[dG[t]]];
                    if (distv[w] < 0) { distv[w] = nxt; qv[tail++] = w; }
                }
            }
        }
        bad += V - tail;
    }
    return bad;
}

/* Random base: d random permutations of p points; voltages distinct per (i, j). */
static void random_lift(int p, int N) {
    BP = p;
    NG = N;
    nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < p; i++) {
            dI[nd] = i;
            dJ[nd] = perm[i];
            dG[nd] = -1;
            nd++;
        }
    }
    for (int t = 0; t < nd; t++) {
        for (;;) {
            int g = rndint(N), ok = 1;
            for (int u = 0; u < nd; u++)
                if (u != t && dG[u] == g && dI[u] == dI[t] && dJ[u] == dJ[t]) { ok = 0; break; }
            if (ok) { dG[t] = g; break; }
        }
    }
    rebuild_lists();
}

/* Simulated annealing on darts. Returns the final energy, or -1 on timeout. */
static long anneal(long steps, double T0, double T1) {
    long E = lift_energy();
    for (long s = 0; s < steps && E > 0; s++) {
        if ((s & 127) == 0 && now() > deadline) return -1;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int kind = rndint(3);
        int t1 = rndint(nd), t2 = rndint(nd);
        int og1 = dG[t1], og2 = dG[t2], oj1 = dJ[t1], oj2 = dJ[t2];
        if (kind == 0) {
            int g = rndint(NG);
            if (g == og1) continue;
            dG[t1] = g;
        } else {
            if (oj1 == oj2) continue;
            dJ[t1] = oj2;
            dJ[t2] = oj1;
        }
        rebuild_lists();
        long E2 = -1;
        if (darts_ok()) E2 = lift_energy();
        if (E2 >= 0 && (E2 <= E || rnd01() < exp((double)(E - E2) / T))) {
            E = E2;
        } else {
            dG[t1] = og1;
            dG[t2] = og2;
            dJ[t1] = oj1;
            dJ[t2] = oj2;
            rebuild_lists();
        }
    }
    return E;
}

static void graph_from_lift(Graph *g) {
    int N = NG, pN = BP * N;
    g->n = 2 * pN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= pN; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, pN + dJ[t] * N + MT[x][dG[t]]);
}

/* Repeatedly pick a random group of a suitable order, then anneal lifts over it. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    long fails = 0;
    deadline = until;
    while (now() < until) {
        long target = best->n + 2;
        if (target > moore) return;
        int r = rndint(7);
        int p = r < 3 ? 1 : r < 5 ? 2 : r < 6 ? 3 : 4;
        long N = (target + 2L * p - 1) / (2L * p) + rndint(3);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2L * p * N > MAXN || N > MAXG) {
            if (++fails > 100000) return;
            continue;
        }
        if (!random_group((int)N, &G)) continue;
        build_tables(&G, (int)N);
        int ok = 0;
        for (int att = 0; att < 3 && !ok; att++) {
            random_lift(p, (int)N);
            long E = anneal(25000, 2.0, 0.05);
            if (E < 0) return;
            if (E == 0) ok = 1;
        }
        if (ok) {
            graph_from_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

/* Add one vertex per side (degree d each), then anneal edge swaps on bad pairs. */
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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------------ main */

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
    deadline = t_end;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double t_mid = t0 + (t_end - t0) * 0.8;
        lift_search(&best, t_mid);
        grow_search(&best, t_end);
    }
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


def _fallback(d, D):
    """A graph that is always valid: K_{d,d} if it works, else K_2, else a single vertex."""
    try:
        k = lib.haar_graph(d, range(d))
        if lib.is_valid(*k, d, D):
            return k
    except Exception:
        pass
    e = (2, [(0, 1)])
    if lib.is_valid(*e, d, D):
        return e
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is not None and lib.is_valid(*start, d, D):
        best = start
    else:
        best = _fallback(d, D)
    if best[0] >= lib.moore_bound(d, D):
        return best   # already a Moore graph: nothing to search for
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
