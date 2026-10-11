"""Irregular-base voltage lifts with dart moves, then full-graph repair.

This version replaces the earlier regular-base lift search with a different construction family.

Lift family: the base has KA classes on side A and KB classes on side B, each of size G, where G is the
order of a semidirect group Z_m x| Z_k2. A dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g. Each
class can carry at most d darts, so the lift has max degree d and is bipartite. Unlike the earlier engine,
the base need not be d-regular or balanced: KA and KB are chosen per run, and the number of darts is free
up to the capacity d per class. Left multiplication is an automorphism of every such lift, so the
diameter is <= D iff a depth-D BFS from the NC = KA+KB class representatives reaches every vertex.
Annealing moves change voltages, reattach dart endpoints, and add or remove darts. The cost is the total
number of unreached (representative, vertex) pairs.

Repair: when a lift is nearly valid but larger than the current best, the full graph is built and repaired
by degree-preserving edge swaps plus edge additions between deficient vertices, with annealing on the
exact count of bad pairs. Growing by two vertices (add a bipartite pair, transfer edges, repair) uses the
same repair routine.

Safety: Python starts from K_{d,d} or a known construction, runs the C engine with a budget that leaves a
margin, re-checks the result with lib.is_valid, and falls back to the start graph on any error.
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

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXC 4
#define MAXDART (MAXD * MAXC)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int nd;
    int di[MAXDART], dj[MAXDART], ds[MAXDART];
} LState;

static int d, D;
static double t_end, t_stop;
static uint64_t rng_state = 88172645463325252ULL;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). Identity is 0. */
static int GM, GK2, GORD;
static int RP[MAXN];

static void set_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

static int sample_group(int total, int *om, int *ok2, int *orr) {
    int cnt = 0;
    for (int m = 1; m <= total; m++) {
        if (total % m) continue;
        int k2 = total / m;
        if (m == 1) {
            if (rndint(++cnt) == 0) { *om = 1; *ok2 = k2; *orr = 0; }
            continue;
        }
        if (k2 == 1) {
            if (rndint(++cnt) == 0) { *om = m; *ok2 = 1; *orr = 1; }
            continue;
        }
        for (int t = 0; t < 120; t++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
            if (rndint(++cnt) == 0) { *om = m; *ok2 = k2; *orr = r; }
        }
    }
    return cnt > 0;
}

/* ------------------------------------------------------------ irregular-base lifts */

static int KA, KB, NC;                    /* classes per side, total classes */
static int nd;                            /* number of darts */
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int LADJ[MAXN][MAXD], LDEG[MAXN];
static int VIS[MAXN], DIST[MAXN], QU[MAXN];
static int VST = 0;
static LState BST_S;

static void save_state(LState *s) {
    s->nd = nd;
    memcpy(s->di, DI, sizeof(int) * nd);
    memcpy(s->dj, DJ, sizeof(int) * nd);
    memcpy(s->ds, DS, sizeof(int) * nd);
}

static void load_state(const LState *s) {
    nd = s->nd;
    memcpy(DI, s->di, sizeof(int) * nd);
    memcpy(DJ, s->dj, sizeof(int) * nd);
    memcpy(DS, s->ds, sizeof(int) * nd);
}

/* Full validity of the dart set: ranges, per-class capacity d, no duplicate darts. */
static int state_ok(void) {
    int ca[MAXC] = {0}, cb[MAXC] = {0};
    for (int t = 0; t < nd; t++) {
        if (DI[t] < 0 || DI[t] >= KA || DJ[t] < 0 || DJ[t] >= KB) return 0;
        if (DS[t] < 0 || DS[t] >= GORD) return 0;
        if (++ca[DI[t]] > d) return 0;
        if (++cb[DJ[t]] > d) return 0;
        for (int u = 0; u < t; u++)
            if (DI[u] == DI[t] && DJ[u] == DJ[t] && DS[u] == DS[t]) return 0;
    }
    return 1;
}

/* Dart t against darts 0..t-1, assuming those are already valid. */
static int new_dart_ok(int t) {
    if (DI[t] < 0 || DI[t] >= KA || DJ[t] < 0 || DJ[t] >= KB) return 0;
    if (DS[t] < 0 || DS[t] >= GORD) return 0;
    int ca = 0, cb = 0;
    for (int u = 0; u < t; u++) {
        if (DI[u] == DI[t]) ca++;
        if (DJ[u] == DJ[t]) cb++;
        if (DI[u] == DI[t] && DJ[u] == DJ[t] && DS[u] == DS[t]) return 0;
    }
    return ca < d && cb < d;
}

static void init_state(void) {
    nd = 0;
    for (int tries = 0; tries < 2000 && nd < MAXDART; tries++) {
        int t = nd;
        DI[t] = rndint(KA);
        DJ[t] = rndint(KB);
        DS[t] = rndint(GORD);
        nd = t + 1;
        if (!new_dart_ok(t)) nd = t;
    }
}

/* Unreached (representative, vertex) pairs over the NC class representatives. */
static long lift_cost(void) {
    int N = NC * GORD;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int g = 0; g < GORD; g++) {
            int a = DI[t] * GORD + g;
            int b = (KA + DJ[t]) * GORD + gmul(g, DS[t]);
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
    long total = 0;
    for (int c = 0; c < NC; c++) {
        int src = c * GORD;
        VST++;
        int head = 0, tail = 0;
        VIS[src] = VST;
        DIST[src] = 0;
        QU[tail++] = src;
        while (head < tail) {
            int u = QU[head++];
            if (DIST[u] >= D) continue;
            for (int i = 0; i < LDEG[u]; i++) {
                int v = LADJ[u][i];
                if (VIS[v] != VST) {
                    VIS[v] = VST;
                    DIST[v] = DIST[u] + 1;
                    QU[tail++] = v;
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void build_full(Graph *g) {
    int N = NC * GORD;
    g->n = N;
    for (int v = 0; v < N; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= KA * GORD;
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < GORD; x++)
            add_edge(g, DI[t] * GORD + x, (KA + DJ[t]) * GORD + gmul(x, DS[t]));
}

/* Annealing over darts; returns the lowest cost seen, with that state saved in BST_S. */
static long anneal_lift(long steps) {
    LState prev;
    long cost = lift_cost();
    long bestc = cost;
    save_state(&BST_S);
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 63) == 0 && now() > t_stop) break;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        save_state(&prev);
        int mv = rndint(100);
        if (mv < 45) {
            if (nd == 0) continue;
            int t = rndint(nd);
            DS[t] = rndint(GORD);
        } else if (mv < 75) {
            if (nd == 0) continue;
            int t = rndint(nd);
            if (rndint(2)) DJ[t] = rndint(KB);
            else DI[t] = rndint(KA);
        } else if (mv < 92) {
            if (nd >= MAXDART) continue;
            DI[nd] = rndint(KA);
            DJ[nd] = rndint(KB);
            DS[nd] = rndint(GORD);
            nd++;
        } else {
            if (nd == 0) continue;
            int t = rndint(nd);
            nd--;
            DI[t] = DI[nd];
            DJ[t] = DJ[nd];
            DS[t] = DS[nd];
        }
        if (!state_ok()) { load_state(&prev); continue; }
        long c2 = lift_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                save_state(&BST_S);
            }
        } else {
            load_state(&prev);
        }
    }
    return bestc;
}

/* ------------------------------------------------------------ full-graph repair */

/* Edge swaps and additions (degree <= d, bipartite) with annealing on the bad-pair count.
 * Returns 1 and leaves g valid if it reaches zero bad pairs before `until`. */
static int repair(Graph *g, double until) {
    static Graph rb;
    int n = g->n;
    if (n < 2) return 0;
    long bad = bad_pairs(g);
    if (bad == 0) return 1;
    long bestbad = bad;
    copy_graph(&rb, g);
    double T = 1.0;
    while (bad > 0 && now() < until) {
        int ok = 0;
        long nb = bad;
        if (rnd01() < 0.2) {
            int a = rndint(n), b = rndint(n);
            if (a != b && g->side[a] != g->side[b] && g->deg[a] < d && g->deg[b] < d &&
                !has_edge(g, a, b)) {
                add_edge(g, a, b);
                nb = bad_pairs(g);
                if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) ok = 1;
                else del_edge(g, a, b);
            }
        } else {
            int v = rndint(n);
            for (int k = 0; k < 30 && badv[v] == 0; k++) v = rndint(n);
            if (g->deg[v] > 0) {
                int u = g->adj[v][rndint(g->deg[v])];
                int s = rndint(n);
                if (s != v && g->side[s] == g->side[v] && g->deg[s] > 0) {
                    int t = g->adj[s][rndint(g->deg[s])];
                    if (t != u && !has_edge(g, v, t) && !has_edge(g, s, u)) {
                        del_edge(g, v, u);
                        del_edge(g, s, t);
                        add_edge(g, v, t);
                        add_edge(g, s, u);
                        nb = bad_pairs(g);
                        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) ok = 1;
                        else {
                            del_edge(g, v, t);
                            del_edge(g, s, u);
                            add_edge(g, v, u);
                            add_edge(g, s, t);
                        }
                    }
                }
            }
        }
        if (ok) bad = nb;
        if (bad < bestbad) {
            bestbad = bad;
            copy_graph(&rb, g);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    if (bestbad == 0) {
        copy_graph(g, &rb);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ lift search */

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    t_stop = until;
    while (now() < until) {
        if (best->n + 1 > moore) return;
        KA = 1 + rndint(MAXC);
        KB = 1 + rndint(MAXC);
        NC = KA + KB;
        long esc = fails > 30 ? (fails - 30) / 30 + 1 : 0;
        if (esc > 8) esc = 8;
        long G0 = (best->n + NC) / NC;          /* NC * G0 >= best->n + 1 */
        long Gl = G0 + rndint(3) + esc;
        if (Gl < 1 || NC * Gl > moore || NC * Gl > MAXN) { fails++; continue; }
        int m, k2, rr;
        if (!sample_group((int)Gl, &m, &k2, &rr)) { fails++; continue; }
        set_group(m, k2, rr);
        init_state();
        long extra = (long)(fails / 20) * 3000;
        if (extra > 40000) extra = 40000;
        long steps = 3000 + rndint(6000) + extra;
        int before = best->n;
        long c = anneal_lift(steps);
        if (c == 0 || (c <= 3L * NC && NC * GORD > best->n)) {
            load_state(&BST_S);
            build_full(&cand);
            if (c == 0) {
                if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
            } else {
                double rend = now() + 2.0;
                if (rend > until) rend = until;
                if (repair(&cand, rend) && cand.n > best->n && is_valid(&cand))
                    copy_graph(best, &cand);
            }
        }
        fails = best->n > before ? 0 : fails + 1;
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
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    return repair(work, until);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    long moore = moore_bound();
    while (now() < until && best->n + 2 <= moore && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice) && is_valid(&work) && work.n > best->n)
            copy_graph(best, &work);
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
    t_end = t0 + limit * 0.97;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.95 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 2.5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
