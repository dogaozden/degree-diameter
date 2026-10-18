"""Combined search: bi-Cayley voltage lifts over Z_m x| Z_k2 with annealing, then
grow-by-two annealing from the best graph, then greedy slack extension.

Python only supplies known starts (projective plane, Araujo-Lopez) and validation.
All search runs in C_SOURCE. build() always returns a checked-valid graph.
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

#define MAXN 2048
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXK 4
#define PEN 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ---------------------------------------------------------------- utilities */

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

static int gcd_i(int a, int b) {
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

/* ---------------------------------------------------------------- graph basics */

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

/* ---------------------------------------------------------------- distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Unordered pairs at distance > D (0 means diameter <= D and connected). */
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

/* ---------------------------------------------------------------- input / output */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------------------------------------------------------- bi-Cayley lifts */
/* Group Z_m x| Z_k2: element (a,b) = a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */

static int GM, GK2, GORD;
static int RP[64], RPI[64];
static int KB;                  /* base blocks per side */
static int LAY[MAXD][MAXK];     /* LAY[l][i]: B-block joined to A-block i in layer l */
static int VOL[MAXD][MAXK];     /* voltage of that dart */
static int NB[MAXD][MAXN];      /* NB[l][v]: layer-l neighbour of v */

static inline int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

static int ginv(int x) {
    int a = x / GK2, b = x % GK2;
    int nb = (GK2 - b) % GK2;
    int c = (int)((GM - ((long)RPI[b] * a) % GM) % GM);
    return c * GK2 + nb;
}

static void setup_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    int rinv = 1 % m;
    for (int t = 1; t < m; t++)
        if ((long)r * t % m == 1 % m) { rinv = t; break; }
    RPI[0] = 1 % m;
    for (int b = 1; b < k2; b++) RPI[b] = (int)((long)RPI[b - 1] * rinv % m);
}

/* Write layer l entries for A-block i and its partner B-block. */
static void set_dart(int l, int i) {
    int j = LAY[l][i], s = VOL[l][i], si = ginv(s);
    int A = i * GORD, B = (KB + j) * GORD;
    for (int g = 0; g < GORD; g++) {
        NB[l][A + g] = B + gmul(g, s);
        NB[l][B + g] = A + gmul(g, si);
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < KB; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (LAY[l][i] == LAY[l2][i] && VOL[l][i] == VOL[l2][i]) c++;
    return c;
}

/* R[v] bit b = representative of block b is within D of v. Returns unreached pair count. */
static long compute_reach(uint64_t *R) {
    int NV = 2 * KB * GORD;
    static uint64_t tmp[MAXN];
    memset(R, 0, sizeof(uint64_t) * NV);
    for (int b = 0; b < 2 * KB; b++) R[b * GORD] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint64_t x = R[v];
            for (int l = 0; l < d; l++) x |= R[NB[l][v]];
            tmp[v] = x;
            changed |= (x != R[v]);
        }
        memcpy(R, tmp, sizeof(uint64_t) * NV);
        if (!changed) break;
    }
    long unreached = 2L * KB * NV;
    for (int v = 0; v < NV; v++) unreached -= __builtin_popcountll(R[v]);
    return unreached;
}

static long lift_cost(uint64_t *R) { return compute_reach(R) + PEN * dupcount(); }

/* Simulated annealing on the current layers/voltages. Returns 1 when cost reaches 0. */
static int bc_anneal(int iters, long patience, double deadline) {
    static uint64_t BUF1[MAXN], BUF2[MAXN];
    uint64_t *cur = BUF1, *nxt = BUF2, *tmpp;
    int NV = 2 * KB * GORD;
    uint64_t full = (1ULL << (2 * KB)) - 1;
    long cost = lift_cost(cur);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) return 0;
        if ((t & 63) == 0 && now() > deadline) return 0;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (KB >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(KB), i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            int s = LAY[l][i1]; LAY[l][i1] = LAY[l][i2]; LAY[l][i2] = s;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = lift_cost(nxt);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                tmpp = cur; cur = nxt; nxt = tmpp;
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                s = LAY[l][i1]; LAY[l][i1] = LAY[l][i2]; LAY[l][i2] = s;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = rndint(d), i = rndint(KB);
        if (rnd01() < 0.4) {  /* defect-targeted choice */
            int u = -1;
            for (int tr = 0; tr < 20 && u < 0; tr++) {
                int v = rndint(NV);
                if (cur[v] != full) u = v;
            }
            if (u >= 0) {
                int blk = u / GORD;
                if (blk < KB) i = blk;
                else
                    for (int ii = 0; ii < KB; ii++)
                        if (LAY[l][ii] == blk - KB) i = ii;
            }
        }
        int old = VOL[l][i];
        int nv = rndint(GORD);
        if (nv == old) continue;
        VOL[l][i] = nv;
        set_dart(l, i);
        long c2 = lift_cost(nxt);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            tmpp = cur; cur = nxt; nxt = tmpp;
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            VOL[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static void graph_from_lift(Graph *g) {
    int NV = 2 * KB * GORD, NA = KB * GORD;
    g->n = NV;
    for (int v = 0; v < NV; v++) { g->deg[v] = 0; g->side[v] = v >= NA; }
    for (int u = 0; u < NA; u++)
        for (int l = 0; l < d; l++) add_edge(g, u, NB[l][u]);
}

static void bicayley_phase(Graph *best, double until) {
    static const int K2L[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    static Graph cand;
    long moore = moore_bound();
    double trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    long fails = 0;
    while (now() < until && fails < 200000) {
        int k = 1;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1) / (trials[c] + 2) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        int bn = best->n;
        int base = bn / (2 * k);
        int Gt = (bn + 2 + 2 * k - 1) / (2 * k) + rndint(base / 8 + 2);
        int k2 = K2L[rndint(20)];
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        long G = (long)m * k2;
        long N = 2L * k * G;
        if (N > moore || N > MAXN || N <= bn) { fails++; continue; }

        int r = -1, cnt = 0;   /* uniform random r with gcd(r,m)=1 and r^k2 = 1 mod m */
        for (int c = 1; c < m; c++) {
            if (gcd_i(c, m) != 1) continue;
            if (powmod(c, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) r = c;
        }
        if (r < 0) { fails++; continue; }

        setup_group(m, k2, r);
        KB = k;
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < KB; i++) LAY[l][i] = i;
            for (int i = KB - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = LAY[l][i]; LAY[l][i] = LAY[l][j]; LAY[l][j] = s;
            }
            for (int i = 0; i < KB; i++) VOL[l][i] = rndint(GORD);
        }
        for (int l = 0; l < d; l++)
            for (int i = 0; i < KB; i++) set_dart(l, i);

        trials[k] += 1;
        if (bc_anneal(6000, 1500, until)) {
            graph_from_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                wins[k] += 1;
            }
        }
    }
}

/* ---------------------------------------------------------------- grow by two */

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

/* ---------------------------------------------------------------- slack extension */

static void slack_phase(Graph *best, double until) {
    static Graph w;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until && fails < 3000 && best->n + 1 <= moore && best->n + 1 <= MAXN) {
        int s = rndint(2);
        int spare[MAXN], ns = 0;
        for (int v = 0; v < best->n; v++)
            if (best->side[v] == s && best->deg[v] < d) spare[ns++] = v;
        if (ns < d) {
            s = 1 - s;
            ns = 0;
            for (int v = 0; v < best->n; v++)
                if (best->side[v] == s && best->deg[v] < d) spare[ns++] = v;
        }
        if (ns < d) break;
        copy_graph(&w, best);
        int nv = best->n;
        w.n = nv + 1;
        w.deg[nv] = 0;
        w.side[nv] = (unsigned char)(1 - s);
        for (int c = 0; c < d; c++) {
            int j = c + rndint(ns - c);
            int tmp = spare[c]; spare[c] = spare[j]; spare[j] = tmp;
            add_edge(&w, nv, spare[c]);
        }
        if (is_valid(&w)) { copy_graph(best, &w); fails = 0; }
        else fails++;
    }
}

/* ---------------------------------------------------------------- main */

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1) { printf("1 0\n"); return 0; }
    if (D == 1 || d > MAXD) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double T = t_end - t0;
        bicayley_phase(&best, t0 + 0.55 * T);
        grow_search(&best, t0 + 0.9 * T);
        slack_phase(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python builds directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graph 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2: always a safe fallback for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    start = known_start(d, D)
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start
    else:
        start = None if start is None or not lib.is_valid(start[0], start[1], d, D) else start

    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing to search

    budget = 0.85 * time_limit - 2.0 - (time.monotonic() - t0)
    if start is not None and D == 3:
        budget = min(budget, 8.0)   # calibration-style case: keep it quick
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass   # keep the valid fallback
    return best
