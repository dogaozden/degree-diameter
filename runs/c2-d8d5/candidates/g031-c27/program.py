"""Bold variant: voltage lifts of a dense projective-plane base, then C annealing and growth.

Python builds exact small constructions and a dense base graph (PG(2,q) or K_{d,d}).
The C engine lifts that base over Z_m, anneals the voltages until every base vertex
reaches all lift vertices within D steps, then grows the best lift by two vertices at a time.
"""
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


C_SOURCE = r'''
/* Voltage-lift search on a dense bipartite base, then grow-by-two annealing.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXE 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;

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

/* Number of unordered pairs at distance > D. Fills badv[v] = number of bad partners of v. */
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

/* ---------------- voltage lifts of a base graph over Z_m ---------------- */

static int NB, NE, MM;
static int BSIDE[MAXN], BDEG[MAXN], BINC[MAXN][MAXD];
static int EU[MAXE], EV[MAXE], VG[MAXE];   /* EU on side 0, EV on side 1 */
static int FREE[MAXE], nfree;
static int vis[MAXN], qu[MAXN], qx[MAXN];
static int vstamp = 0;

static void build_base(const Graph *g) {
    NB = g->n;
    NE = 0;
    for (int u = 0; u < NB; u++) { BSIDE[u] = g->side[u]; BDEG[u] = 0; }
    for (int u = 0; u < NB; u++) {
        if (g->side[u] != 0) continue;
        for (int i = 0; i < g->deg[u]; i++) {
            EU[NE] = u;
            EV[NE] = g->adj[u][i];
            NE++;
        }
    }
    for (int e = 0; e < NE; e++) {
        BINC[EU[e]][BDEG[EU[e]]++] = e;
        BINC[EV[e]][BDEG[EV[e]]++] = e;
    }
}

/* Spanning tree of the base: tree edges keep voltage 0, the rest are free. */
static int mark_tree(void) {
    static int seen[MAXN], q[MAXN], intree[MAXE];
    memset(seen, 0, sizeof(int) * NB);
    memset(intree, 0, sizeof(int) * NE);
    int head = 0, tail = 0;
    seen[0] = 1;
    q[tail++] = 0;
    while (head < tail) {
        int u = q[head++];
        for (int k = 0; k < BDEG[u]; k++) {
            int e = BINC[u][k];
            int w = (EU[e] == u) ? EV[e] : EU[e];
            if (!seen[w]) { seen[w] = 1; intree[e] = 1; q[tail++] = w; }
        }
    }
    if (tail != NB) return 0;
    nfree = 0;
    for (int e = 0; e < NE; e++)
        if (!intree[e]) FREE[nfree++] = e;
    return 1;
}

/* Sum over base representatives (u,0) of the lift vertices NOT within distance D.
 * Zero iff the lift has diameter <= D (lift is fibre-transitive).
 * Stops early and returns a value > limit once the partial sum exceeds limit. */
static long cover_cost_limit(long limit) {
    long N = (long)NB * MM, cost = 0;
    for (int s = 0; s < NB; s++) {
        vstamp++;
        int head = 0, tail = 0;
        vis[s * MM] = vstamp;
        qu[tail] = s;
        qx[tail] = 0;
        tail++;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qu[head], x = qx[head];
                head++;
                for (int k = 0; k < BDEG[u]; k++) {
                    int e = BINC[u][k], v, y;
                    if (u == EU[e]) {
                        v = EV[e];
                        y = x + VG[e];
                        if (y >= MM) y -= MM;
                    } else {
                        v = EU[e];
                        y = x - VG[e];
                        if (y < 0) y += MM;
                    }
                    int id = v * MM + y;
                    if (vis[id] != vstamp) {
                        vis[id] = vstamp;
                        qu[tail] = v;
                        qx[tail] = y;
                        tail++;
                    }
                }
            }
        }
        cost += N - tail;
        if (cost > limit) return cost;
    }
    return cost;
}

/* Simulated annealing over free voltages in Z_m. Returns 0 and fills out[] when a
 * diameter-D lift is found; otherwise returns the best remaining cost. */
static long anneal(int m, double until, int *out) {
    MM = m;
    for (int e = 0; e < NE; e++) VG[e] = 0;
    for (int i = 0; i < nfree; i++) VG[FREE[i]] = rndint(m);
    long cur = cover_cost_limit((long)1 << 60);
    double t_start = now();
    double span = until - t_start;
    if (span < 1e-3) span = 1e-3;
    while (cur > 0 && nfree > 0) {
        double tn = now();
        if (tn > until) break;
        double frac = (tn - t_start) / span;
        double T = 0.05 + 0.02 * (double)(cur + 1) * (1.0 - frac);
        int f = FREE[rndint(nfree)];
        int old = VG[f];
        int nv = rndint(m);
        if (nv == old) continue;
        double lim = (double)cur - T * log(rnd01() + 1e-12);
        long L = (long)floor(lim);
        VG[f] = nv;
        long c2 = cover_cost_limit(L);
        if (c2 <= L) cur = c2;
        else VG[f] = old;
    }
    if (cur == 0) memcpy(out, VG, sizeof(int) * NE);
    return cur;
}

static void build_lift(Graph *g, int m, const int *vg) {
    g->n = NB * m;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)BSIDE[v / m];
    }
    for (int e = 0; e < NE; e++)
        for (int x = 0; x < m; x++) {
            int y = x + vg[e];
            if (y >= m) y -= m;
            add_edge(g, EU[e] * m + x, EV[e] * m + y);
        }
}

/* Try lifts of the current best graph (as base) with growing m. Lifts are searched
 * starting near the target order (about 0.30 * Moore bound), stepping down by
 * bisection on failure and up by one on success. */
static void lift_phase(Graph *best, double until) {
    static Graph cand;
    static int fvg[MAXE];
    double L = until - now();
    if (L < 0.5) return;
    build_base(best);
    if (!mark_tree()) return;
    long moore = moore_bound();
    long mmax = moore / NB;
    if (mmax > MAXN / NB) mmax = MAXN / NB;
    long lastok = 1;
    long m = (long)(0.30 * (double)moore) / NB + 1;
    if (m <= lastok) m = lastok + 1;
    if (m > mmax) m = mmax;
    while (now() < until && m > lastok && m <= mmax) {
        int ok = 0;
        double slice = 0.15 * L;
        for (int att = 0; att < 2 && !ok; att++) {
            double tl = until - now();
            if (tl <= 0.05) break;
            double sl = slice < tl ? slice : tl;
            if (anneal((int)m, now() + sl, fvg) == 0) ok = 1;
        }
        if (ok) {
            build_lift(&cand, (int)m, fvg);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
            lastok = m;
            m++;
        } else {
            if (m == lastok + 1) break;
            m = lastok + (m - lastok) / 2;
            if (m <= lastok) m = lastok + 1;
        }
    }
}

/* ---------------- grow-by-two annealing ---------------- */

static int bad_list[MAXN];
static int badsave[MAXN];
static int used_arr[MAXN];
static int used_stamp = 0;

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
    used_stamp++;
    used_arr[x] = used_arr[y] = used_stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used_arr[a] == used_stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used_arr[b] == used_stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used_arr[a] = used_arr[b] = used_stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int nbad = 0;
        for (int w = 0; w < work->n; w++)
            if (badv[w] > 0) bad_list[nbad++] = w;
        int v = nbad ? bad_list[rndint(nbad)] : rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        memcpy(badsave, badv, sizeof(int) * work->n);
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
            memcpy(badv, badsave, sizeof(int) * work->n);
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
    double t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_phase(&best, t0 + (t_end - t0) * 0.8);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions (calibration cases return immediately).
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

    # Bold search: voltage lifts of the dense base, grown by C annealing.
    budget = end - time.monotonic() - 0.5
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 8)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
