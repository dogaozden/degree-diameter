"""Bi-Cayley tabu search with edge-swap growth for the d=5, D=7 target.

Construction changes from the parent:
  * The bi-Cayley phase uses tabu search over voltage sets instead of annealed hill-climbing.
    Each step samples a neighbourhood of single-voltage moves, takes the best non-tabu move,
    and restarts after a stall. Groups are semidirect products Z_m x| Z_k, sampled from all
    admissible (m, k, r) for a random divisor m of N.
  * Growth uses one random pair-wiring followed by edge-swap annealing on the exact bad-pair
    count. Ruin-and-recreate is dropped.
  * Python keeps the hexagon, projective-plane and Araujo-Pardo-Lopez starts, and returns the
    largest one that passes lib.is_valid if the C output is not an improvement.
"""
import itertools
import time

import numpy as np

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
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXH 2048
#define NBR 24
#define TENURE 7
#define STALL 300
#define SPAN 160

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
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

/* Number of unordered pairs at distance > D, by bitset expansion. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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

/* ---------------- groups ----------------
 * Z_m x| Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Table MT[x*NG+y]. */
static int MT[MAXH * MAXH];
static int INV[MAXH];
static int NG;

static void build_group(int m, int k, int r) {
    static int rp[MAXH];
    NG = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < NG; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < NG; y++) {
            int c = y / k, e = y % k;
            MT[(size_t)x * NG + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < NG; x++)
        for (int y = 0; y < NG; y++)
            if (MT[(size_t)x * NG + y] == 0) { INV[x] = y; break; }
}

/* Random admissible (m, k, r) with m*k = N. Falls back to the cyclic group. */
static void sample_group(int N, int *om, int *ok, int *orr) {
    int divs[64], nd = 0;
    for (int m = 1; m <= N && nd < 64; m++)
        if (N % m == 0) divs[nd++] = m;
    int m = divs[rndint(nd)];
    int k = N / m;
    if (m == 1) { *om = 1; *ok = k; *orr = 0; return; }
    int cand[MAXH], nc = 0;
    for (int r = 1; r < m; r++)
        if (gcd_i(r, m) == 1 && powmod(r, k, m) == 1) cand[nc++] = r;
    if (nc == 0) { *om = N; *ok = 1; *orr = 1; return; }
    *om = m;
    *ok = k;
    *orr = cand[rndint(nc)];
}

/* ---------------- bi-Cayley evaluation ----------------
 * Vertices a_x = x, b_x = N + x. Edges a_x -- b_{x*g_t}, g_0 = e, distinct g_t.
 * Left multiplication is transitive on each side, so BFS from a_e and b_e counts all bad pairs. */
static int dist_b[2 * MAXH], mark_b[2 * MAXH], queue_b[2 * MAXH];
static int stamp_b = 0;

static long eval_gv(const int *gv) {
    int N = NG, V = 2 * N;
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_b++;
        mark_b[src] = stamp_b;
        dist_b[src] = 0;
        queue_b[tail++] = src;
        while (head < tail) {
            int v = queue_b[head++];
            int dv = dist_b[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MT + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (mark_b[u] != stamp_b) {
                        mark_b[u] = stamp_b;
                        dist_b[u] = dv + 1;
                        queue_b[tail++] = u;
                    }
                }
            } else {
                const int *row = MT + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[INV[gv[t]]];
                    if (mark_b[u] != stamp_b) {
                        mark_b[u] = stamp_b;
                        dist_b[u] = dv + 1;
                        queue_b[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static int in_gv(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

static void random_gv(int *gv, int N) {
    gv[0] = 0;
    for (int t = 1; t < d; t++) {
        int v;
        do { v = rndint(N); } while (in_gv(gv, t, v));
        gv[t] = v;
    }
}

static long tabu_until[MAXH];

/* Tabu search over voltages. Each step samples NBR single-voltage moves and takes the best
 * non-tabu one. A replaced voltage is tabu for TENURE steps. Random restart after STALL
 * steps without improvement. Returns the best objective; best_gv holds its voltages. */
static long tabu_run(int N, int *best_gv, double until) {
    int gv[MAXD];
    random_gv(gv, N);
    long cur = eval_gv(gv);
    long best = cur;
    memcpy(best_gv, gv, sizeof(int) * d);
    for (int i = 0; i < N; i++) tabu_until[i] = 0;
    long it = 0, stall = 0;
    while (cur > 0) {
        if ((it & 3) == 0 && now() > until) break;
        it++;
        long bv = -1;
        int bt = -1, bvv = -1;
        for (int s = 0; s < NBR; s++) {
            int t = 1 + rndint(d - 1);
            int v = 0, tries = 0;
            do {
                v = rndint(N);
                tries++;
            } while ((in_gv(gv, d, v) || tabu_until[v] > it) && tries < 1000);
            if (in_gv(gv, d, v)) continue;
            int old = gv[t];
            gv[t] = v;
            long val = eval_gv(gv);
            gv[t] = old;
            if (bv < 0 || val < bv) { bv = val; bt = t; bvv = v; }
        }
        if (bt < 0) {
            random_gv(gv, N);
            cur = eval_gv(gv);
            continue;
        }
        int old = gv[bt];
        tabu_until[old] = it + TENURE;
        gv[bt] = bvv;
        cur = bv;
        if (cur < best) {
            best = cur;
            memcpy(best_gv, gv, sizeof(int) * d);
            stall = 0;
        } else if (++stall > STALL) {
            random_gv(gv, N);
            cur = eval_gv(gv);
            stall = 0;
        }
    }
    return best;
}

static void build_bc(Graph *g, int N, const int *gv) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MT[(size_t)x * N + gv[t]]);
}

static Graph bc_cand;

static void bicayley_phase(Graph *best, double until) {
    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXH) Nmax_l = MAXH;
    if (Nmax_l > MAXN / 2) Nmax_l = MAXN / 2;
    int Nmax = (int)Nmax_l;
    int Nlo = best->n / 2 + 1;
    if (Nlo < d + 1) Nlo = d + 1;
    static int gbest[MAXD];
    while (now() < until && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > SPAN) span = SPAN;
        double u = rnd01();
        int N = Nlo + (int)(u * u * span);
        if (N > Nmax) N = Nmax;
        int m, k, r;
        sample_group(N, &m, &k, &r);
        build_group(m, k, r);
        double left = until - now();
        double slice = left / 6.0;
        if (slice < 1.0) slice = 1.0;
        if (slice > left) slice = left;
        long b = tabu_run(N, gbest, now() + slice);
        if (b == 0) {
            build_bc(&bc_cand, N, gbest);
            if (bc_cand.n > best->n && is_valid(&bc_cand))
                copy_graph(best, &bc_cand);
            Nlo = N + 1;
        }
    }
}

/* ---------------- growth by one vertex pair ---------------- */

/* Wire new pair x (side 0), y (side 1) onto best by random edge subdivision swaps. */
static int wire_pair(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    int k = 0;
    for (long tries = 0; k < d - 1 && tries < 1000000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (b >= n || used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = stamp;
        used[b] = stamp;
        k++;
    }
    return k == d - 1;
}

/* Edge-swap annealing on the exact bad-pair count. Swaps keep degrees and bipartition. */
static int anneal_grow(Graph *work, double until) {
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tr = 0; tr < 30 && badv[v] == 0; tr++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (s == v || work->side[s] != work->side[v] || work->deg[s] == 0) continue;
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
        T *= 0.999;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static int grow_once(const Graph *best, Graph *work, double until) {
    if (best->n + 2 > moore_bound() || best->n + 2 > MAXN) return 0;
    if (!wire_pair(best, work)) return 0;
    return anneal_grow(work, until);
}

static void grow_phase(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 5.0 ? left : 5.0;
        if (grow_once(best, &work, now() + slice) && work.n > best->n)
            copy_graph(best, &work);
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
    double t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD - 1) {
        d = d < 1 ? 1 : d;
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    double L = t_end - t0;
    if (d >= 3 && D >= 2 && best.n < moore_bound()) {
        bicayley_phase(&best, t0 + L * 0.6);
        if (best.n < moore_bound()) grow_phase(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
