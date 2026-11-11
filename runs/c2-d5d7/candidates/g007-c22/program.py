"""Combined bi-Cayley lift + greedy grow search for degree-diameter bipartite graphs.

Pipeline (C engine, one run):
1. Bi-Cayley lift search. Vertices a_x and b_x (x in G, |G| = N, G = Z_m x|_r Z_k) with
   a_x ~ b_{x*g_t} for d distinct voltages g_0 = e. Left multiplication by G is an automorphism
   transitive on each side, so the diameter check is two BFS runs (from a_e and b_e). Voltages are
   hill-climbed. Orders N above the start's half-order are tried, and each success raises the bar.
2. Grow by two. Each step inserts one vertex pair, wired by greedy endpoint-coverage swaps (best of
   several samples), then degree-preserving edge swaps anneal to diameter D. Bad pairs are counted
   by bitset BFS.

Python builds the algebraic starts (hexagon incidence, projective plane, W(q), Araujo-Lopez), keeps
the largest that passes lib.is_valid, and hands it to C. The C output is validated again before use.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Combined bi-Cayley lift search + greedy grow search for bipartite degree-diameter graphs.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXH 2048
#define MAXCAND 512
#define STEPS 8000
#define SPAN 40
#define INIT_TRIALS 6
#define GREEDY_CAND 24

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

/* Number of unordered vertex pairs at distance > D (bitset BFS). Fills badv. */
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

/* ---------------- bi-Cayley lift search over Z_m x|_r Z_k ---------------- */

typedef struct { int m, k, r; } Grp;

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int RP[MAXH];
static int NN;

static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static Grp pick_group(const Grp *c, int cnt) {
    for (int tries = 0; tries < 8; tries++) {
        Grp g = c[rndint(cnt)];
        if (g.m > 1 && g.r != 1) return g;
    }
    return c[rndint(cnt)];
}

static void setup_group(int N, Grp G) {
    NN = N;
    int m = G.m, k = G.k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

static int dist_[2 * MAXH], seen_[2 * MAXH], q_[2 * MAXH];
static int stamp_ = 0;

/* Pairs (source, vertex) at distance > D for sources a_e and b_e. */
static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MTAB + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                const int *row = MTAB + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static long climb(int *gv, double until) {
    long bad = eval_bad(gv);
    double T = 2.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(NN); } while (used_upto(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[t] = old;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

/* Try bi-Cayley lifts of order 2N > best->n. Replaces best on success. */
static void lift_search(Graph *best, double until) {
    static Grp cand[MAXCAND];
    static Grp G;
    static int gv[MAXD];
    static Graph lg;
    long moore = moore_bound();
    long Nlo_l = best->n / 2 + 1;
    if (Nlo_l < d + 1) Nlo_l = d + 1;
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXH) Nmax_l = MAXH;
    int Nlo = (int)Nlo_l, Nmax = (int)Nmax_l;
    while (now() < until && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > SPAN) span = SPAN;
        int N = Nlo + rndint(span);
        int cnt = enum_groups(N, cand);
        if (cnt <= 0) continue;
        G = pick_group(cand, cnt);
        setup_group(N, G);
        gv[0] = 0;
        for (int t = 1; t < d; t++) {
            do { gv[t] = rndint(N); } while (used_upto(gv, t, gv[t]));
        }
        long bad = climb(gv, until);
        if (bad != 0) continue;
        lg.n = 2 * N;
        for (int v = 0; v < lg.n; v++) { lg.deg[v] = 0; lg.side[v] = v >= N; }
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++)
                add_edge(&lg, x, N + MTAB[(size_t)x * N + gv[t]]);
        if (lg.n > best->n && is_valid(&lg)) copy_graph(best, &lg);
        Nlo = N + 1;
    }
}

/* ---------------- greedy grow by one vertex pair ---------------- */

static void wire_pair(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
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
}

static int bq_dist[MAXN], bq_queue[MAXN], bq_mark[MAXN];
static int bq_stamp = 0;

static int ball_size(const Graph *g, int src) {
    int head = 0, tail = 0;
    bq_stamp++;
    bq_mark[src] = bq_stamp;
    bq_dist[src] = 0;
    bq_queue[tail++] = src;
    while (head < tail) {
        int v = bq_queue[head++];
        if (bq_dist[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (bq_mark[u] != bq_stamp) {
                bq_mark[u] = bq_stamp;
                bq_dist[u] = bq_dist[v] + 1;
                bq_queue[tail++] = u;
            }
        }
    }
    return tail;
}

static int wire_greedy(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0; k < d - 1; k++) {
        int ba = -1, bb = -1;
        long bscore = -1;
        int got = 0;
        for (int att = 0; got < GREEDY_CAND && att < 4000; att++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            got++;
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            long score = (long)(work->n - ball_size(work, x)) +
                         (long)(work->n - ball_size(work, y)) +
                         (long)(work->n - ball_size(work, a)) +
                         (long)(work->n - ball_size(work, b));
            del_edge(work, x, b);
            del_edge(work, y, a);
            add_edge(work, a, b);
            if (bscore < 0 || score < bscore) { bscore = score; ba = a; bb = b; }
        }
        if (ba < 0) return 0;
        del_edge(work, ba, bb);
        add_edge(work, x, bb);
        add_edge(work, y, ba);
        used[ba] = used[bb] = stamp;
    }
    return 1;
}

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    static Graph trial;
    long bestbad = -1;
    for (int t = 0; t < INIT_TRIALS; t++) {
        if (!wire_greedy(best, &trial)) wire_pair(best, &trial);
        long b = bad_pairs(&trial);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &trial);
        }
        if (bestbad == 0 || now() > until) break;
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
    t_end = t0 + limit * 0.95;
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

    if (d >= 3 && D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.6);
    }
    if (best.n + 2 <= moore_bound()) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


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
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
