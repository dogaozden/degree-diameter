"""Bi-Cayley and lift search for bipartite degree-diameter graphs.

Phase 1 (C, bi-Cayley): for each order N, every semidirect product Z_m x|_r Z_k of order N is tried
with connection sets S (identity included, the rest enumerated exhaustively or sampled). The graph
A(x) ~ B(x*s) for s in S has order 2N and is d-regular. Left multiplication is an automorphism, so
validity only needs BFS from A(identity) and B(identity).

Phase 2 (C, lifts): random base multigraphs on p+p vertices (p = 2..4) lifted over random semidirect
groups, with hill-climbed voltages. Same orbit-reduced BFS.

Phase 3 (C, growth): insert two vertices and anneal degree-preserving swaps, then saturate.

Python builds the best algebraic start (K_{d,d}, PG(2,q), W(q), Araujo-Pardo-Lopez) and keeps it as
the fallback. Every output is checked with lib.is_valid.
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
#define MAXP 4
#define GMAX 512
#define MAXDART (MAXD * MAXP)
#define MAXGROUPS 1024
#define EXHAUST_LIMIT 400000.0

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

static int d, D;
static double t_end;
static Graph best, work_g, cand_g;

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

/* Number of unordered pairs at distance > D (bitset BFS). */
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

/* Adding an A-B edge between vertices with spare degree never increases a distance. */
static int saturate(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0 || g->deg[a] >= d) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
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

static void complete_bipartite(void) {
    best.n = 2 * d;
    for (int v = 0; v < best.n; v++) { best.deg[v] = 0; best.side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(&best, a, d + b);
}

/* ---------- groups Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e) ---------- */
static int GN;
static int MT[GMAX * GMAX];
static int GINV[GMAX];
static int RP[GMAX];

static void build_group(int m, int k, int r) {
    int N = m * k;
    GN = N;
    for (int b = 0; b < k; b++) RP[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)((a + (long)RP[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { GINV[x] = y; break; }
}

static int enum_groups(int N, int *GM, int *GK, int *GR, int cap) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < cap) { GM[cnt] = 1; GK[cnt] = k; GR[cnt] = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < cap) { GM[cnt] = m; GK[cnt] = k; GR[cnt] = r; cnt++; }
        }
    }
    return cnt;
}

/* ---------- lifts: p fibres per side, darts (i, j, g): A(i,x) ~ B(j, x*g) ---------- */
static Dart DT[MAXDART];
static int ND;
static int dist_[MAXN], qv[MAXN];

static long lift_bad(int p, int nd, int early) {
    int N = GN;
    int V = 2 * p * N;
    long bad = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            if (dist_[v] >= D) continue;
            int nx = dist_[v] + 1;
            if (v < p * N) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < nd; t++) {
                    if (DT[t].i != i) continue;
                    int u = (p + DT[t].j) * N + MT[x * N + DT[t].g];
                    if (dist_[u] < 0) { dist_[u] = nx; qv[tail++] = u; }
                }
            } else {
                int j = v / N - p, y = v % N;
                for (int t = 0; t < nd; t++) {
                    if (DT[t].j != j) continue;
                    int u = DT[t].i * N + MT[y * N + GINV[DT[t].g]];
                    if (dist_[u] < 0) { dist_[u] = nx; qv[tail++] = u; }
                }
            }
        }
        bad += V - tail;
        if (early && bad) return bad;
    }
    return bad;
}

static void build_from_darts(Graph *g, int p, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, DT[t].i * N + x, (p + DT[t].j) * N + MT[x * N + DT[t].g]);
}

static int fresh_g(int nd, int skip, int i, int j) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && DT[t].i == i && DT[t].j == j && DT[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Random d-regular base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* ---------- combinations for bi-Cayley connection sets ---------- */
static double binom_d(int n, int r) {
    double x = 1.0;
    for (int i = 1; i <= r; i++) x = x * (n - r + i) / i;
    return x;
}

/* c[0..r-1] increasing in [1..hi]; advance to next combination. */
static int next_comb(int *c, int r, int hi) {
    int i = r - 1;
    while (i >= 0 && c[i] == hi - (r - 1 - i)) i--;
    if (i < 0) return 0;
    c[i]++;
    for (int j = i + 1; j < r; j++) c[j] = c[j - 1] + 1;
    return 1;
}

static void random_set(int *c, int r, int hi) {
    for (int i = 0; i < r; i++) {
        for (;;) {
            int v = 1 + rndint(hi), dup = 0;
            for (int j = 0; j < i; j++)
                if (c[j] == v) { dup = 1; break; }
            if (!dup) { c[i] = v; break; }
        }
    }
}

/* Bi-Cayley graphs (p = 1): S = {identity} plus r = d-1 more elements of the group. */
static int try_bicayley(double until) {
    int r = d - 1, hi = GN - 1;
    if (r < 1 || r > hi) return 0;
    double combos = binom_d(hi, r);
    int exhaustive = combos <= EXHAUST_LIMIT;
    long iters = exhaustive ? (long)(combos + 0.5) : 400000L;
    int c[MAXD];
    if (exhaustive)
        for (int i = 0; i < r; i++) c[i] = i + 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 1023) == 0 && now() >= until) return 0;
        if (exhaustive) {
            if (it > 0 && !next_comb(c, r, hi)) break;
        } else {
            random_set(c, r, hi);
        }
        DT[0].i = 0; DT[0].j = 0; DT[0].g = 0;
        for (int i = 0; i < r; i++) {
            DT[i + 1].i = 0; DT[i + 1].j = 0; DT[i + 1].g = c[i];
        }
        if (lift_bad(1, d, 1) == 0) {
            build_from_darts(&cand_g, 1, d);
            if (is_valid(&cand_g)) {
                saturate(&cand_g);
                if (cand_g.n > best.n) copy_graph(&best, &cand_g);
                return 1;
            }
        }
    }
    return 0;
}

/* Stage 1: increasing N, exhaustive bi-Cayley search over all semidirect groups of order N. */
static void stage1(double until) {
    static int GM[MAXGROUPS], GK[MAXGROUPS], GR[MAXGROUPS];
    for (int N = best.n / 2 + 1; N <= GMAX; N++) {
        if (now() >= until) return;
        if (2L * N > moore_bound() || 2 * N > MAXN) return;
        int ng = enum_groups(N, GM, GK, GR, MAXGROUPS);
        for (int gi = 0; gi < ng && now() < until; gi++) {
            build_group(GM[gi], GK[gi], GR[gi]);
            if (try_bicayley(until)) break;
        }
    }
}

/* Stage 2: random lifts with p = 2..4 fibres, hill-climbed voltages. */
static void stage2(double until) {
    static int GM[MAXGROUPS], GK[MAXGROUPS], GR[MAXGROUPS];
    int M[MAXP][MAXP];
    while (now() < until) {
        if (best.n + 1L > moore_bound()) return;
        int p = 2 + rndint(3);
        long Nmin = (best.n + 1L + 2L * p - 1) / (2L * p);
        long Nl = Nmin + rndint(3);
        if (Nl < d) Nl = d;
        int N = (int)Nl;
        if (N > GMAX || 2L * p * N > moore_bound() || 2 * p * N > MAXN) continue;
        int ng = enum_groups(N, GM, GK, GR, MAXGROUPS);
        if (ng == 0) continue;
        int pick = rndint(ng);
        build_group(GM[pick], GK[pick], GR[pick]);
        make_base(p, M);
        ND = 0;
        for (int i = 0; i < p; i++)
            for (int j = 0; j < p; j++)
                for (int c = 0; c < M[i][j]; c++) {
                    DT[ND].i = i;
                    DT[ND].j = j;
                    DT[ND].g = c == 0 ? 0 : fresh_g(ND, -1, i, j);
                    ND++;
                }
        long bad = lift_bad(p, ND, 0);
        for (int s = 0; s < 20000 && bad > 0 && now() < until; s++) {
            int t = rndint(ND);
            int old = DT[t].g;
            DT[t].g = fresh_g(ND, t, DT[t].i, DT[t].j);
            long nb = lift_bad(p, ND, 0);
            if (nb <= bad || rnd01() < 0.02) bad = nb;
            else DT[t].g = old;
        }
        if (bad == 0) {
            build_from_darts(&cand_g, p, ND);
            if (is_valid(&cand_g)) {
                saturate(&cand_g);
                if (cand_g.n > best.n) copy_graph(&best, &cand_g);
            }
        }
    }
}

/* ---------- growth: add two vertices, anneal degree-preserving swaps ---------- */
static int grow_once(const Graph *base, Graph *work, double until) {
    int n = base->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, base);
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
    if (!is_valid(work)) return 0;
    saturate(work);
    return 1;
}

static void grow_search(Graph *base, double until) {
    while (now() < until && base->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(base, &work_g, now() + slice)) copy_graph(base, &work_g);
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        d = d < 1 ? 1 : d;
        complete_bipartite();
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (best.n > 0) {
        saturate(&best);
        if (!is_valid(&best)) best.n = 0;
    }
    if (best.n == 0) complete_bipartite();

    if (d >= 3 && D >= 2 && best.n < moore_bound()) {
        double span = t_end - t0;
        stage1(t0 + span * 0.55);
        stage2(t0 + span * 0.85);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite();
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
