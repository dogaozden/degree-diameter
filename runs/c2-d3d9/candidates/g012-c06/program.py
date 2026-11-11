"""Combined bi-Cayley / voltage-lift / grow-by-two search.

C side, in order:
  1. Bi-Cayley graphs over metacyclic groups Z_m x| Z_k of order N. Sweep N downward from
     the Moore limit (floor 0.4 * Moore). Each N gets an equal time share. Non-abelian
     groups are preferred and each connection set is hill-climbed on the number of
     vertices missed within distance D (two BFS runs, by vertex-transitivity).
  2. Voltage lifts over the same group tables, with hill-climbing on the voltages.
  3. Grow by two: add one vertex per side and anneal edge swaps until diameter <= D.
Python builds the start graph, runs C, and keeps the result only if lib.is_valid accepts it.
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

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define MAXD 32
#define MAXG 1024
#define MAXGRP 8192
#define MAXP 4

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

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
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

static void complete_bip(Graph *g, int k) {
    g->n = 2 * k;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k; }
    for (int a = 0; a < k; a++)
        for (int b = 0; b < k; b++) add_edge(g, a, k + b);
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Fills badv[v]. */
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

static int qbuf[MAXN];

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int v = qbuf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; qbuf[tail++] = u; }
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct { int m, k, r; } Grp;
static Grp grp[MAXGRP];
static int ngrp, nnonab;

/* Enumerate groups of order n; non-abelian (r != 1) first. */
static void enum_groups(int n) {
    ngrp = 0;
    nnonab = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1 && ngrp < MAXGRP) {
                    grp[ngrp].m = 1; grp[ngrp].k = k; grp[ngrp].r = 0;
                    ngrp++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (ngrp < MAXGRP) {
                    grp[ngrp].m = m; grp[ngrp].k = k; grp[ngrp].r = r;
                    ngrp++;
                    if (pass == 0) nnonab++;
                }
            }
        }
    }
}

static int MT[MAXG * MAXG]; /* multiplication table of the current group */
static int INV[MAXG];       /* inverses */

static void build_group(Grp G, int n) {
    static int rp[MAXG];
    if (n <= 0 || n > MAXG) return;
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------------------ bi-Cayley search */

static int cdist[2 * MAXG], cq[2 * MAXG];

/* Vertices missed within distance D from A_e plus from B_e. Zero iff diameter <= D. */
static long cayley_cost(const int *S, int n) {
    int V = 2 * n;
    long miss = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? n : 0;
        for (int v = 0; v < V; v++) cdist[v] = -1;
        int head = 0, tail = 0;
        cdist[s0] = 0;
        cq[tail++] = s0;
        while (head < tail) {
            int v = cq[head++];
            int dv = cdist[v];
            if (dv >= D) continue;
            if (v < n) {
                for (int i = 0; i < d; i++) {
                    int u = n + MT[v * n + S[i]];
                    if (cdist[u] < 0) { cdist[u] = dv + 1; cq[tail++] = u; }
                }
            } else {
                int h = v - n;
                for (int i = 0; i < d; i++) {
                    int u = MT[h * n + INV[S[i]]];
                    if (cdist[u] < 0) { cdist[u] = dv + 1; cq[tail++] = u; }
                }
            }
        }
        miss += V - tail;
    }
    return miss;
}

/* Random connection set S = {0, s_1..s_{d-1}}, then hill-climb on cayley_cost. */
static int climb(int n, int *S, int steps, double until) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1), dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
    long cur = cayley_cost(S, n);
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        int i = 1 + rndint(d - 1);
        int x;
        for (;;) {
            x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < d; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) break;
        }
        int old = S[i];
        S[i] = x;
        long c = cayley_cost(S, n);
        if (c <= cur || rnd01() < 0.01) cur = c;
        else S[i] = old;
    }
    return cur == 0;
}

static Graph cand_g;

static void build_cayley(Graph *g, int n, const int *S) {
    g->n = 2 * n;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= n; }
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, n + MT[x * n + S[i]]);
}

/* Sweep N downward; each N gets an equal share of the phase time. */
static void cayley_sweep(Graph *best, double until) {
    long moore = moore_bound();
    long nmax = moore / 2;
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    if (2 * nmax > MAXN) nmax = MAXN / 2;
    long nmin = best->n / 2 + 1;
    long lo = (long)(0.4 * (double)moore / 2.0);
    if (lo > nmin) nmin = lo;
    if (nmin < d + 1) nmin = d + 1;
    if (nmin > nmax) return;
    double total = until - now();
    if (total <= 0) return;
    double share = total / (double)(nmax - nmin + 1);
    if (share < 0.02) share = 0.02;
    int S[MAXD];
    for (long n = nmax; n >= nmin; n--) {
        double t = now();
        if (t >= until) break;
        double end = t + share;
        if (end > until) end = until;
        enum_groups((int)n);
        if (ngrp == 0) continue;
        while (now() < end) {
            int gi = (nnonab > 0 && rnd01() < 0.7) ? rndint(nnonab) : rndint(ngrp);
            build_group(grp[gi], (int)n);
            if (climb((int)n, S, 4000, end)) {
                build_cayley(&cand_g, (int)n, S);
                if (is_valid(&cand_g) && cand_g.n > best->n) copy_graph(best, &cand_g);
                return;
            }
        }
    }
}

/* ------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

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

static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + MT[x * N + dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Hill-climb on voltages of a random base graph; g ends as the lift of the final voltages. */
static int lift_try(Graph *g, int p, int N, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, dt, nd);
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until && fails < 2000) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        long N = (target + 2 * p - 1) / (2 * p) + rndint(3);
        if (N < d || N > MAXG - 1 || 2L * p * N > MAXN || 2L * p * N > moore) {
            fails++;
            continue;
        }
        enum_groups((int)N);
        if (ngrp == 0) { fails++; continue; }
        build_group(grp[rndint(ngrp)], (int)N);
        int steps = 300 + 200000 / (2 * p * (int)N);
        if (lift_try(&cand, p, (int)N, steps, until) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
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
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }

    read_start(&best);
    if (best.n == 0) complete_bip(&best, D >= 2 ? d : 1);

    if (d >= 2 && D >= 2 && best.n < moore_bound()) {
        double T = t_end - t0;
        cayley_sweep(&best, t0 + 0.55 * T);
        lift_search(&best, t0 + 0.72 * T);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bip(&best, D >= 2 ? d : 1);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    if start is None:
        start = lib.haar_graph(d, range(d))            # K_{d,d}: valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D) or d < 2 or D < 2 or d > 32:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
