"""Combined program, bold variant: lifts over ARBITRARY finite groups.

The parent only lifted over semidirect products Z_m x| Z_k. This version also lifts over a pool
of non-metacyclic and non-abelian groups (Heisenberg-type, SL(2,3), GL(2,3), S4, A4, dihedral
products, and direct products with cyclic groups). Groups are passed to C as multiplication
tables. Identity must be index 0, which lets the orbit-reduced BFS use fibre representatives.

Search schedule inside C:
- Interleaved slices of semidirect lifts (parent's family) and pool-group lifts, both aiming at
  a lift strictly larger than the current best.
- Each accepted lift is saturated, then grow-by-two annealing uses the remaining time.
Every candidate is checked by an exact is_valid, so a wrong table or lift can only be rejected.
If anything fails, the best algebraic start (or K_{d,d}) is returned.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, arbitrary-group lift version.
 * Usage:   prog d D seed time_limit   < stream
 * stream:  a graph-text-shaped stdin "1 m" followed by m pairs. The 2m integers after the header
 *          are one token stream:
 *            k, then k groups (N, then N*N table entries mul[x][y], identity = 0),
 *            then start_n, start_m, then start_m edges as 2*start_m integers (start_n = 0 for none).
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
#define MAXP 4
#define MAXG 128
#define NGP 176
#define SCR NGP

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

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

/* All-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* Adding an A-B edge between two vertices with spare degree never increases a distance. */
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

/* ---------------------------------------------------------------- input stream */

static unsigned char MT[NGP + 1][MAXG][MAXG];
static int GN[NGP + 1];
static int NP = 0;

static int *TOK = NULL;
static long NT = 0, TP = 0;

static int next_tok(int *out) {
    if (TP >= NT) return 0;
    *out = TOK[TP++];
    return 1;
}

static void read_stream(void) {
    int dummy = 0, m = 0;
    NT = 0;
    TP = 0;
    if (scanf("%d %d", &dummy, &m) != 2 || m < 0 || m > 2000000) return;
    TOK = (int *)malloc(sizeof(int) * (size_t)(2L * m + 2));
    if (!TOK) return;
    for (long t = 0; t < 2L * m; t++) {
        if (scanf("%d", &TOK[t]) != 1) break;
        NT = t + 1;
    }
}

static void load_pool(void) {
    int k = 0;
    NP = 0;
    if (!next_tok(&k) || k < 0 || k > NGP) return;
    for (int g = 0; g < k; g++) {
        int N = 0;
        if (!next_tok(&N) || N < 1 || N > MAXG) return;
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++) {
                int v = 0;
                if (!next_tok(&v) || v < 0 || v >= N) return;
                MT[g][x][y] = (unsigned char)v;
            }
        GN[g] = N;
        NP = g + 1;
    }
}

static void load_start(Graph *g) {
    int n = 0, m = 0;
    g->n = 0;
    if (!next_tok(&n) || !next_tok(&m) || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u = 0, v = 0;
        if (!next_tok(&u) || !next_tok(&v) || u < 0 || v < 0 || u >= n || v >= n ||
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

/* ---------------------------------------------------------------- groups */

/* Fill slot with a random semidirect product Z_m x|_r Z_k of order N (parent's family). */
static int semi_fill(int slot, int N) {
    int bm = 0, bk = 0, br = 0;
    long count = 0;
    if (N < 1 || N > MAXG) return 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    int rp[MAXG];
    rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) rp[b] = (int)((long)rp[b - 1] * br % bm);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int a = x / bk, b = x % bk, c = y / bk, e = y % bk;
            int v = (int)((a + (long)rp[b] * c) % bm) * bk + (b + e) % bk;
            MT[slot][x][y] = (unsigned char)v;
        }
    GN[slot] = N;
    return 1;
}

static int pick_pool(int lo, int hi) {
    int cnt = 0, pick = -1;
    for (int g = 0; g < NP; g++)
        if (GN[g] >= lo && GN[g] <= hi) {
            cnt++;
            if (rndint(cnt) == 0) pick = g;
        }
    return pick;
}

/* ---------------------------------------------------------------- lifts */

/* Make a random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element y -> p*N + j*N + y.
 * Dart (i, j, g) joins (i, x) to (j, x*g) for every x. Left multiplication is an automorphism. */
static void build_lift(Graph *g, int p, int N, int gi, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= p * N); }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + MT[gi][x][dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced objective: BFS from the 2p fibre representatives (element 0 = identity).
 * Returns the number of (representative, vertex) pairs at distance > D. */
static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Hill-climb the voltages of one random base multigraph over the group in slot gi. */
static int lift_fast_try(Graph *g, int p, int N, int gi, int steps, double until) {
    if (N < d || N > MAXG) return 0;
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
    build_lift(g, p, N, gi, dt, nd);
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, gi, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, gi, dt, nd);
    return bad == 0;
}

/* Semidirect-family lifts (parent's search), aiming strictly above the current best. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        long Nmin = (target + 2L * p - 1) / (2L * p);
        long Nl = Nmin + rndint(3);
        if (Nl < d) Nl = d;
        if (Nl > MAXG) continue;
        int N = (int)Nl;
        if (2L * p * N > moore || 2L * p * N > MAXN) continue;
        if (!semi_fill(SCR, N)) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_fast_try(&cand, p, N, SCR, 20000, until) && is_valid(&cand) &&
                cand.n > best->n) {
                saturate(&cand);
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* Lifts over the pool of arbitrary groups, aiming strictly above the current best. */
static void pool_lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    if (NP <= 0) return;
    while (now() < until) {
        long target = best->n + 2;
        if (target > moore) return;
        int p0 = rndint(4), pp = 1, gi = -1;
        for (int a = 0; a < 4 && gi < 0; a++) {
            pp = 1 + (p0 + a) % 4;
            long Nmin = (target + 2L * pp - 1) / (2L * pp);
            if (Nmin < d) Nmin = d;
            long Nmax = Nmin + 6;
            if (2L * pp * Nmax > moore) Nmax = moore / (2L * pp);
            if (Nmax < Nmin) continue;
            gi = pick_pool((int)Nmin, (int)Nmax);
            if (gi < 0) gi = pick_pool((int)Nmin, MAXG);
        }
        if (gi < 0) return;
        int N = GN[gi];
        if (2L * pp * N > moore || 2L * pp * N > MAXN) continue;
        if (lift_fast_try(&cand, pp, N, gi, 8000, until) && is_valid(&cand) &&
            cand.n > best->n) {
            saturate(&cand);
            copy_graph(best, &cand);
        }
    }
}

/* ---------------------------------------------------------------- growth */

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
    if (!is_valid(work)) return 0;
    saturate(work);
    return 1;
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
        fprintf(stderr, "usage: %s d D seed time_limit < stream\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_stream();
    load_pool();
    load_start(&best);
    if (best.n > 0) {
        saturate(&best);
        if (!is_valid(&best)) best.n = 0;
    }

    if (D >= 2 && best.n > 0 && best.n < moore_bound()) {
        double lift_end = t0 + (t_end - t0) * 0.85;
        while (now() < lift_end && best.n + 2 <= moore_bound()) {
            double before = now();
            double e1 = now() + 2.0;
            if (e1 > lift_end) e1 = lift_end;
            fast_lift_search(&best, e1);
            double e2 = now() + 2.0;
            if (e2 > lift_end) e2 = lift_end;
            pool_lift_search(&best, e2);
            if (now() - before < 0.002) break;
        }
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
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


# ---------------------------------------------------------------- finite groups as tables
# Each group is (N, table) with table[x][y] = x*y, identity index 0.

def _table(elems, mul):
    idx = {e: i for i, e in enumerate(elems)}
    return [[idx[mul(a, b)] for b in elems] for a in elems]


def _closure(gens, mul, ident, limit=128):
    elems, seen = [ident], {ident}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = mul(x, g)
            if y not in seen:
                if len(elems) >= limit:
                    return None
                seen.add(y)
                elems.append(y)
    return elems


def _group_from(gens, mul, ident):
    el = _closure(gens, mul, ident)
    if el is None:
        return None
    return len(el), _table(el, mul)


def _cyc(n):
    return n, [[(a + b) % n for b in range(n)] for a in range(n)]


def _dih(n):
    elems = [(r, s) for s in (0, 1) for r in range(n)]

    def mul(x, y):
        r1, s1 = x
        r2, s2 = y
        return ((r1 + (r2 if s1 == 0 else -r2)) % n, (s1 + s2) % 2)

    return len(elems), _table(elems, mul)


def _heis(m):
    elems = [(a, b, c) for a in range(m) for b in range(m) for c in range(m)]

    def mul(x, y):
        a, b, c = x
        a2, b2, c2 = y
        return ((a + a2) % m, (b + b2) % m, (c + c2 + a * b2) % m)

    return len(elems), _table(elems, mul)


def _mat_mul(p):
    def mul(X, Y):
        a, b, c, e = X
        f, g, h, k = Y
        return ((a * f + b * h) % p, (a * g + b * k) % p,
                (c * f + e * h) % p, (c * g + e * k) % p)
    return mul


def _sl23():
    return _group_from([(1, 1, 0, 1), (0, 2, 1, 0)], _mat_mul(3), (1, 0, 0, 1))


def _gl23():
    return _group_from([(1, 1, 0, 1), (0, 2, 1, 0), (2, 0, 0, 1)], _mat_mul(3), (1, 0, 0, 1))


def _perm_mul(X, Y):
    return tuple(X[j] for j in Y)


def _s4():
    return _group_from([(1, 0, 2, 3), (1, 2, 3, 0)], _perm_mul, (0, 1, 2, 3))


def _a4():
    return _group_from([(1, 2, 0, 3), (0, 2, 3, 1)], _perm_mul, (0, 1, 2, 3))


def _prod(A, B):
    n1, T1 = A
    n2, T2 = B
    n = n1 * n2
    T = [[0] * n for _ in range(n)]
    for x in range(n):
        a1, b1 = divmod(x, n2)
        row = T[x]
        for y in range(n):
            a2, b2 = divmod(y, n2)
            row[y] = T1[a1][a2] * n2 + T2[b1][b2]
    return n, T


def _pool(seed, lo=20, hi=100, cap=170):
    """Tables for a diverse set of groups with orders in [lo, hi] (at most 2 per order)."""
    rng = random.Random(seed)
    specs = {}

    def add(order, nonab, fn):
        if lo <= order <= hi:
            specs.setdefault(order, ([], []))[0 if nonab else 1].append(fn)

    for n in range(2, hi + 1):
        add(n, False, lambda n=n: _cyc(n))
    for n in range(3, hi // 2 + 1):
        add(2 * n, True, lambda n=n: _dih(n))
    base = [(27, lambda: _heis(3)), (64, lambda: _heis(4)), (24, _sl23),
            (48, _gl23), (24, _s4), (12, _a4)]
    for order, fn in base:
        add(order, True, fn)
        for k in range(2, hi // order + 1):
            add(order * k, True, lambda fn=fn, k=k: _prod(fn(), _cyc(k)))
    for n in range(3, 21):
        for k in range(2, 5):
            add(2 * n * k, True, lambda n=n, k=k: _prod(_dih(n), _cyc(k)))
    for a in range(2, 11):
        for b in range(a, 11):
            add(a * b, False, lambda a=a, b=b: _prod(_cyc(a), _cyc(b)))

    chosen = []
    for order in sorted(specs):
        nonab, ab = specs[order]
        rng.shuffle(nonab)
        rng.shuffle(ab)
        picks = nonab[:2]
        if len(picks) < 2 and ab:
            picks = picks + ab[:1]
        chosen.extend(picks)
    chosen = chosen[:cap]

    pool = []
    for fn in chosen:
        try:
            res = fn()
        except Exception:
            continue
        if res is not None and lo <= res[0] <= hi:
            pool.append(res)
    return pool


def _stream(pool, start):
    """Encode pool and start graph as the integer token stream read by the C program."""
    toks = [len(pool)]
    for N, T in pool:
        toks.append(N)
        for row in T:
            toks.extend(row)
    n0, e0 = start
    toks.append(n0)
    toks.append(len(e0))
    for u, v in e0:
        toks.append(u)
        toks.append(v)
    if len(toks) % 2:
        toks.append(0)
    pairs = [(toks[i], toks[i + 1]) for i in range(0, len(toks), 2)]
    return 1, pairs


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

    pool = []
    try:
        pool = _pool(seed)
    except Exception:
        pool = []

    budget = 0.87 * time_limit - (time.monotonic() - t0) - 1.2
    if budget <= 0.2:
        return best
    try:
        stream = _stream(pool, best)
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=stream, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
