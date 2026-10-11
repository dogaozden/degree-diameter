"""Combined bipartite degree-diameter search.

Python builds the strongest structured starts it can (projective planes, Araujo-Lopez,
conic blow-ups, arc-extended planes, generalized quadrangles), validates them, and passes the
best one to a C engine. The C engine alternates three moves, each of which keeps the graph valid:
  1. Twin duplication: copy a vertex with all neighbours of spare degree. Twins keep all distances.
  2. Set-cover augmentation: add one vertex joined to spare vertices that cover every existing
     vertex within distance D-1.
  3. Grow-by-two with annealing: insert an adjacent pair, steal degree-preserving edges, then
     anneal edge swaps until the diameter is at most D.
Small or missing starts also get a voltage-lift search over semidirect products Z_m x| Z_k.
Every returned graph is re-checked with lib.is_valid, and the valid fallback is kept.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
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
#define AUG_STREAK 300

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long MOORE;
static double t_end;
static Graph G, WK, CD, SAFE;

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

/* ------------------------------------------------------------ distance checks */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D; also fills badv[]. */
static long bad_pairs(const Graph *g) {
    int n = g->n, Wn = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * Wn);
    for (int v = 0; v < n; v++) cur[(size_t)v * Wn + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * Wn;
            const uint64_t *src = cur + (size_t)v * Wn;
            for (int w = 0; w < Wn; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * Wn;
                for (int w = 0; w < Wn; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * Wn;
        for (int w = 0; w < Wn; w++) c += __builtin_popcountll(s[w]);
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
            int back = 0;
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == v) back = 1;
            if (!back) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* ------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
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
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

/* ------------------------------------------------------------ groups and lifts */

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *gr, int x, int y) {
    int a = x / gr->k, b = x % gr->k, c = y / gr->k, e = y % gr->k;
    return (int)((a + (long)gr->rp[b] * c) % gr->m) * gr->k + (b + e) % gr->k;
}

static int random_group(int N, Grp *gr) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) {
                gr->m = m;
                gr->k = k;
                gr->r = r;
            }
        }
    }
    if (!count) return 0;
    gr->rp[0] = 1 % gr->m;
    for (int b = 1; b < gr->k; b++)
        gr->rp[b] = (int)((long)gr->rp[b - 1] * gr->r % gr->m);
    return 1;
}

typedef struct { int i, j, g; } Dart;

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
                if (linked) {
                    seen[u] = 1;
                    nseen++;
                    stack[top++] = u;
                }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void build_lift(Graph *g, int p, int N, const Grp *gr, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(gr, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int N, const Grp *gr, int steps) {
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
    build_lift(g, p, N, gr, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, gr, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Grp GR;
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > MOORE) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > MOORE || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &GR)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&CD, p, N, &GR, steps) && CD.n > best->n && is_valid(&CD))
            copy_graph(best, &CD);
    }
}

/* ------------------------------------------------------------ balls and set-cover augmentation */

static uint64_t ball[MAXN][MAXW];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp_ctr = 0;

static void ball_of(const Graph *g, int src, int r, uint64_t *bits) {
    int Wn = (g->n + 63) / 64;
    for (int i = 0; i < Wn; i++) bits[i] = 0;
    int head = 0, t = 0;
    stamp_ctr++;
    bq[t++] = src;
    mark[src] = stamp_ctr;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < g->deg[u]; k++) {
            int v = g->adj[u][k];
            if (mark[v] != stamp_ctr) {
                mark[v] = stamp_ctr;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(const Graph *g) {
    for (int v = 0; v < g->n; v++) ball_of(g, v, D - 1, ball[v]);
}

/* Add one vertex on side X joined to spare vertices that cover every vertex within D-1. */
static int try_add(Graph *g, int X) {
    uint64_t U[MAXW];
    int sel[MAXN];
    int T[MAXD];
    int nt = 0;
    int n = g->n;
    int Wn = (n + 63) / 64;
    if (n + 2 > MAXN) return 0;
    memset(sel, 0, sizeof(int) * (size_t)n);
    for (int i = 0; i < Wn; i++) U[i] = ~0ULL;
    if (n & 63) U[Wn - 1] = (1ULL << (n & 63)) - 1ULL;
    while (nt < d) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < n; v++) {
            if (g->side[v] == X || g->deg[v] >= d || sel[v]) continue;
            int gain = 0;
            for (int i = 0; i < Wn; i++) gain += __builtin_popcountll(ball[v][i] & U[i]);
            if (gain <= 0) continue;
            long sc = (long)gain * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < Wn; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < Wn; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = n;
    g->side[x] = (unsigned char)X;
    g->deg[x] = 0;
    g->n = n + 1;
    for (int k = 0; k < nt; k++) add_edge(g, x, T[k]);
    return 1;
}

/* Twin duplication: a copy of v with the same neighbours. Distances are preserved. */
static int twin_sweep(Graph *g) {
    int total = 0;
    for (int pass = 0; pass < 64; pass++) {
        int got = 0;
        int n0 = g->n;
        if (n0 == 0) break;
        int off = rndint(n0);
        for (int i = 0; i < n0; i++) {
            if (g->n + 1 > MOORE || g->n + 1 > MAXN - 1) return total + got;
            int v = (off + i) % n0;
            int dv = g->deg[v];
            if (dv == 0 || dv > d) continue;
            int ok = 1;
            for (int k = 0; k < dv && ok; k++)
                if (g->deg[g->adj[v][k]] >= d) ok = 0;
            if (!ok) continue;
            int t = g->n++;
            g->side[t] = g->side[v];
            g->deg[t] = dv;
            memcpy(g->adj[t], g->adj[v], sizeof(int) * dv);
            for (int k = 0; k < dv; k++) {
                int u = g->adj[v][k];
                g->adj[u][g->deg[u]++] = t;
            }
            got++;
        }
        total += got;
        if (!got) break;
    }
    return total;
}

/* Grow by two with degree-preserving steals, then anneal edge swaps until valid. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > MOORE || n + 2 > MAXN - 2) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = stamp;
    used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
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

/* ------------------------------------------------------------ main improvement loop */

static void improve(double until) {
    int dirty = 1, streak = 0;
    while (now() < until && G.n + 1 <= MOORE && G.n + 2 <= MAXN - 2) {
        if (twin_sweep(&G) > 0) {
            dirty = 1;
            continue;
        }
        if (streak < AUG_STREAK) {
            if (dirty) {
                recompute_balls(&G);
                dirty = 0;
            }
            if (try_add(&G, rndint(2))) {
                dirty = 1;
                streak = 0;
            } else {
                streak++;
            }
            continue;
        }
        double left = until - now();
        if (left <= 0.05) break;
        double slice = left / 4.0;
        if (slice > 6.0) slice = 6.0;
        if (slice < 0.5) slice = left;
        streak = 0;
        if (grow_once(&G, &WK, now() + slice)) {
            copy_graph(&G, &WK);
            dirty = 1;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    MOORE = moore_bound();
    read_start(&G);
    if (G.n == 0 || 2L * G.n < MOORE) {
        double share = G.n == 0 ? 0.5 : 0.35;
        lift_search(&G, t0 + (t_end - t0) * share);
    }
    if (G.n == 0) complete_bipartite(&G);
    if (!is_valid(&G)) complete_bipartite(&G);
    copy_graph(&SAFE, &G);
    improve(t_end);
    if (!is_valid(&G)) copy_graph(&G, &SAFE);
    print_graph(&G);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Always-valid small graph: K2 for D = 1 or d = 1, a cycle for d = 2, K_{d,d} otherwise."""
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    return lib.haar_graph(d, range(d))


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def _projective(d):
    """PG(2, d-1) incidence graph: Moore graph for D = 3 when d-1 is a prime power."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez record graph for d = q+2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def _conic_blowup(d, D):
    """Twin-style blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def _pg_data(q):
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Arc-extended PG(2,q) starts for each prime power q <= d-1 (diameter 3)."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


def _gq_w(q):
    """Incidence graph of the generalized quadrangle W(q) (diameter 4)."""
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


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the largest valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []

    fallback = _fallback(d, D)
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        return 1, []

    rng = random.Random(seed * 7919 + d)
    starts = [fallback]
    start_deadline = t0 + 0.12 * time_limit
    if D >= 3:
        starts += _try(_arc_extensions, d, start_deadline, rng) or []
        for g in (_try(_projective, d), _try(_araujo, d), _try(_conic_blowup, d, D)):
            if g:
                starts.append(g)
    if D >= 4 and time.monotonic() < start_deadline:
        g = _try(_best_gq, d)
        if g:
            starts.append(g)

    valid = [g for g in starts if g and lib.is_valid(g[0], g[1], d, D)]
    best = max(valid, key=lambda g: g[0])

    if d > 32 or d < 3 or D < 2:
        return best

    remaining = hard_end - time.monotonic() - 1.5
    if remaining < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                         stdin_graph=best, timeout=remaining + 15.0)
        n1, e1 = lib.parse_graph_text(text)
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
    except Exception:
        pass
    return best
