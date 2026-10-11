"""Bold variant: tabu best-of-K repair in C instead of annealing, for the D = 3 targets.

Python supplies the best known D = 3 start (projective plane when d-1 is a prime power, otherwise
the Araujo-Pardo and Lopez graph for q = d-2, or a plain PG(2,q) base). C then grows the graph by
two vertices at a time. Each insertion is repaired by tabu search: at every step one bad vertex is
chosen, K targeted degree-preserving swaps are generated, all are evaluated exactly, and the best
non-tabu swap is applied even if it is worse. A repair that stalls is abandoned and retried from a
fresh insertion. Spare degree is filled greedily, which never increases any distance.

Only D = 3 gets a real construction. Other D values start from K_{d,d} and rely on the C growth.
Every returned graph passes lib.is_valid, and K_{d,d} is the fallback. This version is untested
against the record targets.
"""
import itertools
import random
import time

import lib

TIME_FRAC = 0.90

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define KC 40
#define PATIENCE 1500
#define TT 8

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int v, u, s, t; } Move;

static int d, D;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------------- distances */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static uint64_t *fr;
static int fW;

/* Number of unordered pairs at distance > D. Sets badv and the reach balls. */
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
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    fr = cur;
    fW = W;
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

static int reached(int v, int w) {
    return (int)((fr[(size_t)v * fW + w / 64] >> (w % 64)) & 1ULL);
}

/* ---------------------------------------------------------------- graph basics */

static int has_edge(const Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) if (g->adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

static void del_half(Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++)
        if (g->adj[a][i] == b) { g->adj[a][i] = g->adj[a][--g->deg[a]]; return; }
}

static void del_edge(Graph *g, int a, int b) { del_half(g, a, b); del_half(g, b, a); }

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static int valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++) if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    static int q[MAXN];
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
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; q[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++) if (u < g->adj[u][i]) m++;
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

/* Add edges between sides while both ends have spare degree. Distances never grow. */
static void fill_spare(Graph *g) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] >= d) continue;
        if (g->side[v] == 0) A[na++] = v; else B[nb++] = v;
    }
    for (int it = 0; it < 20 * MAXN && na && nb; it++) {
        int i = rndint(na), j = rndint(nb);
        int a = A[i], b = B[j];
        if (has_edge(g, a, b)) continue;
        add_edge(g, a, b);
        if (g->deg[a] >= d) A[i] = A[--na];
        if (g->deg[b] >= d) B[j] = B[--nb];
    }
}

/* Copy best, add one vertex per side (x on side 0, y on side 1), rewire the spare
 * degree of up to d-1 edges through them. */
static void insert_pair(const Graph *best, Graph *dst) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(dst, best);
    int x = n, y = n + 1;
    dst->n = n + 2;
    dst->deg[x] = dst->deg[y] = 0;
    dst->side[x] = 0;
    dst->side[y] = 1;
    add_edge(dst, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (dst->side[a] != 0 || used[a] == stamp || dst->deg[a] == 0) continue;
        int b = dst->adj[a][rndint(dst->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(dst, a, b);
        add_edge(dst, x, b);
        add_edge(dst, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

/* ---------------------------------------------------------------- tabu repair */

/* Targeted swap for bad vertex v: an unreached partner w, a walk from w to t on the far
 * side, and s a neighbour of t on v's side. Move: (v,u),(s,t) -> (v,t),(s,u). */
static int make_move(const Graph *g, int v, Move *m) {
    if (g->deg[v] == 0) return 0;
    int w = -1;
    for (int tr = 0; tr < 64; tr++) {
        int c = rndint(g->n);
        if (c != v && !reached(v, c)) { w = c; break; }
    }
    if (w < 0) return 0;
    int L = g->side[w] == g->side[v] ? 1 : 2;
    int t = w;
    for (int k = 0; k < L; k++) {
        if (g->deg[t] == 0) return 0;
        t = g->adj[t][rndint(g->deg[t])];
    }
    if (g->deg[t] == 0) return 0;
    int s = g->adj[t][rndint(g->deg[t])];
    int u = g->adj[v][rndint(g->deg[v])];
    if (s == v || t == u || s == t) return 0;
    if (g->side[s] != g->side[v] || g->side[t] == g->side[v]) return 0;
    if (has_edge(g, v, t) || has_edge(g, s, u)) return 0;
    m->v = v; m->u = u; m->s = s; m->t = t;
    return 1;
}

static void apply_move(Graph *g, const Move *m) {
    del_edge(g, m->v, m->u);
    del_edge(g, m->s, m->t);
    add_edge(g, m->v, m->t);
    add_edge(g, m->s, m->u);
}

static void undo_move(Graph *g, const Move *m) {
    del_edge(g, m->v, m->t);
    del_edge(g, m->s, m->u);
    add_edge(g, m->v, m->u);
    add_edge(g, m->s, m->t);
}

/* Insert pairs and repair each by tabu search. Successful graphs replace best. */
static void grow(Graph *best, double until) {
    static Graph cur;
    static long tabu[MAXN];
    long moore = moore_bound();
    while (now() < until && best->n + 2 <= moore && best->n + 2 <= MAXN) {
        insert_pair(best, &cur);
        fill_spare(&cur);
        memset(tabu, 0, sizeof(tabu));
        long step = 0, minb = -1, since = 0;
        int ok = 0;
        while (now() < until) {
            long bb = bad_pairs(&cur);          /* sets badv and fr for cur */
            if (bb == 0) { ok = 1; break; }
            if (minb < 0 || bb < minb) { minb = bb; since = 0; }
            else if (++since > PATIENCE) break;
            step++;
            int v = -1;
            for (int tr = 0; tr < 50; tr++) {
                int c = rndint(cur.n);
                if (badv[c] > 0) { v = c; break; }
            }
            if (v < 0) continue;

            Move cs[KC];
            int nc = 0;
            for (int tr = 0; tr < 3 * KC && nc < KC; tr++)
                if (make_move(&cur, v, &cs[nc])) nc++;
            if (nc == 0) continue;

            long bestb = -1;
            int bi = -1;
            for (int j = 0; j < nc; j++) {
                apply_move(&cur, &cs[j]);
                long b2 = bad_pairs(&cur);      /* clobbers fr/badv; recomputed next step */
                undo_move(&cur, &cs[j]);
                int hit = tabu[cs[j].u] > step || tabu[cs[j].s] > step || tabu[cs[j].t] > step;
                if (hit && !(minb >= 0 && b2 < minb)) continue;
                if (bi < 0 || b2 < bestb || (b2 == bestb && rndint(2))) { bestb = b2; bi = j; }
            }
            if (bi < 0) continue;
            apply_move(&cur, &cs[bi]);
            long until_t = step + TT + rndint(4);
            tabu[cs[bi].v] = tabu[cs[bi].u] = until_t;
            tabu[cs[bi].s] = tabu[cs[bi].t] = until_t;
        }
        if (ok && valid(&cur)) copy_graph(best, &cur);
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
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD || D < 1) {
        if (d < 1 || d > MAXD) d = 1;
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!valid(&best)) complete_bipartite(&best);
    if (D >= 3 && best.n < moore_bound() && best.n < MAXN) {
        fill_spare(&best);
        if (!valid(&best)) complete_bipartite(&best);
        grow(&best, t_end);
    }
    if (!valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def known_start(d, D):
    """Best known D = 3 construction for d, or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)      # Moore graph, optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)              # record 2(q^2+q+5), q = d-2
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    fallback = lib.haar_graph(d, range(d))              # K_{d,d}: valid for D >= 2
    if D == 2:
        return fallback

    best = fallback
    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is None and D == 3 and d >= 3:
        try:
            start = _pg_base(d)
        except Exception:
            start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass
    return best
