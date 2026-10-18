"""Group-table lifts plus grow-by-two, for the weakest target (d=4, D=7).

Change from the parent: the C engine no longer builds its own groups. Python builds explicit
finite groups as multiplication tables (PSL(2,q), PGL(2,q) as permutation closures, direct products
with Z_k, and semidirect products Z_m x| Z_k), and passes each table to C in mode 1. C searches
regular voltage lifts over that group (base 1 to 4 fibres per side, with orbit-reduced diameter
checks and iterated local search). Each lift is verified by the full all-pairs test. Mode 0 then
grows the best graph by two vertices per side with degree-preserving annealing.

Fallbacks: K_{d,d} and the known algebraic starts are always kept. Every C output is re-checked
with lib.is_valid before it replaces the current best, and any failure leaves the best valid
graph unchanged.
"""
import itertools
import math
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage: prog d D seed time_limit mode minn
 *   mode 0: stdin = start graph ("n m" + edges, or "0 0"). Grows it by two vertices per side.
 *   mode 1: stdin = group table "N N*N" followed by N*N lines "k value" (value = k-th entry of
 *           the table x*y, identity index 0). Searches regular lifts over the group for order > minn.
 * stdout: "n m" + edges, the largest valid graph found.
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
#define MAXG 1400
#define KICK_AFTER 800

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static int GN = 0;
static int *GT = NULL;
static long MINN = 0;

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

/* Number of unordered vertex pairs at distance > D (bitset BFS). */
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

/* Read the group table: "N M" with M = N*N, then M lines "k value". */
static int read_group(void) {
    int N, M;
    if (scanf("%d %d", &N, &M) != 2) return 0;
    if (N < 1 || N > MAXG || M != N * N) return 0;
    GT = malloc(sizeof(int) * (size_t)M);
    if (!GT) return 0;
    for (int k = 0; k < M; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= M || v < 0 || v >= N) return 0;
        GT[u] = v;
    }
    for (int y = 0; y < N; y++)
        if (GT[y] != y || GT[y * N] != y) return 0;
    GN = N;
    return 1;
}

/* ---------------------------------------------------------------- voltage lifts */
typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins (i, x) to (j, x*g). */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GT[x * N + dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* The group acts regularly by left multiplication, so it suffices to BFS from the identity of
 * each of the 2p fibres. Returns the number of (fibre, vertex) pairs at distance > D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int N = GN, nv = g->n;
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

/* Iterated local search over the voltages of one random base multigraph on p fibres. */
static int lift_ils(Graph *g, int p, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP], bestdt[MAXD * MAXP];
    int nd = 0, N = GN;
    if (N < d || (p > 1 && d < 2)) return 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, dt, nd);
    long bad = orbit_bad(g, p);
    long bestbad = bad;
    memcpy(bestdt, dt, sizeof(Dart) * nd);
    int stall = 0;
    for (int s = 0; s < steps && bestbad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, dt, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
        if (bad < bestbad) {
            bestbad = bad;
            memcpy(bestdt, dt, sizeof(Dart) * nd);
            stall = 0;
        } else {
            stall++;
        }
        if (stall > KICK_AFTER && bestbad > 0) {
            memcpy(dt, bestdt, sizeof(Dart) * nd);
            for (int k = 0; k < 2; k++) {
                int u = rndint(nd);
                dt[u].g = fresh_voltage(dt, nd, u, dt[u].i, dt[u].j, N);
            }
            build_lift(g, p, dt, nd);
            bad = orbit_bad(g, p);
            stall = 0;
        }
    }
    memcpy(dt, bestdt, sizeof(Dart) * nd);
    build_lift(g, p, dt, nd);
    return bestbad == 0;
}

/* Search lifts over the loaded group for orders above max(best, MINN). */
static void group_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        long cur = best->n > MINN ? best->n : MINN;
        int ps[MAXP], np = 0;
        for (int p = 1; p <= MAXP; p++) {
            long nv = 2L * p * GN;
            if (nv > cur && nv <= moore && nv <= MAXN) ps[np++] = p;
        }
        if (np == 0) return;
        int p = ps[rndint(np)];
        if (lift_ils(&cand, p, 6000, until) && cand.n > cur && is_valid(&cand))
            copy_graph(best, &cand);
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
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [mode minn] < input\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mode = argc > 5 ? atoi(argv[5]) : 0;
    MINN = argc > 6 ? atol(argv[6]) : 0;
    double t0 = now();
    double t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        if (d >= 1 && d <= MAXD) { complete_bipartite(&best); print_graph(&best); }
        else printf("0 0\n");
        return 0;
    }

    if (mode == 1) {
        if (D >= 2 && read_group()) group_search(&best, t_end);
        if (best.n == 0) complete_bipartite(&best);
        if (!is_valid(&best)) complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound()) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Several sign conventions are tried; a candidate is kept only if it passes lib.is_valid.
    Returns None if nothing verifies.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
    return out


# ---------------------------------------------------------------- explicit groups as tables
# A group table is (N, tab) with tab[x*N + y] = x*y and identity at index 0.

def _closure(gens, cap=1400):
    """Permutation group generated by gens (tuples); returns (elems, index) with identity first, or None."""
    m = len(gens[0])
    ident = tuple(range(m))
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(map(x.__getitem__, g))  # x composed with g
            if y not in index:
                if len(elems) >= cap:
                    return None
                index[y] = len(elems)
                elems.append(y)
    return elems, index


def _perm_table(elems, index):
    N = len(elems)
    tab = [0] * (N * N)
    for i, x in enumerate(elems):
        for j, y in enumerate(elems):
            tab[i * N + j] = index[tuple(map(x.__getitem__, y))]
    return N, tab


def _psl_gens(q, pgl=False):
    """Generators of PSL(2,q) (or PGL(2,q)) acting on the projective line {0..q-1, inf = q}."""
    F = lib.GF(q)
    inf = q

    def trans(a):
        return tuple(inf if x == inf else F.add(x, a) for x in range(q + 1))

    def scal(c):
        return tuple(inf if x == inf else F.mul(c, x) for x in range(q + 1))

    def invert():
        return tuple(inf if x == 0 else (0 if x == inf else F.neg(F.inv(x)))
                     for x in range(q + 1))

    gens = [trans(a) for a in range(1, q)]
    gens.append(invert())
    g = F.primitive_element()
    gens.append(scal(F.mul(g, g)))
    if pgl:
        gens.append(scal(g))
    return gens


def _psl(q):
    res = _closure(_psl_gens(q))
    return None if res is None else _perm_table(*res)


def _pgl(q):
    res = _closure(_psl_gens(q, pgl=True))
    return None if res is None else _perm_table(*res)


def _prod(base, k):
    """Direct product with Z_k: element g*k + c, (g,c)(h,e) = (gh, c+e)."""
    if base is None:
        return None
    N, tab = base
    M = N * k
    out = [0] * (M * M)
    for g in range(N):
        for c in range(k):
            row = (g * k + c) * M
            for h in range(N):
                th = tab[g * N + h] * k
                for e in range(k):
                    out[row + h * k + e] = th + (c + e) % k
    return M, out


def _semi(m, k, r):
    """Z_m x| Z_k with action r of order k."""
    M, mul, _ = lib.semidirect_group(m, k, r)
    out = [0] * (M * M)
    for x in range(M):
        for y in range(M):
            out[x * M + y] = mul(x, y)
    return M, out


def _semi_specs():
    out = []
    for m in range(5, 200):
        if any(m % s == 0 for s in range(2, math.isqrt(m) + 1)):
            continue
        for k in range(2, 10):
            N = m * k
            if (m - 1) % k or not (105 <= N <= 720):
                continue
            r = next((r for r in range(2, m)
                      if pow(r, k, m) == 1 and all(pow(r, j, m) != 1 for j in range(1, k))),
                     None)
            if r is not None:
                out.append((N, m, k, r))
    out.sort(key=lambda t: abs(t[0] - 480))
    return out[:4]


def _group_builders():
    specs = [
        ("PSL(2,8)", lambda: _psl(8)),
        ("PSL(2,7)xZ3", lambda: _prod(_psl(7), 3)),
        ("PGL(2,7)", lambda: _pgl(7)),
        ("PGL(2,7)xZ2", lambda: _prod(_pgl(7), 2)),
        ("PSL(2,7)xZ2", lambda: _prod(_psl(7), 2)),
        ("A6", lambda: _psl(9)),
        ("A6xZ2", lambda: _prod(_psl(9), 2)),
        ("PSL(2,11)", lambda: _psl(11)),
        ("A5xZ8", lambda: _prod(_psl(5), 8)),
        ("A5xZ7", lambda: _prod(_psl(5), 7)),
        ("S5xZ4", lambda: _prod(_pgl(5), 4)),
        ("A5xZ4", lambda: _prod(_psl(5), 4)),
    ]
    for N, m, k, r in _semi_specs():
        specs.append((f"Z{m}:Z{k}", lambda m=m, k=k, r=r: _semi(m, k, r)))
    return specs


# ---------------------------------------------------------------- driver

def _accept(best, out, d, D):
    """Return out if it is valid and strictly larger than best, else best."""
    try:
        n, e = out
        if n > best[0] and lib.is_valid(n, e, d, D):
            return (n, e)
    except Exception:
        pass
    return best


def _lift_phase(d, D, seed, best, until):
    builders = _group_builders()
    for gi, (name, make) in enumerate(builders):
        left = until - time.monotonic()
        if left < 1.0:
            break
        slice_t = max(1.0, left / (len(builders) - gi))
        try:
            tab = make()
        except Exception:
            continue
        if tab is None:
            continue
        N, table = tab
        if N < d:
            continue
        stdin = (N, [(k, table[k]) for k in range(N * N)])
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + gi, slice_t, 1, best[0]],
                             stdin_graph=stdin, timeout=slice_t + 8)
            best = _accept(best, lib.parse_graph_text(text), d, D)
        except Exception:
            pass
    return best


def _grow_phase(d, D, seed, best, until):
    left = until - time.monotonic()
    if left < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, left, 0, 0],
                         stdin_graph=best, timeout=left + 8)
        best = _accept(best, lib.parse_graph_text(text), d, D)
    except Exception:
        pass
    return best


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
        best = _accept(best, cand, d, D)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    deadline = t0 + 0.9 * time_limit - 2.0
    remaining = deadline - time.monotonic()
    if remaining < 1.0:
        return best

    try:
        best = _lift_phase(d, D, seed, best, time.monotonic() + 0.7 * remaining)
    except Exception:
        pass
    try:
        best = _grow_phase(d, D, seed, best, deadline)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
