"""Group-table bi-Cayley lift search with grow-by-two annealing.

The earlier engine searched semidirect voltage lifts. This version changes the construction.
Python passes a multiplication table for one finite group, chosen from several families:
the affine group AGL(1,q) (non-abelian), semidirect products Z_m x| Z_k, and cyclic groups.
C then searches for lifts of a base with kb vertices per side and d darts per base vertex.
Each dart (i, j, s) joins A_{i,g} to B_{j,g*s}. Left multiplication is an automorphism, so the
diameter is checked by 2*kb BFS runs from class representatives. Every candidate is re-checked
in C, and the best lift is grown by two vertices with annealing. Python keeps the best of the
known constructions and the search outputs, and checks every result with lib.is_valid.

Each group gets a slice of the time budget. Stdin for the C engine encodes the table as
"G G*G" followed by pairs (x*G+y, x*y), so no changes to lib are needed.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 16
#define MAXG 512
#define MAXK 3
#define MAXDART (MAXD * MAXK)
#define MAXW (MAXN / 64)
#define BIGCOST 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D, GG;
static double t_end;
static int MUL[MAXG][MAXG];

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

/* Reads "G M" then M lines "u v" with u = x*G+y and v = x*y. */
static int read_group(void) {
    int g, m;
    if (scanf("%d %d", &g, &m) != 2) return 0;
    if (g < 1 || g > MAXG || m != g * g) return 0;
    GG = g;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= g * g || v < 0 || v >= g) return 0;
        MUL[u / g][u % g] = v;
    }
    for (int x = 0; x < g; x++)
        if (MUL[0][x] != x || MUL[x][0] != x) return 0;
    return 1;
}

static int KB, ND;
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXG];
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GG; g++) DPERM[t][g] = MUL[g][DS[t]];
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GG;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GG; g++) {
            int a = DI[t] * GG + g;
            int b = (KB + DJ[t]) * GG + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GG;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GG;
        VST++;
        int head = 0, tail = 0;
        VIS[src] = VST;
        QU[tail++] = src;
        for (int depth = 0; depth < D; depth++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = QU[head++];
                for (int i = 0; i < LDEG[u]; i++) {
                    int v = LADJ[u][i];
                    if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void build_full(Graph *g) {
    int N = 2 * KB * GG;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GG; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GG; x++)
            add_edge(g, DI[t] * GG + x, (KB + DJ[t]) * GG + DPERM[t][x]);
}

static int lift_climb(int kb, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < kb; i++) {
            int t = l * kb + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(GG);
            set_dart_perm(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GG);
            if (nv == old) continue;
            DS[t] = nv;
            set_dart_perm(t);
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[t] = old; set_dart_perm(t); }
        } else {
            if (kb < 2) continue;
            int l = rndint(d);
            int i1 = rndint(kb), i2 = rndint(kb);
            if (i1 == i2) continue;
            int t1 = l * kb + i1, t2 = l * kb + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    if (cost != 0) return 0;
    build_full(out);
    return 1;
}

static void lift_search(Graph *best, double until, long mb) {
    static Graph cand;
    int fails = 0;
    while (now() < until && fails < 4000) {
        int kb = 1 + rndint(3);
        long N = 2L * kb * GG;
        if (N <= best->n || N > mb || N > MAXN) { fails++; continue; }
        long extra = (long)(fails / 50) * 2000;
        if (extra > 40000) extra = 40000;
        long steps = 3000 + rndint(6000) + extra;
        if (lift_climb(kb, steps, &cand) && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            fails = 0;
        } else {
            fails++;
        }
    }
}

static int grow_once(const Graph *best, Graph *work, double until, long mb) {
    int n = best->n;
    if (n + 2 > mb || n + 2 > MAXN) return 0;
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

static void grow_search(Graph *best, double until, long mb) {
    static Graph work;
    while (now() < until && best->n + 2 <= mb && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice, mb)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("2 1\n0 1\n"); return 0; }
    static Graph best;
    if (D < 2) { printf("2 1\n0 1\n"); return 0; }
    complete_bipartite(&best);
    if (!read_group()) { print_graph(&best); return 0; }

    long mb = moore_bound();
    lift_search(&best, t0 + (t_end - t0) * 0.6, mb);
    grow_search(&best, t_end, mb);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def _agl1(q):
    """Affine group AGL(1,q) = {x -> ax+b}, identity first; returns (name, order, mul)."""
    F = lib.GF(q)
    els = [(1, 0)] + [(a, b) for a in range(1, q) for b in range(q) if (a, b) != (1, 0)]
    idx = {e: i for i, e in enumerate(els)}

    def mul(x, y):
        a, b = els[x]
        c, e = els[y]
        return idx[(F.mul(a, c), F.add(F.mul(a, e), b))]

    return (f"AGL1({q})", len(els), mul)


def _cyclic(N):
    return (f"Z{N}", N, lambda x, y: (x + y) % N)


def _candidate_groups(seed, d, D):
    """Three groups of order 90..200 drawn from several families."""
    rng = random.Random(1000003 * seed + 97 * d + D)
    pool = [_agl1(11), _agl1(13)]
    sd = []
    for m in range(3, 201):
        for k in range(2, 201):
            if not 90 <= m * k <= 200:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    sd.append((m, k, r))
    rng.shuffle(sd)
    for m, k, r in sd[:8]:
        order, mul, _ = lib.semidirect_group(m, k, r)
        pool.append((f"SD({m},{k},{r})", order, mul))
    pool.append(_cyclic(rng.randint(90, 200)))
    rng.shuffle(pool)
    return pool[:3]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D) or d > 16:
        return best

    groups = _candidate_groups(seed, d, D)
    for gi, (name, order, mul) in enumerate(groups):
        left = 0.92 * time_limit - 1.5 - (time.monotonic() - t0)
        if left < 1.0:
            break
        b = left / (len(groups) - gi)
        pairs = [(x * order + y, mul(x, y)) for x in range(order) for y in range(order)]
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + gi, round(b, 2)],
                             stdin_graph=(order, pairs), timeout=b + 3)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass
    return best
