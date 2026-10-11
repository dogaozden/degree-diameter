"""Combined program: Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez,
or K_{d,d}) and checks it with lib.is_valid. The C engine then climbs from that start.

New in this version: the C engine searches voltage lifts over a much wider family of groups
and base graphs. Groups are central products Z_z x (Z_m x|_r Z_k), so non-metacyclic groups
are included. Base graphs have up to 8 vertices per side, given as d random perfect matchings
(layers). Voltages are optimised by simulated annealing on an orbit-reduced diameter cost,
which needs only 2p BFS runs because the group acts regularly on each fibre. The lift is
evaluated implicitly, so no graph is rebuilt per step. Once lift search stops improving,
grow-by-two annealing uses the remaining time. Every output is checked and falls back safely."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Voltage lifts. Base: d layers, each a permutation of p A-fibres onto p B-fibres (p <= 8).
 *    Group: central product Z_z x (Z_m x|_r Z_k), order N. Voltages are annealed so that the
 *    orbit-reduced diameter cost (BFS from the 2p fibre representatives) reaches zero.
 * 2. Grow by two: insert one vertex per side and anneal degree-preserving edge swaps.
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
#define MAXP 8
#define MAXG 512

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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* ---------------------------------------------------------------- groups
 * Central product Z_z x (Z_m x|_r Z_k), order N = z*m*k.
 * Element index: c*(m*k) + a*k + b, with (a,b)(a',b') = (a + r^b a', b + b').
 */
typedef struct {
    int N, z, m, k, r;
    int rp[MAXG];
    int mul[MAXG * MAXG];
    int inv[MAXG];
} Grp;

static Grp GR;

static void set_group(int N, int z, int m, int k, int r) {
    GR.N = N; GR.z = z; GR.m = m; GR.k = k; GR.r = r;
    int mk = m * k;
    GR.rp[0] = 1 % m;
    for (int b = 1; b < k; b++) GR.rp[b] = (int)((long)GR.rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int c1 = x / mk, rem1 = x % mk, a1 = rem1 / k, b1 = rem1 % k;
        for (int y = 0; y < N; y++) {
            int c2 = y / mk, rem2 = y % mk, a2 = rem2 / k, b2 = rem2 % k;
            int c = (c1 + c2) % z;
            int a = (int)(((long)a1 + (long)GR.rp[b1] * a2) % m);
            int b = (b1 + b2) % k;
            GR.mul[x * N + y] = c * mk + a * k + b;
        }
    }
    for (int x = 0; x < N; x++) {
        GR.inv[x] = 0;
        for (int y = 0; y < N; y++)
            if (GR.mul[x * N + y] == 0) { GR.inv[x] = y; break; }
    }
}

/* Uniformly random group of order N among the central products listed above. */
static void random_group_set(int N) {
    long count = 0;
    int bz = 1, bm = 1, bk = N, br = 0;
    for (int z = 1; z <= N; z++) {
        if (N % z) continue;
        int M = N / z;
        for (int m = 1; m <= M; m++) {
            if (M % m) continue;
            int k = M / m;
            if (m == 1) {
                count++;
                if (rndint((int)count) == 0) { bz = z; bm = 1; bk = k; br = 0; }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                count++;
                if (rndint((int)count) == 0) { bz = z; bm = m; bk = k; br = r; }
            }
        }
    }
    set_group(N, bz, bm, bk, br);
}

/* ---------------------------------------------------------------- lifts
 * Layer l (0..d-1) is a permutation PERM[l] of the p A-fibres onto the p B-fibres.
 * Dart (l, i) carries voltage VG[l][i]: A-vertex (i,x) joins B-vertex (PERM[l][i], x*g).
 * Each vertex has exactly d neighbours. Darts from the same fibre i into the same target
 * fibre must carry distinct voltages, so no parallel edges occur.
 */
static int LP, LN;
static int PERM[MAXD][MAXP];
static int PINV[MAXD][MAXP];
static int VG[MAXD][MAXP];

static void random_base(int p) {
    LP = p;
    for (int l = 0; l < d; l++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            PERM[l][i] = perm[i];
            PINV[l][perm[i]] = i;
        }
    }
}

static int clashes(int l, int i, int g) {
    int j = PERM[l][i];
    for (int l2 = 0; l2 < d; l2++)
        if (l2 != l && PERM[l2][i] == j && VG[l2][i] == g) return 1;
    return 0;
}

static void random_voltages(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < LP; i++) VG[l][i] = -1;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < LP; i++) {
            int g;
            do { g = rndint(LN); } while (clashes(l, i, g));
            VG[l][i] = g;
        }
}

/* Orbit-reduced diameter cost. The group acts regularly on each fibre by left
 * multiplication, which is an automorphism of the lift. So it suffices to BFS from the
 * 2p fibre representatives (element 0). The cost is the number of (representative, vertex)
 * pairs at distance > D, and it is zero exactly when the lift has diameter <= D. */
static int vdist[MAXN], vmark[MAXN], vq[MAXN];
static int vstamp = 0;

static long orbit_cost(void) {
    int half = LP * LN;
    int NV = 2 * half;
    long total = 0;
    for (int b = 0; b < 2 * LP; b++) {
        int src = b * LN;
        int head = 0, tail = 0;
        vstamp++;
        vmark[src] = vstamp;
        vdist[src] = 0;
        vq[tail++] = src;
        while (head < tail) {
            int v = vq[head++];
            int dv = vdist[v];
            if (dv >= D) continue;
            if (v < half) {
                int i = v / LN, x = v % LN;
                for (int l = 0; l < d; l++) {
                    int u = (LP + PERM[l][i]) * LN + GR.mul[x * LN + VG[l][i]];
                    if (vmark[u] != vstamp) {
                        vmark[u] = vstamp;
                        vdist[u] = dv + 1;
                        vq[tail++] = u;
                    }
                }
            } else {
                int w = v - half;
                int j = w / LN, y = w % LN;
                for (int l = 0; l < d; l++) {
                    int i = PINV[l][j];
                    int u = i * LN + GR.mul[y * LN + GR.inv[VG[l][i]]];
                    if (vmark[u] != vstamp) {
                        vmark[u] = vstamp;
                        vdist[u] = dv + 1;
                        vq[tail++] = u;
                    }
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

static void build_explicit(Graph *g) {
    int half = LP * LN;
    g->n = 2 * half;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= half; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < LP; i++)
            for (int x = 0; x < LN; x++)
                add_edge(g, i * LN + x, (LP + PERM[l][i]) * LN + GR.mul[x * LN + VG[l][i]]);
}

/* Simulated annealing on the voltages. Returns 1 when the orbit cost reaches zero. */
static int anneal_lift(long steps, double until) {
    long cost = orbit_cost();
    if (cost == 0) return 1;
    for (long s = 0; s < steps; s++) {
        if ((s & 255) == 0 && now() > until) break;
        double T = 1.2 * (1.0 - (double)s / (double)steps) + 0.05;
        int l = rndint(d), i = rndint(LP);
        int g = rndint(LN);
        int old = VG[l][i];
        if (g == old || clashes(l, i, g)) continue;
        VG[l][i] = g;
        long nc = orbit_cost();
        long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) return 1;
        } else {
            VG[l][i] = old;
        }
    }
    return 0;
}

/* Search lifts of order 2pN strictly larger than the current best. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int p = 1 + rndint(MAXP);
        long target = (long)best->n + 2;
        if (target > moore) return;
        long Nmin = (target + 2L * p - 1) / (2L * p);
        long N = Nmin + rndint(3);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2L * p * N > MAXN || N > MAXG) continue;
        random_group_set((int)N);
        LN = (int)N;
        random_base(p);
        random_voltages();
        if (anneal_lift(15000, until)) {
            build_explicit(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
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
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
