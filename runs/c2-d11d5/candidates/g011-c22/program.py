"""Combined program: a compiled bi-Cayley lift annealer, then a C grow-by-two engine.

New in this version: the bi-Cayley voltage search runs in C (mode "L"). Each dart change
rewrites only the 2G adjacency slots it touches. Reachability is tracked with one byte per
vertex, a mask of the 2k block representatives within distance D. Because the lift is
invariant under left multiplication by the group, that check is exact.

Every returned graph is checked with lib.is_valid. K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Two modes, selected by argv[1]:
 *   L: bi-Cayley lift annealer.
 *      prog L d D seed time_limit k m k2 r
 *      Lift over Z_m x| Z_k2 (element a*k2+b, r^k2 = 1 mod m) with k blocks per side.
 *      Prints the lifted graph ("n m" + edges) or "0 0".
 *   G: grow-by-two search from the graph on stdin.
 *      prog G d D seed time_limit < start_graph
 *      Prints the best valid graph found, never worse than the input.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------------ bi-Cayley lift (mode L) */

static int LDEG, LDIA, LK, LM, LK2, LG, LN;
static long *LPW;          /* LPW[b] = r^b mod m */
static int *Ladj;          /* LN * LDEG: neighbour of vertex v in layer slot l */
static int *Llay;          /* LDEG * LK: partner B-block of A-block i in layer l */
static int *Lvol;          /* LDEG * LK: voltage of dart (l, i) */
static unsigned int *Lmark;
static unsigned int Lstamp = 0;
static uint8_t *Lcur, *Lnxt;
static uint8_t LPOP[256];

/* Group multiplication in Z_m x| Z_k2: (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / LK2, b = x % LK2, c = y / LK2, e = y % LK2;
    long t = ((long)a + LPW[b] * (long)c) % LM;
    return (int)(t * LK2 + (b + e) % LK2);
}

/* Dart (l, i, p, s): A(i,g) ~ B(p, g*s) for all g. Sets both directions in slot l. */
static void set_dart(int l, int i, int p, int s) {
    for (int g = 0; g < LG; g++) {
        int u = i * LG + g;
        int w = (LK + p) * LG + gmul(g, s);
        Ladj[(size_t)u * LDEG + l] = w;
        Ladj[(size_t)w * LDEG + l] = u;
    }
}

/* Number of repeated (i, p, s) triples, which would create multi-edges. */
static long dupcount(void) {
    Lstamp++;
    if (Lstamp == 0) {
        memset(Lmark, 0, sizeof(unsigned int) * (size_t)LK * LK * LG);
        Lstamp = 1;
    }
    long dups = 0;
    for (int l = 0; l < LDEG; l++)
        for (int i = 0; i < LK; i++) {
            size_t key = ((size_t)i * LK + Llay[l * LK + i]) * LG + Lvol[l * LK + i];
            if (Lmark[key] == Lstamp) dups++;
            else Lmark[key] = Lstamp;
        }
    return dups;
}

/* Cost = missing (vertex, representative) pairs + penalty for duplicates. Zero iff valid. */
static long lift_cost(void) {
    int N = LN;
    for (int v = 0; v < N; v++)
        Lcur[v] = (v % LG == 0) ? (uint8_t)(1u << (v / LG)) : 0;
    for (int r = 0; r < LDIA; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = Lcur[v];
            const int *a = Ladj + (size_t)v * LDEG;
            for (int l = 0; l < LDEG; l++) x |= Lcur[a[l]];
            Lnxt[v] = x;
            changed |= (x != Lcur[v]);
        }
        uint8_t *t = Lcur;
        Lcur = Lnxt;
        Lnxt = t;
        if (!changed) break;
    }
    long miss = 0;
    for (int v = 0; v < N; v++) miss += 2 * LK - LPOP[Lcur[v]];
    return miss + 1000L * dupcount();
}

static void lift_init(void) {
    int tmp[8];
    for (int l = 0; l < LDEG; l++) {
        for (int i = 0; i < LK; i++) tmp[i] = i;
        for (int i = LK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = tmp[i];
            tmp[i] = tmp[j];
            tmp[j] = t;
        }
        for (int i = 0; i < LK; i++) {
            Llay[l * LK + i] = tmp[i];
            Lvol[l * LK + i] = rndint(LG);
        }
    }
    for (int l = 0; l < LDEG; l++)
        for (int i = 0; i < LK; i++)
            set_dart(l, i, Llay[l * LK + i], Lvol[l * LK + i]);
}

/* Simulated annealing with stagnation restarts. Returns 1 when the state is a valid lift. */
static int lift_solve(double until) {
    const long patience = 6000;
    long it = 0;
    for (;;) {
        if (now() > until) return 0;
        lift_init();
        long cost = lift_cost();
        if (cost == 0) return 1;
        double T = 1.0 + 0.02 * (double)cost;
        long best = cost, last_imp = it;
        for (;;) {
            it++;
            if ((it & 63) == 0 && now() > until) return 0;
            if (it - last_imp > patience) break;
            T *= 0.9997;
            if (T < 0.3) T = 0.3;

            if (LK >= 2 && rnd01() < 0.25) {
                /* Swap the partners of two A-blocks inside one layer. */
                int l = rndint(LDEG);
                int i1 = rndint(LK), i2 = rndint(LK - 1);
                if (i2 >= i1) i2++;
                int *lay = Llay + (size_t)l * LK;
                int *vol = Lvol + (size_t)l * LK;
                int tmp = lay[i1];
                lay[i1] = lay[i2];
                lay[i2] = tmp;
                set_dart(l, i1, lay[i1], vol[i1]);
                set_dart(l, i2, lay[i2], vol[i2]);
                long c2 = lift_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = lay[i1];
                    lay[i1] = lay[i2];
                    lay[i2] = tmp;
                    set_dart(l, i1, lay[i1], vol[i1]);
                    set_dart(l, i2, lay[i2], vol[i2]);
                    continue;
                }
            } else {
                /* Change one voltage. */
                int l = rndint(LDEG), i = rndint(LK);
                int *lay = Llay + (size_t)l * LK;
                int *vol = Lvol + (size_t)l * LK;
                int old = vol[i];
                int nw = rndint(LG);
                if (nw == old) continue;
                vol[i] = nw;
                set_dart(l, i, lay[i], nw);
                long c2 = lift_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    vol[i] = old;
                    set_dart(l, i, lay[i], old);
                    continue;
                }
            }
            if (cost < best) {
                best = cost;
                last_imp = it;
            }
            if (cost == 0) return 1;
        }
    }
}

static void print_lift(void) {
    long m = (long)LK * LG * LDEG;
    printf("%d %ld\n", LN, m);
    for (int u = 0; u < LK * LG; u++)
        for (int l = 0; l < LDEG; l++)
            printf("%d %d\n", u, Ladj[(size_t)u * LDEG + l]);
}

static int lift_main(double t0, double limit, int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    LDEG = d;
    LDIA = D;
    LK = atoi(argv[6]);
    LM = atoi(argv[7]);
    LK2 = atoi(argv[8]);
    long R = atol(argv[9]);
    if (LDEG < 1 || LDEG > MAXD || LDIA < 1 || LK < 1 || LK > 4 || LM < 2 || LK2 < 1) {
        printf("0 0\n");
        return 0;
    }
    LG = LM * LK2;
    LN = 2 * LK * LG;
    if (LG < 2 || LN > MAXN) {
        printf("0 0\n");
        return 0;
    }
    R = ((R % LM) + LM) % LM;
    LPW = malloc(sizeof(long) * (size_t)LK2);
    long p = 1 % LM;
    for (int b = 0; b < LK2; b++) {
        LPW[b] = p;
        p = p * R % LM;
    }
    if (p != 1 % LM) {
        printf("0 0\n");
        return 0;
    }
    Ladj = malloc(sizeof(int) * (size_t)LN * LDEG);
    Llay = malloc(sizeof(int) * (size_t)LDEG * LK);
    Lvol = malloc(sizeof(int) * (size_t)LDEG * LK);
    Lmark = calloc((size_t)LK * LK * LG, sizeof(unsigned int));
    Lcur = malloc((size_t)LN);
    Lnxt = malloc((size_t)LN);
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        LPOP[x] = (uint8_t)c;
    }
    double t_end = t0 + limit * 0.92 - 0.1;
    if (lift_solve(t_end)) print_lift();
    else printf("0 0\n");
    return 0;
}

/* ------------------------------------------------------------------ grow-by-two (mode G) */

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

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
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
                    g->side[u] = 1 - g->side[v];
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

static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;

/* One grow-by-two attempt from best. On success work holds n+2 valid vertices. */
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

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s mode d D seed time_limit [k m k2 r]\n", argv[0]);
        return 2;
    }
    char mode = argv[1][0];
    d = atoi(argv[2]);
    D = atoi(argv[3]);
    long seed = atol(argv[4]);
    double limit = atof(argv[5]);
    double t0 = now();
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (mode == 'L') {
        if (d < 1 || d > MAXD) {
            printf("0 0\n");
            return 0;
        }
        return lift_main(t0, limit, argc, argv);
    }

    if (d < 1 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&gbest);
    if (gbest.n == 0) {
        printf("0 0\n");
        return 0;
    }
    grow_search(t0 + limit * 0.9 - 0.2);
    if (!is_valid(&gbest)) {
        printf("0 0\n");
        return 0;
    }
    print_graph(&gbest);
    return 0;
}
'''


_KS = (1, 2, 3, 4)
_LIFT_SLICE = 2.5   # seconds per group tried by the C lift annealer


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Phase 1: compiled bi-Cayley lift search. Each call tries one group for a short slice.
    # A bandit picks the block count k, and the order goal ratchets up after successes.
    lift_frac = 0.6 if best_n > 3000 else 0.75
    lift_deadline = t0 + lift_frac * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05
    lift_no = 0

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining_lift = lift_deadline - time.monotonic()
        if remaining_lift < 0.5:
            break
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        slice_t = min(_LIFT_SLICE, remaining_lift)
        trials[k] += 1
        lift_no += 1
        res = None
        try:
            text = lib.run_c(C_SOURCE, ["L", d, D, seed * 7919 + lift_no, round(slice_t, 2),
                                        k, m, k2, r],
                             timeout=slice_t + 10)
            res = lib.parse_graph_text(text)
        except Exception:
            res = None
        if res is not None and res[0] > best_n:
            before = best_n
            consider(res[0], res[1])
            if best_n > before:
                wins[k] += 1
                goal = max(goal, best_n * 1.04)
                continue
        goal = max(float(best_n) * 1.02, goal * 0.99)

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, ["G", d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
