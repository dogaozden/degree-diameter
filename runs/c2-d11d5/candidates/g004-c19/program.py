"""Combined program: a C bi-Cayley lift annealer over semidirect groups Z_m x| Z_k2 (base size k),
then a C grow-by-two engine on the best graph found.

The lift annealer keeps every layer's neighbour table in sync incrementally, so one move costs
one pass of BFS per block representative. Each returned graph is checked with lib.is_valid,
and K_{d,d} is the fallback.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
/* Two modes, selected by argument count.
 *  grow mode:  prog d D seed time_limit           < start_graph
 *              grow-by-two from a valid start graph; never worse than the input.
 *  lift mode:  prog d D seed time_limit m k2 r k
 *              simulated annealing over bi-Cayley lifts of a base with k vertices per side,
 *              over the group Z_m x| Z_k2 (x)(a,b)*(c,e) = (a + r^b c, b + e), with r^k2 = 1 mod m.
 *              Vertex A_{i,g} = i*G+g, B_{j,h} = (k+j)*G+h, G = m*k2. Layer l matches A_i to
 *              B_{perm[l][i]} with voltage s: A_{i,g} ~ B_{p, g*s}. The group acts by left
 *              multiplication, so a graph is valid iff every block representative reaches all
 *              vertices within D. The cost counts unreached (representative, vertex) pairs
 *              plus a penalty for duplicate darts. The first zero-cost lift is printed.
 * Output: "n m" then the edges, or "0 0" if nothing was found.
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
#define MAXK 8
#define MAXK2 64

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

/* ------------------------------------------------------------------ grow mode */

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;
static double t_end;

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

static int graph_is_valid(const Graph *g) {
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
    if (!graph_is_valid(g)) g->n = 0;
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

/* One grow-by-two attempt from best; on success work holds n+2 valid vertices. */
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
    return graph_is_valid(work);
}

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
    }
}

/* ------------------------------------------------------------------ lift mode */

static int KK, GG, MM, K2, NN;
static int powr[MAXK2];                 /* powr[t] = r^t mod MM */
static int perm[MAXD][MAXK], pinv[MAXD][MAXK];
static int sh[MAXD][MAXK], shinv[MAXD][MAXK];
/* nbr[v][l] = neighbour of v in layer l. Slot l always belongs to layer l. */
static int nbr[MAXN][MAXD];
static int mark[MAXN], qbuf[MAXN];
static int mstamp = 0;

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Semidirect product: (a,b)*(c,e) = (a + r^b c, b + e), element coded a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int A = (int)(((long)a + (long)powr[b] * c) % MM);
    int B = (b + e) % K2;
    return A * K2 + B;
}

/* Inverse: (a,b)^-1 = (-r^(-b) a, -b). */
static inline int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int A = (int)(((long)(MM - powr[nb]) * a) % MM);
    return A * K2 + nb;
}

/* Recompute layer-l neighbours of A block i and of B block perm[l][i]. */
static void fix_slot(int l, int i) {
    int j = perm[l][i];
    int sv = sh[l][i], si = shinv[l][i];
    for (int g = 0; g < GG; g++) {
        nbr[i * GG + g][l] = (KK + j) * GG + gmul(g, sv);
        nbr[(KK + j) * GG + g][l] = i * GG + gmul(g, si);
    }
}

static void set_voltage(int l, int i, int val) {
    sh[l][i] = val;
    shinv[l][i] = ginv(val);
    fix_slot(l, i);
}

static void swap_perm(int l, int i1, int i2) {
    int t = perm[l][i1];
    perm[l][i1] = perm[l][i2];
    perm[l][i2] = t;
    pinv[l][perm[l][i1]] = i1;
    pinv[l][perm[l][i2]] = i2;
    fix_slot(l, i1);
    fix_slot(l, i2);
}

static void randomize_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KK; i++) perm[l][i] = i;
        for (int i = KK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < KK; i++) {
            pinv[l][perm[l][i]] = i;
            sh[l][i] = rndint(GG);
            shinv[l][i] = ginv(sh[l][i]);
            fix_slot(l, i);
        }
    }
}

/* Duplicate darts: two layers that give the same (partner, voltage) for the same A block. */
static long dupcount(void) {
    long dup = 0;
    for (int i = 0; i < KK; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (perm[l][i] == perm[l2][i] && sh[l][i] == sh[l2][i]) dup++;
    return dup;
}

/* Sum over block representatives of the number of vertices not reached within D, plus a
 * duplicate penalty. Zero exactly when the lift is simple and has diameter <= D. */
static long lift_cost(void) {
    long unreached = 0;
    for (int b = 0; b < 2 * KK; b++) {
        mstamp++;
        int head = 0, tail = 0, src = b * GG;
        mark[src] = mstamp;
        qbuf[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                for (int t = 0; t < d; t++) {
                    int u = nbr[v][t];
                    if (mark[u] != mstamp) {
                        mark[u] = mstamp;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        unreached += NN - tail;
    }
    return unreached + 60L * dupcount();
}

static void print_lift(void) {
    long m = (long)KK * GG * d;
    printf("%d %ld\n", NN, m);
    for (int v = 0; v < KK * GG; v++)
        for (int t = 0; t < d; t++) printf("%d %d\n", v, nbr[v][t]);
}

/* Annealing with time-based cooling windows and random restarts. Prints and returns 1 on success. */
static int run_lift(double until) {
    while (now() < until) {
        randomize_state();
        long cur = lift_cost();
        if (cur == 0) { print_lift(); return 1; }
        double start = now();
        double win = until - start;
        if (win > 10.0) win = 10.0;
        double T0 = 2.0 + 0.02 * (double)cur;
        const double T1 = 0.25;
        for (;;) {
            double el = now() - start;
            if (el >= win) break;
            double T = T0 * pow(T1 / T0, el / win);
            int l = rndint(d);
            if (KK >= 2 && rnd01() < 0.25) {
                int i1 = rndint(KK), i2 = rndint(KK - 1);
                if (i2 >= i1) i2++;
                swap_perm(l, i1, i2);
                long c2 = lift_cost();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else swap_perm(l, i1, i2);
            } else {
                int i = rndint(KK);
                int old = sh[l][i];
                int nv = rndint(GG);
                if (nv == old) continue;
                set_voltage(l, i, nv);
                long c2 = lift_cost();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else set_voltage(l, i, old);
            }
            if (cur == 0) { print_lift(); return 1; }
        }
    }
    return 0;
}

static int lift_entry(double t0, double limit, int m, int k2, int r, int k) {
    if (d < 2 || d > MAXD || D < 2 || k < 1 || k > MAXK || k2 < 1 || k2 > MAXK2 || m < 2)
        return 0;
    r %= m;
    if (r < 0) r += m;
    if (gcd_int(r, m) != 1) return 0;
    MM = m;
    K2 = k2;
    KK = k;
    GG = m * k2;
    NN = 2 * KK * GG;
    if (NN > MAXN) return 0;
    powr[0] = 1 % MM;
    for (int t = 1; t < K2; t++) powr[t] = (int)((long)powr[t - 1] * r % MM);
    if ((long)powr[K2 - 1] * r % MM != 1 % MM) return 0;   /* need r^k2 = 1 mod m */
    double until = t0 + limit * 0.92 - 0.1;
    return run_lift(until);
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [m k2 r k] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (argc >= 9) {
        int m = atoi(argv[5]), k2 = atoi(argv[6]), r = atoi(argv[7]), k = atoi(argv[8]);
        if (!lift_entry(t0, limit, m, k2, r, k)) printf("0 0\n");
        return 0;
    }

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    t_end = t0 + limit * 0.9 - 0.2;
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
    if (!graph_is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


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


# ----------------------------------------------------------------------------
# Group sampling for the semidirect lifts Z_m x| Z_k2.
# ----------------------------------------------------------------------------

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


_KS = (1, 2, 3, 4, 5, 6)
_MAX_LIFT_N = 8000


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

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
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

    # Phase 1: C lift annealer over semidirect groups, with a bandit over base sizes k.
    # Each call either returns a valid lift (which raises the goal) or uses its full slice
    # (which relaxes the goal back toward the current best).
    if D >= 3 and d >= 2:
        lift_deadline = t0 + 0.86 * total
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}
        goal = float(best_n) * 1.03

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        while True:
            remaining = lift_deadline - time.monotonic()
            if remaining < 1.5:
                break
            budget = min(remaining - 0.5, 6.0)
            k = pick_k()
            target = max(2, -(-int(goal) // (2 * k)) + rng.randrange(0, 3))
            g = _sample_group(target, rng)
            if g is None:
                goal = max(best_n * 1.01, goal * 0.99)
                continue
            m, k2, r = g
            N = 2 * k * m * k2
            if N <= best_n or N > _MAX_LIFT_N:
                goal = max(best_n * 1.01, goal * 0.99)
                continue
            trials[k] += 1
            seed_i = rng.randrange(1, 1 << 30)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed_i, round(budget, 2), m, k2, r, k],
                                 timeout=budget + 10)
                n_out, e_out = lib.parse_graph_text(text)
            except Exception:
                n_out, e_out = 0, []
            before = best_n
            if n_out > 0:
                consider(n_out, e_out)
            if best_n > before:
                wins[k] += 1
                goal = max(goal, best_n * 1.03)
            else:
                goal = max(best_n * 1.01, goal * 0.99)

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
