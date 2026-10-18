"""Combined program: a C-native bi-Cayley lift annealer, then a C grow-by-two engine.

New idea in this version: the voltage-lift search over Z_m x| Z_k2 moves into C. Reachability is
kept as one 64-bit mask per vertex, with one bit per block representative. Lifts under left
translation are symmetric, so "every vertex reaches every representative within D" is exactly the
diameter condition. The annealer moves voltages (targeted at unreached vertices) and block
permutations, with a duplicate-edge penalty. Each evaluation is a few microseconds per vertex, so
it runs many more trials than the Python search. The best lift is handed to the grow phase.

Python builds the exact constructions (projective planes, Araujo-Pardo-Lopez, W(q)) and the
K_{d,d} fallback. Every returned graph is checked with lib.is_valid.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 8
#define LPEN 400

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

static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;

/* ---------------------------------------------------------------------------
 * Bi-Cayley lift annealer over Z_m x| Z_k2 (left-translation symmetric).
 * Vertices: A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h.
 * Layer l pairs A_i with B_{Lperm[l][i]} through voltage Lvol[l][i]:
 *   A_{i,g} ~ B_{j, g*s},  B_{j,h} ~ A_{i, h*s^{-1}}.
 * Reach: bit b of Lreach[v] is set when block-representative b (identity of block b)
 * is within distance D of v. Valid iff every vertex reaches all 2K representatives.
 * -------------------------------------------------------------------------*/
static int LK, LM, LK2, LG, Ld, LD;
static int Lpw[64];
static int Lperm[MAXD][MAXK];
static int Lvol[MAXD][MAXK];
static int Lnbr[MAXD][MAXN];
static uint64_t LBUF1[MAXN], LBUF2[MAXN], LCUR[MAXN];
static uint64_t *Lfinal;

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmodl(long a, long e, long m) {
    long r = 1 % m;
    a %= m;
    while (e > 0) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

static int gmul(int x, int y) {
    int a = x / LK2, b = x % LK2, c = y / LK2, e = y % LK2;
    long t = ((long)a + (long)Lpw[b] * c) % LM;
    return (int)(t * LK2 + (b + e) % LK2);
}

static int ginv(int x) {
    int a = x / LK2, b = x % LK2;
    int nb = (LK2 - b) % LK2;
    long c = ((long)LM - (long)Lpw[nb] * a % LM) % LM;
    return (int)(c * LK2 + nb);
}

static void setdart(int l, int i) {
    int j = Lperm[l][i], s = Lvol[l][i];
    int si = ginv(s);
    int Abase = i * LG, Bbase = (LK + j) * LG;
    for (int g = 0; g < LG; g++) {
        Lnbr[l][Abase + g] = Bbase + gmul(g, s);
        Lnbr[l][Bbase + g] = Abase + gmul(g, si);
    }
}

static long Ldup(void) {
    long dup = 0;
    for (int i = 0; i < LK; i++)
        for (int l = 0; l < Ld; l++)
            for (int l2 = l + 1; l2 < Ld; l2++)
                if (Lperm[l][i] == Lperm[l2][i] && Lvol[l][i] == Lvol[l2][i]) dup++;
    return dup;
}

/* Cost = unreached (vertex, representative) pairs + penalty for duplicate edges. */
static long Leval(void) {
    int N = 2 * LK * LG;
    uint64_t *cur = LBUF1, *nxt = LBUF2;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * LK; b++) cur[(size_t)b * LG] = 1ULL << b;
    for (int t = 0; t < LD; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t r = cur[v];
            for (int l = 0; l < Ld; l++) r |= cur[Lnbr[l][v]];
            nxt[v] = r;
            if (r != cur[v]) changed = 1;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long unreached = 0;
    int full = 2 * LK;
    for (int v = 0; v < N; v++) unreached += full - __builtin_popcountll(cur[v]);
    Lfinal = cur;
    return unreached + LPEN * Ldup();
}

static int lift_search(long iters, long patience, double deadline) {
    int N = 2 * LK * LG;
    uint64_t full = (1ULL << (2 * LK)) - 1;
    for (int l = 0; l < Ld; l++) {
        for (int i = 0; i < LK; i++) Lperm[l][i] = i;
        for (int i = LK - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int t = Lperm[l][i];
            Lperm[l][i] = Lperm[l][r];
            Lperm[l][r] = t;
        }
        for (int i = 0; i < LK; i++) {
            Lvol[l][i] = rndint(LG);
            setdart(l, i);
        }
    }
    long cost = Leval();
    memcpy(LCUR, Lfinal, sizeof(uint64_t) * (size_t)N);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > deadline) break;
        double T = 0.2 + 0.05 * c0 * (1.0 - (double)t / (double)iters);

        if (LK >= 2 && rnd01() < 0.25) {
            int l = rndint(Ld);
            int i1 = rndint(LK), i2 = rndint(LK - 1);
            if (i2 >= i1) i2++;
            int tmp = Lperm[l][i1]; Lperm[l][i1] = Lperm[l][i2]; Lperm[l][i2] = tmp;
            setdart(l, i1);
            setdart(l, i2);
            long c2 = Leval();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                memcpy(LCUR, Lfinal, sizeof(uint64_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = Lperm[l][i1]; Lperm[l][i1] = Lperm[l][i2]; Lperm[l][i2] = tmp;
                setdart(l, i1);
                setdart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1, targeted = 0;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tries = 0; tries < 30; tries++) {
                int w = rndint(N);
                if (LCUR[w] != full) { v = w; break; }
            }
            if (v >= 0) {
                int blk = v / LG;
                l = rndint(Ld);
                if (blk < LK) {
                    i = blk;
                } else {
                    int j = blk - LK;
                    for (int ii = 0; ii < LK; ii++)
                        if (Lperm[l][ii] == j) { i = ii; break; }
                    if (i < 0) continue;
                }
                targeted = 1;
            }
        }
        if (!targeted) { l = rndint(Ld); i = rndint(LK); }

        int old = Lvol[l][i];
        int nw = rndint(LG);
        if (nw == old) continue;
        Lvol[l][i] = nw;
        setdart(l, i);
        long c2 = Leval();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            memcpy(LCUR, Lfinal, sizeof(uint64_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            Lvol[l][i] = old;
            setdart(l, i);
        }
    }
    return cost == 0;
}

/* Pick Z_m x| Z_k2 with about `target` elements, and r of order dividing k2 mod m. */
static int sample_group(long target) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int attempt = 0; attempt < 200; attempt++) {
        int k2 = K2S[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long r = -1;
        if (k2 == 1) {
            r = 1;
        } else {
            if (k2 == 2 && m > 2 && rndint(10) < 3) {
                long c = m - 1;
                if (gcdl(c, m) == 1 && powmodl(c, 2, m) == 1 % m) r = c;
            }
            for (int tries = 0; r < 0 && tries < 60; tries++) {
                long c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcdl(c, m) == 1 && powmodl(c, k2, m) == 1 % m) r = c;
            }
            if (r < 0) continue;
        }
        LM = (int)m;
        LK2 = k2;
        LG = (int)(m * k2);
        for (int b = 0; b < k2; b++) Lpw[b] = (int)powmodl(r, b, m);
        return 1;
    }
    return 0;
}

static void lift_to_graph(void) {
    static Graph lg;
    int N = 2 * LK * LG;
    lg.n = N;
    for (int v = 0; v < N; v++) {
        lg.deg[v] = 0;
        lg.side[v] = (v < LK * LG) ? 0 : 1;
        for (int l = 0; l < Ld; l++) lg.adj[v][lg.deg[v]++] = Lnbr[l][v];
    }
    if (lg.n > gbest.n && is_valid(&lg)) copy_graph(&gbest, &lg);
}

/* Bandit over block counts K, with an order goal that ratchets up after successes. */
static void lift_phase(double deadline) {
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }
    double goal = (double)(gbest.n > 0 ? gbest.n : 2 * d) * 1.05;
    long mb = moore_bound();
    long lim = mb < MAXN ? mb : MAXN;
    while (now() < deadline) {
        int K = 1;
        if (rnd01() < 0.2) {
            K = 1 + rndint(5);
        } else {
            double bs = -1.0;
            for (int k = 1; k <= 5; k++) {
                double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; K = k; }
            }
        }
        long target = (long)(goal / (2.0 * K)) + rndint(3);
        if (target < 2) target = 2;
        LK = K;
        if (!sample_group(target)) { goal *= 0.99; continue; }
        long N = 2L * K * LG;
        if (N > lim) { goal *= 0.98; continue; }
        if (N <= gbest.n) {
            double g2 = gbest.n * 1.02;
            goal = goal > g2 ? goal : g2;
            continue;
        }
        trials[K]++;
        if (lift_search(6000, 1500, deadline)) {
            wins[K]++;
            lift_to_graph();
            double g2 = N * 1.04;
            goal = goal > g2 ? goal : g2;
        } else {
            double g1 = gbest.n * 1.02, g2 = goal * 0.99;
            goal = g1 > g2 ? g1 : g2;
        }
    }
}

/* ---------------------------------------------------------------------------
 * Grow-by-two: insert one vertex per side using spare degree, then anneal.
 * -------------------------------------------------------------------------*/
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
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_end = t0 + limit * 0.92 - 0.5;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    Ld = d;
    LD = D;
    read_start(&gbest);

    if (t_end - now() > 0.5) lift_phase(now() + 0.85 * (t_end - now()));
    if (gbest.n > 0) grow_search(t_end);

    if (gbest.n == 0 || !is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (Python).
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # C engine: native voltage-lift annealing, then grow-by-two from the best graph.
    budget = 0.9 * time_limit - 1.0
    remaining = t0 + budget - time.monotonic() - 1.0
    if remaining > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 15)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
