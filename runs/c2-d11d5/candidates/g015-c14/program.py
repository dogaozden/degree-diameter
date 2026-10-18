"""Bi-Cayley voltage-lift search in C (bold change: C-speed annealing over a wider group family,
direct products and semidirect products, with base sizes k up to 6), followed by a C grow-by-two
phase on the best graph. Every returned graph is checked with lib.is_valid; K_{d,d} (or an exact
construction) is the fallback.
"""
import itertools
import math
import random
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
#define MAXK 16
#define CANDS 6
#define LPEN 1000

/* ------------------------------------------------------------------ common */

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

static void seed_rng(long seed) {
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
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

/* ------------------------------------------------------- grow-by-two (mode 1) */

static double t_end;
static Graph gbest, gwork, gtry;
static int used[MAXN];
static int stamp = 0;

static void make_candidate(const Graph *best, Graph *w) {
    int n = best->n;
    copy_graph(w, best);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

static void choose_candidate(const Graph *best, Graph *work) {
    long bestbad = -1;
    for (int c = 0; c < CANDS; c++) {
        make_candidate(best, &gtry);
        long b = bad_pairs(&gtry);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &gtry);
        }
        if (b == 0) break;
    }
}

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    choose_candidate(best, work);
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

/* ------------------------------------------------- bi-Cayley lifts (mode 0)
 *
 * Group G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e)),
 * r^k2 = 1 mod m. Blocks A_i (i<k) and B_p (p<k), vertex = block*G + g.
 * Layer l pairs A_i with B_{lay[l][i]} through voltage svol[l][i]:
 *   A_{i,g} ~ B_{p, g*s}.  Each layer is a permutation, so the graph is d-regular.
 * The graph is invariant under left multiplication, so diameter <= D iff every
 * block representative reaches every vertex within D steps.
 */

static int LK, LG, LN, LM, LK2;
static long LPW[64];
static int lay[MAXD][MAXK];
static int svol[MAXD][MAXK];
static int NBR[MAXD][MAXN];
static uint64_t LBUF0[MAXN], LBUF1[MAXN], LREACH[MAXN], LTMP[MAXN];
static int LMARK[1 << 17];
static int LSTAMP = 0;

static long lgcd(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / LK2, b = x % LK2, c = y / LK2, e = y % LK2;
    long t = (a + LPW[b] * c) % LM;
    return (int)(t * LK2 + (b + e) % LK2);
}

static int ginv(int x) {
    int a = x / LK2, b = x % LK2;
    int nb = (LK2 - b) % LK2;
    long t = (LPW[nb] * a) % LM;
    long na = (LM - t) % LM;
    return (int)(na * LK2 + nb);
}

static void set_dart(int l, int i) {
    int p = lay[l][i], s = svol[l][i];
    int si = ginv(s);
    int G = LG, k = LK;
    for (int g = 0; g < G; g++) {
        NBR[l][i * G + g] = (k + p) * G + gmul(g, s);
        NBR[l][(k + p) * G + g] = i * G + gmul(g, si);
    }
}

static int dupcount(void) {
    int dup = 0;
    LSTAMP++;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < LK; i++) {
            long idx = ((long)i * LK + lay[l][i]) * LG + svol[l][i];
            if (LMARK[idx] == LSTAMP) dup++;
            else LMARK[idx] = LSTAMP;
        }
    return dup;
}

/* Writes the reach bitmask of every vertex into out; returns unreached (vertex, block) pairs. */
static long reach_into(uint64_t *out) {
    uint64_t *cur = LBUF0, *nxt = LBUF1;
    int N = LN;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * LK; b++) cur[(long)b * LG] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[NBR[l][v]];
            nxt[v] = x;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long cnt = 0;
    for (int v = 0; v < N; v++) cnt += __builtin_popcountll(cur[v]);
    memcpy(out, cur, sizeof(uint64_t) * (size_t)N);
    return 2L * LK * N - cnt;
}

static long lift_cost(uint64_t *out) {
    long u = reach_into(out);
    return u + (long)LPEN * dupcount();
}

static void lift_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < LK; i++) lay[l][i] = i;
        for (int i = LK - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < LK; i++) svol[l][i] = rndint(LG);
        for (int i = 0; i < LK; i++) set_dart(l, i);
    }
}

static int lift_anneal(double deadline, long iters, long patience) {
    uint64_t full = (1ULL << (2 * LK)) - 1;
    lift_init();
    long cost = lift_cost(LREACH);
    if (cost == 0) return 1;
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters; t++) {
        if ((t & 7) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (LK >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(LK), i2 = rndint(LK - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = lift_cost(LTMP);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(LREACH, LTMP, sizeof(uint64_t) * (size_t)LN);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            if (cost == 0) return 1;
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            for (int tries = 0; tries < 30; tries++) {
                int u = rndint(LN);
                if (LREACH[u] == full) continue;
                int block = u / LG;
                l = rndint(d);
                if (block < LK) {
                    i = block;
                } else {
                    int j = block - LK;
                    for (i = 0; i < LK; i++)
                        if (lay[l][i] == j) break;
                }
                break;
            }
        }
        if (l < 0) { l = rndint(d); i = rndint(LK); }

        int old = svol[l][i];
        int nw = rndint(LG);
        if (nw == old) continue;
        svol[l][i] = nw;
        set_dart(l, i);
        long c2 = lift_cost(LTMP);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(LREACH, LTMP, sizeof(uint64_t) * (size_t)LN);
            if (cost < best) { best = cost; last = t; }
        } else {
            svol[l][i] = old;
            set_dart(l, i);
        }
        if (cost == 0) return 1;
    }
    return cost == 0;
}

static int lift_run(double deadline, long iters, long patience) {
    while (now() < deadline) {
        if (lift_anneal(deadline, iters, patience)) return 1;
    }
    return 0;
}

static void print_lift(void) {
    long m = (long)LK * LG * d;
    printf("%d %ld\n", LN, m);
    for (int i = 0; i < LK; i++)
        for (int g = 0; g < LG; g++) {
            int v = i * LG + g;
            for (int l = 0; l < d; l++) printf("%d %d\n", v, NBR[l][v]);
        }
}

/* argv: 0 mode d D seed limit k m k2 r */
static int lift_entry(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    d = atoi(argv[2]);
    D = atoi(argv[3]);
    long seed = atol(argv[4]);
    double limit = atof(argv[5]);
    int k = atoi(argv[6]);
    long m = atol(argv[7]);
    long k2 = atol(argv[8]);
    long r = atol(argv[9]);
    double t0 = now();
    seed_rng(seed);
    if (d < 1 || d > MAXD || D < 2 || k < 1 || k > MAXK || m < 2 || m > MAXN ||
        k2 < 1 || k2 > 64 || r < 1 || r >= m || lgcd(r, m) != 1) {
        printf("0 0\n");
        return 0;
    }
    LK = k;
    LM = (int)m;
    LK2 = (int)k2;
    LG = LM * LK2;
    LN = 2 * LK * LG;
    if (LN > MAXN || LN < 4) { printf("0 0\n"); return 0; }
    LPW[0] = 1 % m;
    for (int t = 1; t < LK2; t++) LPW[t] = LPW[t - 1] * r % m;
    if (LPW[LK2 - 1] * r % m != 1 % m) { printf("0 0\n"); return 0; }

    double deadline = t0 + limit * 0.9 - 0.3;
    if (lift_run(deadline, 8000, 2000)) print_lift();
    else printf("0 0\n");
    return 0;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: prog 0 d D seed limit k m k2 r | prog 1 d D seed limit < graph\n");
        return 2;
    }
    if (atoi(argv[1]) == 0) return lift_entry(argc, argv);
    if (argc < 6) {
        fprintf(stderr, "usage: prog 1 d D seed limit < graph\n");
        return 2;
    }
    d = atoi(argv[2]);
    D = atoi(argv[3]);
    long seed = atol(argv[4]);
    double limit = atof(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.2;
    seed_rng(seed);
    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


_KS = (1, 2, 3, 4, 5, 6)
_K2_CHOICES = (1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16)
_CAP = 8000  # keeps 2*k*G within the C engine's vertex limit


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
# Group sampling for the C lift search: Z_m x| Z_k2 with r^k2 = 1 mod m.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) with m * k2 close to target, or None."""
    for _ in range(200):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        if rng.random() < 0.3:
            r = 1  # direct product Z_m x Z_k2
        else:
            r = None
            for _ in range(80):
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

    total = max(1.0, 0.8 * time_limit - 3.0)
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

    # Exact constructions.
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

    # Phase 1: C bi-Cayley lift search with a bandit over base sizes k and an order goal
    # that ratchets up on success and eases off on failure.
    lift_deadline = t0 + 0.75 * total
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.05

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        left = lift_deadline - time.monotonic()
        if left < 1.5:
            break
        budget = min(10.0, left)
        goal = min(goal, float(_CAP))
        k = pick_k()
        target = int(goal // (2 * k)) + rng.randrange(0, 3)
        target = min(max(2, target), _CAP // (2 * k) - 20)
        g = _sample_group(target, rng)
        if g is None:
            goal = max(float(best_n) * 1.02, goal * 0.97)
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        if 2 * k * G > _CAP:
            continue
        trials[k] += 1
        seed_c = rng.randrange(1, 1 << 30)
        try:
            text = lib.run_c(C_SOURCE, [0, d, D, seed_c, round(budget, 2), k, m, k2, r],
                             stdin_graph=None, timeout=budget + 15)
            n_, e_ = lib.parse_graph_text(text)
        except Exception:
            n_, e_ = 0, []
        if n_ > best_n and lib.is_valid(n_, e_, d, D):
            wins[k] += 1
            best = (n_, e_)
            best_n = n_
            goal = max(goal, n_ * 1.03)
        else:
            goal = max(float(best_n) * 1.02, goal * 0.97)

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 1.5
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_SOURCE, [1, d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
