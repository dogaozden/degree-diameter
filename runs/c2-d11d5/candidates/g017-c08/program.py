"""Combined program: bi-Cayley voltage-lift annealing moved into C (new idea: the whole lift search,
including group sampling, layer permutations and voltage moves, runs in one C loop with a
bitmask reach check over all vertices and seeds only at block representatives). Python supplies
exact constructions and the start graph. A grow-by-two phase runs if the best graph is small.

Every returned graph is checked with lib.is_valid, and K_{d,d} (or a known construction) is the fallback.
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
#define MAXK 4
#define PEN 1000L
#define GROW_MAX 1500

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

/* ---------------- bi-Cayley lift search over Z_m x| Z_k2 ----------------
 * Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
 * Layer l pairs A_i with B_{LL[l][i]} through voltage LS[l][i]: A_{i,g} ~ B_{j, g*s}.
 * Each layer is a permutation, so degree d is exact. Left multiplication is an automorphism,
 * so checking reach from all vertices to the block representatives (b*G) is a full check.
 */
static int LK, LG, Lm, Lk2;
static int Lpw[16];
static int Lnb[MAXD][MAXN];
static int LL[MAXD][MAXK];
static int LS[MAXD][MAXK];
static int LSi[MAXD][MAXK];
static uint64_t RR0[MAXN], RR1[MAXN], LRET[MAXN], LREC[MAXN];
static Graph cand;
static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;
static double goal_order = 4.0;

static int gmul(int x, int y) {
    int a = x / Lk2, b = x % Lk2, c = y / Lk2, e = y % Lk2;
    long t = ((long)a + (long)Lpw[b] * c) % Lm;
    return (int)t * Lk2 + (b + e) % Lk2;
}

static int ginv(int x) {
    int a = x / Lk2, b = x % Lk2;
    int nb = (Lk2 - b) % Lk2;
    long t = ((long)Lpw[nb] * a) % Lm;
    return (int)((Lm - t) % Lm) * Lk2 + nb;
}

static void set_dart(int l, int i) {
    int G = LG, k = LK, j = LL[l][i], s = LS[l][i], si = LSi[l][i];
    for (int g = 0; g < G; g++) {
        Lnb[l][i * G + g] = (k + j) * G + gmul(g, s);
        Lnb[l][(k + j) * G + g] = i * G + gmul(g, si);
    }
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < LK; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (LL[l][i] == LL[l2][i] && LS[l][i] == LS[l2][i]) c++;
    return c;
}

/* Cost = unreached (vertex, block) pairs + PEN * duplicate darts. Reach bits go to LRET. */
static long lift_cost(void) {
    int G = LG, N = 2 * LK * G, B = 2 * LK;
    uint64_t *cur = RR0, *nxt = RR1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < B; b++) cur[(size_t)b * G] |= 1ULL << b;
    for (int rr = 0; rr < D; rr++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[Lnb[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += B - __builtin_popcountll(cur[v]);
    memcpy(LRET, cur, sizeof(uint64_t) * (size_t)N);
    return unr + PEN * dupcount();
}

static int build_cand(int k, int G) {
    int N = 2 * k * G, A = k * G;
    cand.n = N;
    for (int v = 0; v < N; v++) {
        cand.deg[v] = 0;
        cand.side[v] = (unsigned char)(v < A ? 0 : 1);
    }
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) add_edge(&cand, v, Lnb[l][v]);
    return is_valid(&cand);
}

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Random Z_m x| Z_k2 with m*k2 >= target; r = 1 (direct product) is the safe fallback. */
static void sample_group(long target, int *m_out, int *k2_out, int *r_out) {
    static const int K2S[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12};
    int k2 = K2S[rndint(12)];
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            long c = 2 + rndint((int)(m - 2));
            if (gcdl(c, m) == 1 && powmodl(c, k2, m) == 1 % m) { r = (int)c; break; }
        }
    }
    *m_out = (int)m;
    *k2_out = k2;
    *r_out = r;
}

/* Simulated annealing for one group. On success the candidate graph is in cand. */
static int anneal_run(int k, int m, int k2, int r, double deadline, long maxit, long patience) {
    LK = k;
    Lm = m;
    Lk2 = k2;
    LG = m * k2;
    int G = LG, N = 2 * k * G, B = 2 * k;
    uint64_t full = (1ULL << B) - 1;
    Lpw[0] = 1 % m;
    for (int t = 1; t < k2; t++) Lpw[t] = (int)((long)Lpw[t - 1] * r % m);

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) LL[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), t = LL[l][i];
            LL[l][i] = LL[l][j];
            LL[l][j] = t;
        }
        for (int i = 0; i < k; i++) {
            LS[l][i] = rndint(G);
            LSi[l][i] = ginv(LS[l][i]);
            set_dart(l, i);
        }
    }
    long cost = lift_cost();
    memcpy(LREC, LRET, sizeof(uint64_t) * (size_t)N);
    long c0 = cost > 1 ? cost : 1;
    long best_cost = cost, last = 0;

    for (long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        if (it - last > patience) break;
        double temp = 0.01 * (double)c0 * (1.0 - (double)it / (double)maxit);
        if (temp < 0.5) temp = 0.5;
        long c2 = cost;
        int accept = 0;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int t = LL[l][i1];
            LL[l][i1] = LL[l][i2];
            LL[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                accept = 1;
            } else {
                t = LL[l][i1];
                LL[l][i1] = LL[l][i2];
                LL[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = 0, i = 0, v = -1;
            for (int tr = 0; tr < 20; tr++) {
                int u = rndint(N);
                if (LREC[u] != full) { v = u; break; }
            }
            if (v >= 0 && rnd01() < 0.7) {
                int blk = v / G;
                l = rndint(d);
                if (blk < k) {
                    i = blk;
                } else {
                    int j = blk - k;
                    i = rndint(k);
                    for (int ii = 0; ii < k; ii++)
                        if (LL[l][ii] == j) { i = ii; break; }
                }
            } else {
                l = rndint(d);
                i = rndint(k);
            }
            int old = LS[l][i], nw = rndint(G);
            if (nw == old) continue;
            LS[l][i] = nw;
            LSi[l][i] = ginv(nw);
            set_dart(l, i);
            c2 = lift_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                accept = 1;
            } else {
                LS[l][i] = old;
                LSi[l][i] = ginv(old);
                set_dart(l, i);
            }
        }

        if (accept) {
            cost = c2;
            memcpy(LREC, LRET, sizeof(uint64_t) * (size_t)N);
            if (cost < best_cost) { best_cost = cost; last = it; }
        }
    }
    if (cost != 0) return 0;
    return build_cand(k, G);
}

/* Ratcheted search over random lifts; each success raises the order goal above the new best. */
static void lift_phase(double until) {
    while (now() < until) {
        int k = 1 + rndint(MAXK);
        long cap = MAXN / (2L * k);
        long target = (long)(goal_order / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (target > cap) target = cap;
        int m, k2, r;
        sample_group(target, &m, &k2, &r);
        long G = (long)m * k2;
        if (2L * k * G > MAXN) continue;
        if (2L * k * G <= gbest.n) {
            if (goal_order < gbest.n * 1.02) goal_order = gbest.n * 1.02;
            continue;
        }
        double slice = now() + 6.0;
        if (slice > until) slice = until;
        int ok = anneal_run(k, m, k2, r, slice, 400000L, 8000L);
        if (ok && cand.n > gbest.n) {
            copy_graph(&gbest, &cand);
            if (goal_order < gbest.n * 1.03) goal_order = gbest.n * 1.03;
        } else if (!ok) {
            double f = gbest.n * 1.01;
            if (goal_order * 0.995 > f) f = goal_order * 0.995;
            goal_order = f;
        }
    }
}

/* ---------------- grow-by-two from the best graph ---------------- */

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
    double t_end = t0 + limit * 0.92 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n > 0) goal_order = gbest.n * 1.02;
    else goal_order = 4.0;

    double lift1 = t0 + 0.8 * (t_end - t0);
    lift_phase(lift1);
    if (gbest.n > 0 && gbest.n <= GROW_MAX) grow_search(t_end);
    else lift_phase(t_end);

    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    budget = max(1.0, 0.9 * time_limit - 2.0)
    deadline = t0 + budget

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
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # C engine: lift annealing, then grow-by-two if the graph is still small.
    remaining = deadline - time.monotonic() - 1.0
    if remaining > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
