"""Combined program: a C bi-Cayley voltage-lift search over semidirect groups, then a C
grow-by-two engine on small graphs.

Every returned graph is checked with lib.is_valid, and K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealing over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h.
# Layer l pairs A_i with B_{lay[l][i]} through voltage vol[l][i]: A_{i,g} ~ B_{j, g*s}.
# Every layer is a permutation, so every vertex has degree d. G acts regularly on every
# block, so the diameter is <= D iff every block representative reaches every vertex in D steps.
# Usage: prog d D seed time_limit start_n   (prints the best graph found with n > start_n, else "0 0")
# ----------------------------------------------------------------------------

C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 4
#define MAXG 8192
#define MAXN (2 * MAXK * MAXG)
#define MAXDEG 32
#define PEN 1000

static int d, D, K, G, M, K2, R;
static int pw[64];
static int lay[MAXDEG][MAXK];
static int vol[MAXDEG][MAXK];
static int nbr[MAXDEG][MAXN];
static int NN;
static int bufS[MAXN], bufA[MAXN], bufB[MAXN];
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int wins[MAXK + 1], trials[MAXK + 1];
static int bestU[MAXN * MAXDEG / 2], bestV[MAXN * MAXDEG / 2];
static long bestM = 0;
static int bestNN = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Group element x = a*K2 + b represents (a, b) in Z_M x| Z_K2. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
}

static int sample_group(int target) {
    static const int ks[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int att = 0; att < 300; att++) {
        K2 = ks[rndint(20)];
        M = (target + K2 - 1) / K2;
        if (M < 2) M = 2;
        if (M * K2 > MAXG) continue;
        if (K2 == 1) {
            R = 1;
        } else {
            if (M < 3) continue;
            int found = 0;
            if (K2 == 2 && rnd01() < 0.3) {
                R = M - 1;
                if (powmod(R, 2, M) == 1 % M && gcd_i(R, M) == 1) found = 1;
            }
            for (int tr = 0; tr < 80 && !found; tr++) {
                int c = 2 + rndint(M - 2);
                if (gcd_i(c, M) == 1 && powmod(c, K2, M) == 1 % M) {
                    R = c;
                    found = 1;
                }
            }
            if (!found) continue;
        }
        for (int b = 0; b < K2; b++) pw[b] = (int)powmod(R, b, M);
        G = M * K2;
        return 1;
    }
    return 0;
}

/* Write the neighbours created by layer l for base vertex i (A side) and its partner (B side). */
static void set_dart(int l, int i) {
    int j = lay[l][i], s = vol[l][i];
    int Ab = i * G, Bb = (K + j) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        nbr[l][Ab + g] = Bb + h;
        nbr[l][Bb + h] = Ab + g;
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            vol[l][i] = rndint(G);
            set_dart(l, i);
        }
    }
}

/* Unreached (block representative, vertex) pairs; out receives the bitmask per vertex. */
static long compute_reach(int *out) {
    int *a = out, *b = bufS;
    for (int v = 0; v < NN; v++) a[v] = 0;
    for (int bl = 0; bl < 2 * K; bl++) a[bl * G] = 1 << bl;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            int x = a[v];
            for (int l = 0; l < d; l++) x |= a[nbr[l][v]];
            b[v] = x;
            if (x != a[v]) changed = 1;
        }
        int *t = a;
        a = b;
        b = t;
        if (!changed) break;
    }
    if (a != out) memcpy(out, a, sizeof(int) * NN);
    long cnt = 0;
    for (int v = 0; v < NN; v++) cnt += __builtin_popcount((unsigned)out[v]);
    return (long)(2 * K) * NN - cnt;
}

/* Number of repeated darts (same base vertex, same partner block, same voltage). */
static int dupcount(void) {
    int c = 0, tot = d * K;
    for (int p = 1; p < tot; p++) {
        int l1 = p / K, i1 = p % K;
        for (int q = 0; q < p; q++) {
            int l2 = q / K, i2 = q % K;
            if (i1 == i2 && lay[l1][i1] == lay[l2][i2] && vol[l1][i1] == vol[l2][i2]) c++;
        }
    }
    return c;
}

static long anneal(long iters, long patience) {
    int full = (1 << (2 * K)) - 1;
    int *cur = bufA, *tmp = bufB;
    long cost = compute_reach(cur) + (long)PEN * dupcount();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 255) == 0 && now() > t_end) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tv = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tv;
            set_dart(l, i1);
            set_dart(l, i2);
            c2 = compute_reach(tmp) + (long)PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                int *sw = cur;
                cur = tmp;
                tmp = sw;
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                tv = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tv;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = rndint(d), i = rndint(K);
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tr = 0; tr < 30 && v < 0; tr++) {
                int c = rndint(NN);
                if (cur[c] != full) v = c;
            }
            if (v >= 0) {
                int bl = v / G;
                if (bl < K) {
                    i = bl;
                } else {
                    int j = bl - K;
                    i = -1;
                    for (int ii = 0; ii < K; ii++)
                        if (lay[l][ii] == j) {
                            i = ii;
                            break;
                        }
                    if (i < 0) continue;
                }
            }
        }

        int old = vol[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        vol[l][i] = nw;
        set_dart(l, i);
        c2 = compute_reach(tmp) + (long)PEN * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            int *sw = cur;
            cur = tmp;
            tmp = sw;
            cost = c2;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            vol[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost;
}

static void save_state(void) {
    long m = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++) {
            bestU[m] = u;
            bestV[m] = nbr[l][u];
            m++;
        }
    bestM = m;
    bestNN = NN;
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) {
            bs = s;
            bk = k;
        }
    }
    return bk;
}

static double ease(double goal, double best_n) {
    double a = best_n * 1.02 + 1.0, b = goal * 0.99;
    return a > b ? a : b;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long best_n = start_n;
    int found = 0;
    double goal = (double)start_n * 1.03 + 2.0;

    while (now() < t_end) {
        int k = pick_k();
        long target = (long)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group((int)target)) {
            goal = ease(goal, (double)best_n);
            continue;
        }
        K = k;
        NN = 2 * K * G;
        if (NN <= best_n || NN > MAXN) {
            goal = (double)best_n * 1.02 + 1.0;
            continue;
        }
        trials[k]++;
        random_state();
        long cost = anneal(60000, 8000);
        if (cost == 0) {
            wins[k]++;
            save_state();
            best_n = NN;
            found = 1;
            goal = (double)NN * 1.04 + 1.0;
        } else {
            goal = ease(goal, (double)best_n);
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestNN, bestM);
    for (long e = 0; e < bestM; e++) printf("%d %d\n", bestU[e], bestV[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# C engine 2: grow-by-two from a valid start graph.
# Usage: prog d D seed time_limit < start_graph
# ----------------------------------------------------------------------------

C_GROW = r'''
/* Grow-by-two search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Each step inserts one vertex on each side, using the spare degree freed by d-1 deleted
 * edges, then anneals degree-preserving edge swaps until every pair is within distance D.
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

static double t_end;
static Graph gbest, gwork;
static int used[MAXN];
static int stamp = 0;

/* One grow-by-two attempt starting from best; on success work holds n+2 valid vertices. */
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
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
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

_GROW_MAX_N = 1500


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

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

    # Phase 1: C bi-Cayley lift annealing. The C side runs many trials itself, so the
    # per-eval cost stays low and only the best valid graph is returned to Python.
    use_grow = best_n <= _GROW_MAX_N
    left = final - time.monotonic()
    lift_budget = (0.6 * left - 1.0) if use_grow else (left - 3.0)
    if d >= 2 and lift_budget > 3.0:
        try:
            text = lib.run_c(C_LIFT, [d, D, seed, round(lift_budget, 2), best_n],
                             timeout=lift_budget + 10)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    # Phase 2: C grow-by-two on small graphs, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if use_grow and remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_GROW, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
