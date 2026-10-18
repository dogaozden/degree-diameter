"""Combined program: C bi-Cayley lift annealer (block-representative bitmask reach,
incremental layer rebuild), then a C grow-by-two engine that inserts vertices into the
best graph found. Every returned graph is checked with lib.is_valid; K_{d,d} (or a known
construction) is the fallback.
"""
import itertools
import time

import lib


# Bi-Cayley lift annealer over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < kk), B_{j,h} = (kk+j)*G + h, g,h in the group.
# Layer l pairs A_i with B_{lay[l][i]} through voltage S[l][i]: A_{i,g} ~ B_{j,g*s}.
# Left multiplication by the group is an automorphism, so distances from the 2*kk block
# representatives (index b*G) to every vertex decide the diameter. Reach is kept as a
# bitmask per vertex over these representatives. Only the rebuilt layer's neighbour table
# changes after a move, so a move costs one layer rebuild plus D*N*d mask ORs.
C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXL 32
#define MAXK 4
#define MAXP 64
#define PEN 1000L
#define ITERS 20000L
#define PATIENCE 4000L

static int d, D, kk, G, N, gm, k2;
static int lay[MAXL][MAXK], ilay[MAXL][MAXK];
static int S[MAXL][MAXK], Si[MAXL][MAXK];
static int nbr[MAXL][MAXN];
static int powr[MAXP];
static uint64_t PA[MAXN], PB[MAXN], RCUR[MAXN], RCAND[MAXN];
static long trials[MAXK + 1], wins[MAXK + 1];
static int *bestE;
static long best_n = 0, best_m = 0;
static uint64_t rng_state = 88172645463325252ULL;

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

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod(long long b, long long e, long long md) {
    long long r = 1 % md;
    b %= md;
    while (e > 0) {
        if (e & 1) r = r * b % md;
        b = b * b % md;
        e >>= 1;
    }
    return (int)r;
}

static void set_group(int m, int kg, int r) {
    gm = m;
    k2 = kg;
    G = m * kg;
    powr[0] = 1 % m;
    for (int b = 1; b < kg; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element coded as a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = ((long long)a + (long long)powr[b] * c) % gm;
    int bb = (b + e) % k2;
    return (int)(t * k2 + bb);
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = ((long long)powr[nb] * a) % gm;
    long long aa = (gm - t) % gm;
    return (int)(aa * k2 + nb);
}

static void sample_group(int target, int *pm, int *pk, int *pr) {
    static const int KG[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int kg = KG[rndint(20)];
    int m = (target + kg - 1) / kg;
    if (m < 2) m = 2;
    int r = 1;
    if (kg > 1 && m > 2) {
        for (int tr = 0; tr < 60; tr++) {
            int c = 2 + rndint(m - 2);
            if (gcd_int(c, m) == 1 && powmod(c, kg, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    *pm = m;
    *pk = kg;
    *pr = r;
}

static void build_layer(int l) {
    for (int i = 0; i < kk; i++) {
        int j = lay[l][i];
        int s = S[l][i], si = Si[l][i];
        int ab = i * G, bb = (kk + j) * G;
        for (int h = 0; h < G; h++) {
            nbr[l][ab + h] = bb + gmul(h, s);
            nbr[l][bb + h] = ab + gmul(h, si);
        }
    }
}

/* Number of repeated darts: same A-block, same B-block and same voltage in two layers. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < kk; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Cost = unreached (vertex, representative) pairs + penalty for repeated darts.
 * Writes the final reach masks into out. */
static long eval_cost(uint64_t *out) {
    uint64_t *cur = PA, *nxt = PB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * kk; b++) cur[(long)b * G] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        bad += 2 * kk - __builtin_popcountll(cur[v]);
        out[v] = cur[v];
    }
    return bad + PEN * dupcount();
}

static void randomize(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kk; i++) lay[l][i] = i;
        for (int i = kk - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < kk; i++) {
            ilay[l][lay[l][i]] = i;
            S[l][i] = rndint(G);
            Si[l][i] = ginv(S[l][i]);
        }
        build_layer(l);
    }
}

/* Returns 1 if a valid lift was reached (state left in nbr), 0 if not, -1 on timeout. */
static int anneal(long iters, long patience, double deadline) {
    int full = (1 << (2 * kk)) - 1;
    long last = 0, best, cost, c2;
    randomize();
    cost = eval_cost(RCUR);
    best = cost;
    double c0 = cost > 1 ? (double)cost : 1.0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) return -1;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (kk >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(kk);
            int i2 = rndint(kk - 1);
            if (i2 >= i1) i2++;
            int j1 = lay[l][i1], j2 = lay[l][i2];
            lay[l][i1] = j2;
            lay[l][i2] = j1;
            ilay[l][j1] = i2;
            ilay[l][j2] = i1;
            build_layer(l);
            c2 = eval_cost(RCAND);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(RCUR, RCAND, sizeof(uint64_t) * (size_t)N);
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                lay[l][i1] = j1;
                lay[l][i2] = j2;
                ilay[l][j1] = i1;
                ilay[l][j2] = i2;
                build_layer(l);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tr = 0; tr < 30; tr++) {
                int c = rndint(N);
                if (RCUR[c] != (uint64_t)full) {
                    v = c;
                    break;
                }
            }
            if (v >= 0) {
                int blk = v / G;
                l = rndint(d);
                i = (blk < kk) ? blk : ilay[l][blk - kk];
            }
        }
        if (l < 0) {
            l = rndint(d);
            i = rndint(kk);
        }
        int nw = rndint(G);
        int old = S[l][i];
        if (nw == old) continue;
        int oldsi = Si[l][i];
        S[l][i] = nw;
        Si[l][i] = ginv(nw);
        build_layer(l);
        c2 = eval_cost(RCAND);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(RCUR, RCAND, sizeof(uint64_t) * (size_t)N);
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            S[l][i] = old;
            Si[l][i] = oldsi;
            build_layer(l);
        }
    }
    return cost == 0 ? 1 : 0;
}

static void record_best(void) {
    long c = 0;
    for (int v = 0; v < kk * G; v++)
        for (int l = 0; l < d; l++) {
            bestE[2 * c] = v;
            bestE[2 * c + 1] = nbr[l][v];
            c++;
        }
    best_m = c;
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = ((double)wins[k] + 1.0) / ((double)trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_n = argc > 5 ? atol(argv[5]) : 0;
    double t_end = now() + limit * 0.92 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }
    bestE = malloc(sizeof(int) * 2 * 262144);
    if (!bestE) {
        printf("0 0\n");
        return 0;
    }
    best_n = min_n;
    best_m = 0;
    double goal = (double)min_n * 1.03 + 2.0;

    while (now() < t_end) {
        int kc = pick_k();
        int target = (int)(goal / (2.0 * kc)) + rndint(3);
        if (target < 2) target = 2;
        int m, kg, r;
        sample_group(target, &m, &kg, &r);
        long Nc = 2L * kc * (long)(m * kg);
        if (Nc > MAXN) {
            goal *= 0.95;
            continue;
        }
        if (Nc <= best_n) {
            if (goal < best_n * 1.02 + 2.0) goal = best_n * 1.02 + 2.0;
            continue;
        }
        set_group(m, kg, r);
        kk = kc;
        N = (int)Nc;
        trials[kk]++;
        int res = anneal(ITERS, PATIENCE, t_end);
        if (res < 0) break;
        if (res == 1) {
            wins[kk]++;
            record_best();
            best_n = N;
            double up = N * 1.04;
            if (goal < up) goal = up;
            if (goal > MAXN * 0.95) goal = MAXN * 0.95;
        } else {
            double low = best_n * 1.02 + 2.0;
            goal = goal * 0.99;
            if (goal < low) goal = low;
        }
    }

    if (best_m <= 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", best_n, best_m);
    for (long e = 0; e < best_m; e++) printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    return 0;
}
'''


# Grow-by-two search core (unchanged engine): inserts one vertex on each side and anneals
# degree-preserving swaps until every pair is within distance D.
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

    if (d < 1 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&gbest);
    if (gbest.n == 0) {
        printf("0 0\n");
        return 0;
    }
    grow_search(t_end);
    if (!is_valid(&gbest)) {
        printf("0 0\n");
        return 0;
    }
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

    total = max(1.0, 0.85 * time_limit - 2.5)
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

    # Phase 1: C bi-Cayley lift annealing over semidirect products, seeded by the best order.
    if 2 <= d <= 30 and D >= 2:
        lift_secs = (final - time.monotonic() - 3.0) * 0.8
        if lift_secs > 3.0:
            try:
                text = lib.run_c(C_LIFT, [d, D, seed, round(lift_secs, 2), best_n],
                                 timeout=lift_secs + 10)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    # Phase 2: C grow-by-two from the best graph, using the remaining time.
    remaining = final - time.monotonic() - 1.5
    if remaining > 2.0 and best_n > 2 * d:
        try:
            text = lib.run_c(C_GROW, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
