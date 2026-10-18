"""Combined program: C-native bi-Cayley lift annealing, then a C grow-by-two engine for small graphs.

New in this version:
- The whole voltage search for Z_m x| Z_k2 lifts runs in C (C_LIFT). The cost is the number of
  (vertex, block) pairs at distance > D. A bitmask DP over the 2k block representatives computes it.
  Left translations are automorphisms, so checking representatives is enough.
- Moves are targeted: an unreached vertex is picked, and one of its darts is re-voltaged or swapped.
- A bandit over base size k in 1..6 and an order ratchet drive the group sampling in C.

Every returned graph is checked with lib.is_valid. K_{d,d} (or a known construction) is the fallback.
"""
import itertools
import time

import lib


C_GROW = r'''
/* Grow-by-two search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
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


C_LIFT = r'''
/* Bi-Cayley lift annealing over Z_m x| Z_k2.
 * Usage: prog d D seed time_limit [goal_n]
 * Output: "n m" + edges of the largest valid lift found, or "0 0".
 *
 * Vertices: A-block i occupies [i*G, (i+1)*G), B-block j occupies [(kb+j)*G, (kb+j+1)*G).
 * Layer l gives the matching A-block i -> B-block lay[l][i] with voltage vol[l][i]:
 * A_{i,g} ~ B_{lay, g*vol}. Left translations are automorphisms, so the cost counts
 * (vertex, block) pairs whose block representative is farther than D, via a bitmask DP.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 40
#define MAXK 6
#define MAXN 60000
#define PEN 1000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

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

/* ---- group Z_m x| Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int gm, gk2, gG, gr;
static int powr[64];

static void set_group(int m, int k2, int r) {
    gm = m; gk2 = k2; gG = m * k2; gr = r;
    long p = 1 % m;
    for (int b = 0; b < k2; b++) {
        powr[b] = (int)p;
        p = p * r % m;
    }
}

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2;
    int c = y / gk2, e = y % gk2;
    long long t = ((long long)a + (long long)powr[b] * c) % gm;
    return (int)(t * gk2 + (b + e) % gk2);
}

/* ---- lift state ---- */
static int kb, NN;
static int lay[MAXD][MAXK], vol[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint16_t bufA[MAXN], bufB[MAXN], rcur[MAXN], rnew[MAXN];

static void set_dart(int l, int i) {
    int j = lay[l][i], s = vol[l][i];
    int Ab = i * gG, Bb = (kb + j) * gG;
    for (int g = 0; g < gG; g++) {
        int h = gmul(g, s);
        nbr[l][Ab + g] = Bb + h;
        nbr[l][Bb + h] = Ab + g;
    }
}

/* Writes per-vertex reach masks into dst; returns the number of unreached (vertex, block) pairs. */
static long reach_cost(uint16_t *dst) {
    uint16_t *cur = bufA, *nxt = bufB;
    int n = NN;
    memset(cur, 0, sizeof(uint16_t) * (size_t)n);
    for (int b = 0; b < 2 * kb; b++) cur[b * gG] = (uint16_t)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint16_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint16_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < n; v++) cost += 2 * kb - __builtin_popcount(cur[v]);
    memcpy(dst, cur, sizeof(uint16_t) * (size_t)n);
    return cost;
}

static long dupcount(void) {
    long c = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < kb; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l2][i] == lay[l][i] && vol[l2][i] == vol[l][i]) c++;
    return c;
}

static long full_cost(uint16_t *dst) {
    return reach_cost(dst) + PEN * dupcount();
}

static long pw_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static int sample_group(int k, long target, int *mo, int *k2o, int *ro) {
    static const int CH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int att = 0; att < 300; att++) {
        int k2 = CH[rndint(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (2L * k * m * k2 > MAXN) continue;
        long r = -1;
        if (k2 == 1) {
            r = 1 % m;
        } else {
            if (rndint(4) == 0 && pw_mod(m - 1, k2, m) == 1 % m) {
                r = m - 1;
            } else if (m >= 3) {
                for (int t = 0; t < 60; t++) {
                    long c = 2 + rndint((int)(m - 2));
                    if (gcd_l(c, m) == 1 && pw_mod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
        }
        if (r < 0) continue;
        *mo = (int)m;
        *k2o = k2;
        *ro = (int)r;
        return 1;
    }
    return 0;
}

static int search_lift(long iters, long patience) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) lay[l][i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1), t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < kb; i++) vol[l][i] = rndint(gG);
        for (int i = 0; i < kb; i++) set_dart(l, i);
    }
    uint16_t full = (uint16_t)((1u << (2 * kb)) - 1);
    long cost = full_cost(rcur);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 7) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (kb >= 2 && rnd01() < 0.25) {
            /* Swap the B-blocks of two A-blocks inside one layer. */
            int l = rndint(d);
            int i1 = rndint(kb), i2 = rndint(kb - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = full_cost(rnew);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(rcur, rnew, sizeof(uint16_t) * (size_t)NN);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        /* Re-voltage one dart, aimed at an unreached vertex when one is sampled. */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int v = rndint(NN);
                if (rcur[v] != full) {
                    int b = v / gG;
                    l = rndint(d);
                    if (b < kb) {
                        i = b;
                    } else {
                        int j = b - kb;
                        i = -1;
                        for (int q = 0; q < kb; q++)
                            if (lay[l][q] == j) { i = q; break; }
                    }
                    break;
                }
            }
        }
        if (l < 0 || i < 0) { l = rndint(d); i = rndint(kb); }

        int old = vol[l][i];
        int nv = rndint(gG);
        if (nv == old) continue;
        vol[l][i] = nv;
        set_dart(l, i);
        long c2 = full_cost(rnew);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(rcur, rnew, sizeof(uint16_t) * (size_t)NN);
            if (cost < best) { best = cost; last = t; }
        } else {
            vol[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static int bestK = 0, bestM = 0, bestK2 = 0, bestR = 0;
static long bestN = 0;
static int blay[MAXD][MAXK], bvol[MAXD][MAXK];

static void emit(void) {
    set_group(bestM, bestK2, bestR);
    kb = bestK;
    NN = 2 * kb * gG;
    printf("%d %ld\n", NN, (long)d * kb * gG);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < kb; i++)
            for (int g = 0; g < gG; g++) {
                int u = i * gG + g;
                int v = (kb + blay[l][i]) * gG + gmul(g, bvol[l][i]);
                printf("%d %d\n", u, v);
            }
}

static long moore_cap(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long goal = argc > 5 ? atol(argv[5]) : 2;
    t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    long mb = moore_cap();
    if (mb > MAXN) mb = MAXN;
    if (goal < 2) goal = 2;

    long trials[MAXK + 1], wins[MAXK + 1];
    memset(trials, 0, sizeof trials);
    memset(wins, 0, sizeof wins);
    long best_n = 0;

    while (now() < t_end) {
        if (goal > mb) goal = mb;
        if (goal < 2) goal = 2;

        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        long target = goal / (2L * k) + rndint(3);
        if (target < 2) target = 2;

        int m, k2, r;
        if (!sample_group(k, target, &m, &k2, &r)) continue;
        set_group(m, k2, r);
        kb = k;
        NN = 2 * k * gG;
        if (NN > mb) continue;
        if (NN <= best_n) {
            goal = best_n + best_n / 50 + 1;
            continue;
        }

        trials[k]++;
        if (search_lift(6000, 1500)) {
            wins[k]++;
            if (NN > best_n) {
                best_n = NN;
                bestK = kb; bestM = m; bestK2 = k2; bestR = r;
                memcpy(blay, lay, sizeof lay);
                memcpy(bvol, vol, sizeof vol);
            }
            goal = NN + NN / 25 + 1;
        } else {
            long g2 = goal - goal / 100;
            long floor_n = best_n + best_n / 50 + 1;
            goal = g2 > floor_n ? g2 : floor_n;
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    bestN = best_n;
    emit();
    return 0;
}
'''


_GROW_MAX_N = 1500
_LIFT_MAX_D = 40


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

    # Phase 1: C-native bi-Cayley lift annealing. It gets almost the whole budget when the
    # start graph is already large, since the grow phase is skipped in that case.
    if 2 <= d <= _LIFT_MAX_D and D >= 3:
        if best_n > _GROW_MAX_N:
            lift_budget = total - 2.0
        else:
            lift_budget = 0.7 * total
        lift_budget = max(1.0, lift_budget)
        try:
            text = lib.run_c(C_LIFT, [d, D, seed, round(lift_budget, 2), int(best_n)],
                             timeout=lift_budget + 30)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    # Phase 2: C grow-by-two from the best small graph, using the remaining time.
    remaining = final - time.monotonic() - 2.0
    if best_n <= _GROW_MAX_N and best_n > 2 * d and remaining > 2.0:
        try:
            text = lib.run_c(C_GROW, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 10)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
