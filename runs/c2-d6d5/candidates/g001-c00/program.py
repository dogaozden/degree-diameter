"""Combined search for bipartite degree-diameter graphs.

Python: exact Moore / record graphs for D = 3, and a K_{d,d} fallback.
C engine: (1) bi-Cayley voltage-lift annealing over random semidirect products
Z_m x| Z_k, with a bandit over the base size k (from g000-i00); (2) grow-by-two
annealing on the best graph (from g000-seed). Every returned graph is checked
with lib.is_valid, and the K_{d,d} fallback is always kept.
"""
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

#define MAXN 4096
#define MAXD 16
#define MAXDEG 16
#define MAXW (MAXN / 64)
#define MAXK 4
#define MAXKK 64
#define PEN 1000L
#define SA_ITERS 20000
#define SA_PATIENCE 3000

static int d, D;

/* ------------------------------------------------------------ utilities */

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

/* ------------------------------------------------------------ graph type */

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    unsigned char side[MAXN];
} Graph;

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

/* Bitset reachability. Returns the number of unordered pairs at distance > D. */
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
            memcpy(dst, src, sizeof(uint64_t) * W);
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
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) {
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXKK];
} Grp;

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k, b = x % g->k, c = y / g->k, e = y % g->k;
    return (int)(((long)a + (long)g->rp[b] * c) % g->m) * g->k + (b + e) % g->k;
}

static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, Grp *g) {
    int nk = (int)(sizeof K2S / sizeof K2S[0]);
    for (int tries = 0; tries < 200; tries++) {
        int k = K2S[rndint(nk)];
        int m = (target + k - 1) / k;
        if (m < 2) m = 2;
        if (m * k > MAXN) continue;
        int r = -1;
        if (k == 1) {
            r = 1;
        } else if (k == 2 && rnd01() < 0.3) {
            int c = m - 1;
            if (gcd(c, m) == 1 && powmod(c, 2, m) == 1 % m) r = c;
        } else {
            for (int t = 0; t < 60; t++) {
                int c = m > 2 ? 2 + rndint(m - 2) : 1;
                if (gcd(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        g->m = m;
        g->k = k;
        g->r = r;
        g->rp[0] = 1 % m;
        for (int b = 1; b < k; b++) g->rp[b] = (int)((long)g->rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ bi-Cayley lifts */

/* A-block i has blocks A_i,x = i*G+x. Layer l pairs A_i with B-block layers[l][i]
 * via voltage S[l][i]: A_{i,x} ~ B_{j, x*s}. Every layer is a permutation of blocks,
 * so every vertex has exactly d neighbours (one per layer). */
typedef struct {
    int k, G, N;
    int layers[MAXD][MAXK];
    int S[MAXD][MAXK];
} Lift;

static int nbr[MAXD][MAXN];

static void rebuild(const Lift *L, const Grp *g) {
    int k = L->k, G = L->G;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = L->layers[l][i], s = L->S[l][i];
            for (int x = 0; x < G; x++) {
                int u = i * G + x;
                int w = (k + j) * G + gmul(g, x, s);
                nbr[l][u] = w;
                nbr[l][w] = u;
            }
        }
}

/* Number of pairs of darts from the same A-block with the same target and voltage. */
static int dupcount(const Lift *L) {
    int c = 0;
    for (int i = 0; i < L->k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (L->layers[l1][i] == L->layers[l2][i] && L->S[l1][i] == L->S[l2][i]) c++;
    return c;
}

static uint64_t EA[MAXN], EB[MAXN];

/* Unreached (representative, vertex) pairs. Bit b of reach[v] = block-representative b
 * is within distance D of v. Zero means diameter <= D. */
static long eval_unreached(const Lift *L, uint64_t *reach_out) {
    int N = L->N, k = L->k, G = L->G;
    uint64_t *cur = EA, *nxt = EB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] |= 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long reached = 0;
    for (int v = 0; v < N; v++) {
        reach_out[v] = cur[v];
        reached += __builtin_popcountll(cur[v]);
    }
    return 2L * k * N - reached;
}

static uint64_t RCUR[MAXN], RTMP[MAXN];

static void init_random_lift(Lift *L) {
    int k = L->k, G = L->G;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) L->layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = L->layers[l][i];
            L->layers[l][i] = L->layers[l][j];
            L->layers[l][j] = t;
        }
        for (int i = 0; i < k; i++) L->S[l][i] = rndint(G);
    }
}

/* Simulated annealing over layers and voltages. Returns 1 on success (nbr holds the lift). */
static int sa_trial(Lift *L, const Grp *g, double until) {
    int k = L->k, G = L->G, N = L->N;
    uint64_t full = (1ULL << (2 * k)) - 1;
    init_random_lift(L);
    rebuild(L, g);
    long cost = eval_unreached(L, RCUR) + PEN * (long)dupcount(L);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;
    for (int t = 0; t < SA_ITERS; t++) {
        if (cost == 0) break;
        if (t - last > SA_PATIENCE) break;
        if ((t & 7) == 0 && now() > until) return 0;
        double temp = 0.01 * c0 * (1.0 - (double)t / SA_ITERS);
        if (temp < 0.5) temp = 0.5;

        int type = 0, ol = 0, oi = 0, oi2 = 0, oold = 0;
        if (k >= 2 && rnd01() < 0.25) {
            type = 1;
            ol = rndint(d);
            oi = rndint(k);
            oi2 = rndint(k - 1);
            if (oi2 >= oi) oi2++;
            int tmp = L->layers[ol][oi];
            L->layers[ol][oi] = L->layers[ol][oi2];
            L->layers[ol][oi2] = tmp;
        } else {
            int l = 0, i = 0;
            if (rnd01() < 0.4) {
                int start = rndint(N), u = -1;
                for (int q = 0; q < N; q++) {
                    int v = (start + q) % N;
                    if (RCUR[v] != full) { u = v; break; }
                }
                if (u >= 0) {
                    int blk = u / G;
                    l = rndint(d);
                    if (blk < k) {
                        i = blk;
                    } else {
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (L->layers[l][ii] == blk - k) i = ii;
                        if (i < 0) i = rndint(k);
                    }
                } else {
                    l = rndint(d);
                    i = rndint(k);
                }
            } else {
                l = rndint(d);
                i = rndint(k);
            }
            int nw = rndint(G);
            if (nw == L->S[l][i]) continue;
            ol = l;
            oi = i;
            oold = L->S[l][i];
            L->S[l][i] = nw;
        }

        rebuild(L, g);
        long c2 = eval_unreached(L, RTMP) + PEN * (long)dupcount(L);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(RCUR, RTMP, sizeof(uint64_t) * (size_t)N);
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
            }
        } else {
            if (type == 1) {
                int tmp = L->layers[ol][oi];
                L->layers[ol][oi] = L->layers[ol][oi2];
                L->layers[ol][oi2] = tmp;
            } else {
                L->S[ol][oi] = oold;
            }
            rebuild(L, g);
        }
    }
    return cost == 0;
}

static void lift_to_graph(const Lift *L, Graph *g) {
    g->n = L->N;
    int NA = L->k * L->G;
    for (int u = 0; u < g->n; u++) {
        g->side[u] = u >= NA;
        g->deg[u] = 0;
        for (int l = 0; l < d; l++) g->adj[u][g->deg[u]++] = nbr[l][u];
    }
}

/* Bandit over base sizes k in 1..MAXK. */
static long trials_k[MAXK + 1], wins_k[MAXK + 1];

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bestk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins_k[k] + 1.0) / (trials_k[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bestk = k; }
    }
    return bestk;
}

static void sa_phase(Graph *best, double until) {
    static Lift L;
    static Grp gr;
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int k = pick_k();
        int bn = best->n;
        int base = bn / (2 * k);
        int target = base + 1 + rndint(base / 8 + 2);
        if (target < d) target = d;
        if (!sample_group(target, &gr)) continue;
        int G = gr.m * gr.k;
        int N = 2 * k * G;
        if (N <= bn || (long)N > moore || N > MAXN) {
            if (++fails > 5000) break;
            continue;
        }
        L.k = k;
        L.G = G;
        L.N = N;
        trials_k[k]++;
        if (sa_trial(&L, &gr, until)) {
            lift_to_graph(&L, &cand);
            if (cand.n > best->n && is_valid(&cand)) {
                *best = cand;
                wins_k[k]++;
            }
        }
    }
}

/* ------------------------------------------------------------ grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if ((long)n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    *work = *best;
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = 0;
    work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    int got = 0;
    for (int tries = 0; got < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        got++;
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

static void grow_phase(Graph *best, double until) {
    static Graph work;
    while (now() < until && (long)best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) *best = work;
    }
}

/* ------------------------------------------------------------ main */

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
    double t_end = t0 + limit * 0.95 - 0.5;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1) {
        printf("1 0\n");
        return 0;
    }
    if (d == 1 || D < 2 || d > MAXDEG) {
        printf("2 1\n0 1\n");
        return 0;
    }

    static Graph gbest;
    read_start(&gbest);
    if (gbest.n == 0) complete_bipartite(&gbest);
    if (!is_valid(&gbest)) complete_bipartite(&gbest);

    if (gbest.n < moore_bound()) {
        double t_sa = t0 + (t_end - t0) * 0.85;
        sa_phase(&gbest, t_sa);
        grow_phase(&gbest, t_end);
    }
    if (!is_valid(&gbest)) complete_bipartite(&gbest);
    print_graph(&gbest);
    return 0;
}
'''


def _exact(d, D):
    """Exact constructions for D = 3 (Moore graph or Araujo-Pardo-Lopez record)."""
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if d == 1 or D == 1:
        return (2, [(0, 1)])

    # K_{d,d}: diameter 2, always valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    ex = None
    try:
        ex = _exact(d, D)
    except Exception:
        ex = None
    if ex is not None and ex[0] > best[0] and lib.is_valid(ex[0], ex[1], d, D):
        best = ex
        if D == 3 and lib.is_prime_power(d - 1):
            return best  # Moore graph: optimal, nothing to search

    if d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    start = best if best[0] > 2 * d else None
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
