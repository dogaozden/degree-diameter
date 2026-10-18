"""Combined program: exact starts in Python, then one C engine.

The C engine runs two phases on a valid start graph:
1. Bi-Cayley lift annealing over Z_m x| Z_k2 (from the fast bitset engine), with
   reach masks computed from the 2K block identities.
2. Grow-by-two annealing on the best full graph, with bitset diameter checks.

Python builds the exact or structured starts (projective planes, Araujo-Pardo-Lopez,
W(q) for D = 4, K_{d,d}, cycles), passes the best one to C, and validates the output
with lib.is_valid before returning it.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 64
#define MAXW (MAXN / 64)
#define KMAX 6
#define PEN 1000.0
#define ITERS 12000
#define PATIENCE 2500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int dd, DD;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

static int popc32(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555u);
    x = (x & 0x33333333u) + ((x >> 2) & 0x33333333u);
    x = (x + (x >> 4)) & 0x0F0F0F0Fu;
    return (int)((x * 0x01010101u) >> 24);
}

static long long moore_bound(void) {
    if (DD <= 0 || dd <= 0) return 1;
    if (dd == 1) return 2;
    if (dd == 2) return 2LL * DD;
    long long s = 0, p = 1;
    for (int i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 100000000LL) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ graph basics */

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > DD. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DD; r++) {
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
        for (int w = 0; w < W; w++) c += popc32((uint32_t)s[w]) + popc32((uint32_t)(s[w] >> 32));
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > dd) return 0;
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
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
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
                    g->side[u] = (unsigned char)(1 - g->side[v]);
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
    g->n = 2 * dd;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= dd; }
    for (int a = 0; a < dd; a++)
        for (int b = 0; b < dd; b++) add_edge(g, a, dd + b);
}

/* ------------------------------------------------------- semidirect groups */

/* Group Z_gm x| Z_gk2, element a*gk2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gm, gk2, Gord, K, NV, LL;
static int pw[64];

static int gmul(int x, int y) {
    int a1 = x / gk2, b1 = x % gk2, a2 = y / gk2, b2 = y % gk2;
    int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % gm);
    int b = (b1 + b2) % gk2;
    return a * gk2 + b;
}

static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long t = ((long long)pw[nb] * a) % gm;
    int na = (int)((gm - t) % gm);
    return na * gk2 + nb;
}

static void sample_group(int target, int *om, int *ok2, int *orr) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int att = 0; att < 200; att++) {
        int k2 = K2S[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = (m >= 3) ? m - 1 : 1;
        } else {
            r = -1;
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    int c = 2 + rndint(m - 2);
                    if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
            if (r < 0) continue;
        }
        *om = m; *ok2 = k2; *orr = r;
        return;
    }
    *om = (target < 2) ? 2 : target;
    *ok2 = 1;
    *orr = 1;
}

static void setup_group(int m, int k2, int r, int k) {
    gm = m; gk2 = k2; Gord = m * k2;
    K = k; LL = dd; NV = 2 * K * Gord;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
}

/* ------------------------------------------------------------- lift engine */

static int lay[MAXD * KMAX], ilay[MAXD * KMAX], vol[MAXD * KMAX];
static int nbr[MAXD * MAXN];
static uint32_t bufA[MAXN], bufB[MAXN], scrA[MAXN], scrB[MAXN];
static uint32_t *stR = bufA, *candR = bufB;
static double sa_deadline = 0.0;
static int trials[KMAX + 1], wins[KMAX + 1];

static void set_dart(int l, int i) {
    int j = lay[l * K + i], s = vol[l * K + i];
    int is = ginv(s);
    int *nb = nbr + (size_t)l * NV;
    for (int g = 0; g < Gord; g++) {
        nb[i * Gord + g] = (K + j) * Gord + gmul(g, s);
        nb[(K + j) * Gord + g] = i * Gord + gmul(g, is);
    }
}

static void swap_lay(int l, int i1, int i2) {
    int *lp = lay + l * K;
    int *ip = ilay + l * K;
    int j1 = lp[i1], j2 = lp[i2];
    lp[i1] = j2; lp[i2] = j1;
    ip[j2] = i1; ip[j1] = i2;
}

static void random_init(void) {
    int perm[KMAX];
    for (int l = 0; l < LL; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l * K + i] = perm[i];
            ilay[l * K + perm[i]] = i;
            vol[l * K + i] = rndint(Gord);
        }
    }
    for (int l = 0; l < LL; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < LL; l1++)
            for (int l2 = l1 + 1; l2 < LL; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i]) c++;
    return c;
}

static double total_cost(const uint32_t *r) {
    long long s = 0;
    for (int v = 0; v < NV; v++) s += 2 * K - popc32(r[v]);
    return (double)s + PEN * (double)dupcount();
}

/* Reach masks after DD rounds: bit b of out[v] = identity of block b within DD of v. */
static void compute_reach(uint32_t *out) {
    uint32_t *X = scrA, *Y = scrB;
    memset(X, 0, sizeof(uint32_t) * (size_t)NV);
    for (int b = 0; b < 2 * K; b++) X[(size_t)b * Gord] = 1u << b;
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint32_t x = X[v];
            for (int l = 0; l < LL; l++) x |= X[nbr[(size_t)l * NV + v]];
            Y[v] = x;
            changed |= (x != X[v]);
        }
        uint32_t *tmp = X; X = Y; Y = tmp;
        if (!changed) break;
    }
    memcpy(out, X, sizeof(uint32_t) * (size_t)NV);
}

static int accept(double c2, double c, double temp) {
    if (c2 <= c) return 1;
    return rnd01() < exp(-(c2 - c) / temp);
}

static int sa_run(void) {
    random_init();
    compute_reach(stR);
    double cost = total_cost(stR);
    double c0 = cost > 1.0 ? cost : 1.0;
    double bestc = cost;
    long last = 0;
    uint32_t full = (uint32_t)((1ULL << (2 * K)) - 1ULL);

    for (long t = 0; t < ITERS; t++) {
        if (cost == 0.0) break;
        if (t - last > PATIENCE) break;
        if ((t & 31) == 0 && now() > sa_deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(LL);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_lay(l, i1, i2);
            set_dart(l, i1);
            set_dart(l, i2);
            compute_reach(candR);
            double c2 = total_cost(candR);
            if (accept(c2, cost, temp)) {
                uint32_t *tmp = stR; stR = candR; candR = tmp;
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                swap_lay(l, i1, i2);
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int off = rndint(NV);
            for (int q = 0; q < NV; q++) {
                int v = off + q;
                if (v >= NV) v -= NV;
                if (stR[v] != full) {
                    int b = v / Gord;
                    l = rndint(LL);
                    if (b < K) i = b;
                    else i = ilay[l * K + (b - K)];
                    break;
                }
            }
        }
        if (l < 0) {
            l = rndint(LL);
            i = rndint(K);
        }
        int old = vol[l * K + i];
        int nw = rndint(Gord);
        if (nw == old) continue;
        vol[l * K + i] = nw;
        set_dart(l, i);
        compute_reach(candR);
        double c2 = total_cost(candR);
        if (accept(c2, cost, temp)) {
            uint32_t *tmp = stR; stR = candR; candR = tmp;
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            vol[l * K + i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0.0;
}

static int pick_K(void) {
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

static void build_graph(Graph *g) {
    int half = K * Gord;
    g->n = NV;
    for (int v = 0; v < NV; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= half);
    }
    for (int u = 0; u < half; u++)
        for (int l = 0; l < LL; l++) add_edge(g, u, nbr[(size_t)l * NV + u]);
}

static void lift_loop(Graph *best, double until) {
    static Graph cand;
    long long moore = moore_bound();
    sa_deadline = until;
    while (now() < until) {
        int k = pick_K();
        int base = best->n / (2 * k);
        int spread = base / 8 + 1;
        if (spread < 2) spread = 2;
        int target = base + 1 + rndint(spread);
        if (target < 2) target = 2;
        int m, k2, r;
        sample_group(target, &m, &k2, &r);
        long long nv = 2LL * k * m * k2;
        if (nv <= best->n || nv > MAXN || nv > moore) continue;
        trials[k]++;
        setup_group(m, k2, r, k);
        if (sa_run()) {
            wins[k]++;
            build_graph(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------ grow-by-two phase */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > MAXN || n + 2 > moore_bound()) return 0;
    copy_graph(work, best);
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
    used[x] = stamp;
    used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < dd - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = stamp;
        used[b] = stamp;
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
    static Graph w;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 3.0 ? left : left / 3.0;
        if (slice < 0.05) break;
        if (grow_once(best, &w, now() + slice)) copy_graph(best, &w);
    }
}

/* ------------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_all = t0 + limit * 0.92;
    rs = (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    static Graph bestG;
    if (dd < 1 || dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    read_start(&bestG);
    if (DD < 2) {
        if (bestG.n == 0) { printf("0 0\n"); return 0; }
        print_graph(&bestG);
        return 0;
    }
    if (bestG.n == 0) complete_bipartite(&bestG);

    double t_lift = now() + (t_all - now()) * 0.88;
    lift_loop(&bestG, t_lift);
    if (bestG.n + 2 <= moore_bound()) grow_search(&bestG, t_all);

    if (!is_valid(&bestG)) complete_bipartite(&bestG);
    print_graph(&bestG);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts (Python).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = float(time_limit)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: degree 2, diameter D, bipartite
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Exact and structured starts.
    pg = _best_pg(d)
    consider(pg)
    if D == 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if pg is not None and lib.is_prime_power(d - 1):
            return best
    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if best[0] >= lib.moore_bound(d, D):
        return best

    # C engine: lift annealing, then grow-by-two, from the best start.
    elapsed = time.monotonic() - t0
    budget = 0.80 * T - elapsed - 2.5  # margin for compilation and output
    if budget >= 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, int(seed) % (1 << 31), round(budget, 2)],
                             stdin_graph=best, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(text)
            consider((n, e))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
