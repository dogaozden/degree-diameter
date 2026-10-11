"""Direct-target bi-Cayley lift search.

Instead of hill-climbing a fixed group and growing the order by two, each attempt
picks a random semidirect group Z_m x| Z_k2 of an order just large enough for
best.n + 2 vertices, then runs simulated annealing on the darts (voltages and
layer permutations) until every representative reaches every vertex within D.
Any valid lift becomes the new best. Cost is computed on the 2k orbit representatives
only, which is exact because the group acts regularly on each side.

Fallbacks: a known algebraic start (projective plane or Araujo-Lopez) when available,
otherwise K_{d,d}. Python re-checks everything with lib.is_valid before returning.
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
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 4096
#define MAXK 4
#define MAXDART (MAXD * MAXK)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long moore;

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

static int gcd_i(int a, int b) {
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

static long compute_moore(void) {
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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D. */
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
        total += n - c;
    }
    return total / 2;
}

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------ input / output */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element (a,b) = a*k2+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK, GR;
static int RPt[MAXG];

static void set_group(int m, int k2, int r) {
    GM = m; GK = k2; GR = r;
    RPt[0] = 1 % m;
    for (int b = 1; b < k2; b++) RPt[b] = (int)((long)RPt[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int s = (int)(((long)a + (long)RPt[b] * c) % GM);
    int t = b + e;
    if (t >= GK) t -= GK;
    return s * GK + t;
}

/* Uniform random (m, k2, r) with m*k2 = N, gcd(r,m) = 1, r^k2 = 1 mod m. */
static void random_group(int N) {
    long cnt = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    set_group(bm, bk, br);
}

/* ------------------------------------------------------------ lifts */

static int K_, N_, nd_;
static int dI[MAXDART], dJ[MAXDART], dS[MAXDART];

static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

static int accept_move(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

/* Cost = 1e6 * duplicate darts + total unreached (representative, vertex) pairs.
   Representatives are A_i = i*N and B_j = (k+j)*N, i.e. every vertex index r*N, r < 2k. */
static long lift_cost(void) {
    int k = K_, N = N_, n = 2 * k * N, nd = nd_;
    long pen = 0;
    for (int t = 0; t < nd; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int g = 0; g < N; g++) {
            int a = dI[t] * N + g;
            int b = (k + dJ[t]) * N + gmul(g, dS[t]);
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    if (stampL > 1000000000) { memset(visL, 0, sizeof(visL)); stampL = 0; }
    long unreached = 0;
    for (int r = 0; r < 2 * k; r++) {
        stampL++;
        int head = 0, tail = 0;
        int src = r * N;
        visL[src] = stampL;
        qL[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qL[head++];
                for (int i = 0; i < degL[u]; i++) {
                    int v = adjL[u][i];
                    if (visL[v] != stampL) { visL[v] = stampL; qL[tail++] = v; }
                }
            }
        }
        unreached += n - tail;
    }
    return pen * 1000000L + unreached;
}

static void random_darts(void) {
    int k = K_, N = N_;
    nd_ = d * k;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(N);
        }
    }
}

/* Simulated annealing on the current darts. Returns final cost (0 = valid lift). */
static long anneal(long steps, double until) {
    int k = K_, N = N_, nd = nd_;
    long c = lift_cost();
    const double T0 = 1.2, T1 = 0.03;
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        if (k > 1 && rnd01() < 0.25) {
            int l = rndint(d), a = rndint(k), b = rndint(k);
            if (a == b) continue;
            int t1 = l * k + a, t2 = l * k + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (accept_move(c2 - c, T)) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(nd);
            int old = dS[t];
            int nv = rndint(N);
            if (nv == old) continue;
            dS[t] = nv;
            long c2 = lift_cost();
            if (accept_move(c2 - c, T)) c = c2;
            else dS[t] = old;
        }
    }
    return c;
}

static void build_lift(Graph *g) {
    int k = K_, N = N_;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (k + dJ[t]) * N + gmul(x, dS[t]));
}

/* ------------------------------------------------------------ search */

static Graph best, cand;

/* Repeatedly target order best.n + 2 with a fresh random group and annealed lift. */
static void lift_search(double until) {
    static const int kc[8] = {1, 1, 1, 2, 2, 3, 4, 2};
    int fails = 0, consec = 0;
    while (now() < until && best.n + 2 <= moore) {
        int target = best.n + 2;
        int k = kc[rndint(8)];
        long N = (target + 2L * k - 1) / (2L * k) + rndint(3);
        long nv = 2L * k * N;
        if (N < 1 || N > MAXG || nv > moore || nv > MAXN) {
            if (++fails > 200000) return;
            continue;
        }
        K_ = k;
        N_ = (int)N;
        random_group((int)N);
        random_darts();
        long mult = 1 + consec / 10;
        if (mult > 8) mult = 8;
        long c = anneal(60000L * mult, until);
        if (c == 0) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
            consec = 0;
        } else {
            consec++;
        }
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
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) lift_search(t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= lib.moore_bound(d, D):
        return best

    # C runs on its own clock (95% of its argument); keep a margin for compile and startup.
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 4)
        consider(lib.parse_graph_text(text))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
