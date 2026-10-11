"""Bold variant: bi-Cayley voltage lifts over semidirect groups Z_m x| Z_k with
K in {1,2,3,4} vertices per side, searched by simulated annealing over shifts and
per-layer matchings. Every candidate is re-verified in C and in Python. The start
is the best known direct construction, falling back to K_{d,d}, so output is always valid."""
import time

import lib

C_SOURCE = r'''
/* Voltage-lift search for bipartite degree-diameter graphs.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (valid start), or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Model: group G = Z_M x| Z_KK (order GN), K vertices per side.
 *   A_{i,g} ~ B_{j,g*s} for each dart (i,j,s). Each layer l gives one dart per i
 *   with a permutation of j, so every vertex has degree d.
 *   Left multiplication is an automorphism, so diameter <= D is equivalent to
 *   every representative (A_i or B_j) reaching all vertices within D steps.
 * Search: simulated annealing on shifts and per-layer matchings, cost =
 *   1e6 * duplicate darts + unreached (representative, vertex) pairs.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXK 4
#define MAXG 1024

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static int cap_n;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
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

/* ------------------------------------------------------------ BFS */

static int vis_[MAXN];
static int vst_ = 0;
static int q_[MAXN];

/* Number of vertices reached from s within lim steps (including s). */
static int reach(int (*adj)[MAXD], const int *deg, int s, int lim) {
    vst_++;
    if (vst_ >= 1000000000) {
        memset(vis_, 0, sizeof(vis_));
        vst_ = 1;
    }
    int head = 0, tail = 0;
    vis_[s] = vst_;
    q_[tail++] = s;
    for (int lev = 0; lev < lim && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = q_[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (vis_[v] != vst_) {
                    vis_[v] = vst_;
                    q_[tail++] = v;
                }
            }
        }
    }
    return tail;
}

/* ------------------------------------------------------------ graph basics */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* Simple, bipartite by side labels, degree <= d, diameter <= D. */
static int full_check(Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < n; s++)
        if (reach(g->adj, g->deg, s, D) != n) return 0;
    return 1;
}

static int read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 0; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return 0;
        }
        add_edge(g, u, v);
    }
    static int col[MAXN], qu[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        qu[tail++] = s;
        while (head < tail) {
            int v = qu[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (col[u] == -1) {
                    col[u] = 1 - col[v];
                    qu[tail++] = u;
                } else if (col[u] == col[v]) {
                    g->n = 0;
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) g->side[v] = (unsigned char)col[v];
    if (!full_check(g)) {
        g->n = 0;
        return 0;
    }
    return 1;
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
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= d);
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_GM x| Z_GKK, element (a,b) coded as a*GKK+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int GM, GKK, GN;
static int RP[MAXG];

static void set_group(int m, int kk, int r) {
    GM = m;
    GKK = kk;
    GN = m * kk;
    for (int b = 0; b < kk; b++) RP[b] = (int)powmod_l(r, b, m);
}

static int gmul(int x, int y) {
    int a = x / GKK, b = x % GKK, c = y / GKK, e = y % GKK;
    int aa = (a + RP[b] * c) % GM;
    return aa * GKK + (b + e) % GKK;
}

/* Uniform over all valid (m, r) for order N: gcd(r,m)=1, r^kk = 1 mod m. */
static void random_group(int N) {
    int cnt = 0, bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int kk = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, kk, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { bm = m; bk = kk; br = r; }
        }
    }
    set_group(bm, bk, br);
}

/* ------------------------------------------------------------ lifts */

static int K;               /* vertices per side in the base graph */
static int nd;              /* number of darts = d*K */
static int dI[MAXD * MAXK], dJ[MAXD * MAXK], dS[MAXD * MAXK];
static int ladj[MAXN][MAXD], ldeg[MAXN];

/* Layer l: a permutation of j's, so every A_i and every B_j has degree d. */
static void init_darts(void) {
    nd = d * K;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(GN);
        }
    }
}

static long lift_cost(void) {
    int n = 2 * K * GN;
    long pen = 0;
    for (int t = 0; t < nd; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    for (int v = 0; v < n; v++) ldeg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < GN; x++) {
            int a = dI[t] * GN + x;
            int b = (K + dJ[t]) * GN + gmul(x, dS[t]);
            ladj[a][ldeg[a]++] = b;
            ladj[b][ldeg[b]++] = a;
        }
    long unr = 0;
    for (int r = 0; r < 2 * K; r++)
        unr += n - reach(ladj, ldeg, r * GN, D);
    return pen * 1000000L + unr;
}

static void build_graph(Graph *g) {
    int n = 2 * K * GN;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= K * GN);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < GN; x++)
            add_edge(g, dI[t] * GN + x, (K + dJ[t]) * GN + gmul(x, dS[t]));
}

/* Simulated annealing on one random group. Returns 1 if cost reaches 0. */
static int lift_attempt(int steps, double until) {
    init_darts();
    long c = lift_cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = 0.6 * (1.0 - (double)s / steps) + 0.03;
        if (K > 1 && rnd01() < 0.4) {
            int l = rndint(d), a = rndint(K), b = rndint(K);
            if (a == b) continue;
            int t1 = l * K + a, t2 = l * K + b;
            int tmp = dJ[t1];
            dJ[t1] = dJ[t2];
            dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else {
                tmp = dJ[t1];
                dJ[t1] = dJ[t2];
                dJ[t2] = tmp;
            }
        } else {
            int t = rndint(nd);
            int old = dS[t];
            int nw = rndint(GN);
            if (nw == old) continue;
            dS[t] = nw;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

/* ------------------------------------------------------------ search driver */

static Graph best, cand;

static void lift_search(double until) {
    static const int kset[6] = {1, 1, 2, 2, 3, 4};
    long fails = 0;
    while (now() < until && best.n + 2 <= cap_n) {
        int k = kset[rndint(6)];
        int target = best.n + 2;
        int Nmin = (target + 2 * k - 1) / (2 * k);
        int N = Nmin + rndint(3);
        if (2 * k * N > cap_n) N = Nmin;
        if (2 * k * N > cap_n || N > MAXG || N < 1) {
            if (++fails > 100000) break;
            continue;
        }
        K = k;
        random_group(N);
        if (lift_attempt(30000, until)) {
            build_graph(&cand);
            if (cand.n > best.n && full_check(&cand)) best = cand;
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
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long mc = compute_moore();
    cap_n = mc < MAXN ? (int)mc : MAXN;

    if (!read_start(&best)) complete_bipartite(&best);
    if (best.n < cap_n) lift_search(t_end);
    if (!full_check(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family
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

    try:
        consider(_known_start(d, D))
    except (ValueError, StopIteration):
        pass

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = time_limit - (time.monotonic() - t0)
    budget = 0.85 * remaining - 2.0
    if budget < 2.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
