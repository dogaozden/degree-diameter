"""Group-symmetric bi-lift search. Non-abelian semidirect lifts of small bases are annealed,
checking only one BFS per fibre representative (left multiplication is an automorphism)."""
import itertools
import time

import lib


C_SOURCE = r'''
/* Group-symmetric bipartite lift search for degree-diameter graphs.
 * A lift of a p-fibre base over a group G of order N has 2pN vertices. Left
 * multiplication by any group element is an automorphism of the lift, so the
 * distance profile is identical across each fibre. Checking one BFS per fibre
 * representative (2p BFS runs) therefore decides diameter <= D for the whole graph.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 48
#define MAXW (MAXN / 64)
#define MAXP 8
#define PATIENCE 30000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best;
static Graph cand;

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------- group Z_m x|_r Z_k, element (a,b) coded as a*k+b ---------------- */

typedef struct {
    int m, k, r;
    int rp[MAXN];   /* rp[b] = r^b mod m */
} Grp;

static Grp GG;
static int INV[MAXN];

static void set_group(int m, int k, int r) {
    GG.m = m;
    GG.k = k;
    GG.r = r;
    GG.rp[0] = 1 % m;
    for (int b = 1; b < k; b++) GG.rp[b] = (int)((long)GG.rp[b - 1] * r % m);
}

/* (a,b)(c,e) = (a + r^b c, b + e). Identity is element 0. */
static int gmul(int x, int y) {
    int k = GG.k, m = GG.m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int t = (int)((a + (long)GG.rp[b] * c) % m);
    return t * k + (b + e) % k;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int k = GG.k, m = GG.m;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    int c = (int)((m - (long)GG.rp[nb] * a % m) % m);
    return c * k + nb;
}

static void random_group(int N) {
    int divs[128], nd = 0;
    for (int k = 1; k <= N && nd < 128; k++)
        if (N % k == 0) divs[nd++] = k;
    int k = divs[rndint(nd)];
    int m = N / k;
    if (k == 1 || m < 3) { set_group(m, k, 1); return; }
    for (int tries = 0; tries < 200; tries++) {
        int r = 2 + rndint(m - 2);
        if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) { set_group(m, k, r); return; }
    }
    set_group(m, k, 1);
}

/* ---------------- lift state ---------------- */

static int P_, N_, NL;
static int sig[MAXD][MAXP];   /* B-fibre hit by A-fibre i in layer l */
static int val[MAXD][MAXP];   /* voltage of that dart */
static int isig[MAXD][MAXP];  /* A-fibre hitting B-fibre j in layer l */
static unsigned int vis[MAXN];
static unsigned int vstamp = 0;
static int bq[MAXN];

static int dup_dart(int l, int i) {
    for (int l2 = 0; l2 < NL; l2++)
        if (l2 != l && sig[l2][i] == sig[l][i] && val[l2][i] == val[l][i]) return 1;
    return 0;
}

static void swap_targets(int l, int i1, int i2) {
    int t = sig[l][i1];
    sig[l][i1] = sig[l][i2];
    sig[l][i2] = t;
    isig[l][sig[l][i1]] = i1;
    isig[l][sig[l][i2]] = i2;
}

static void random_init(int p) {
    for (int l = 0; l < NL; l++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            sig[l][i] = perm[i];
            isig[l][perm[i]] = i;
        }
    }
    for (int l = 0; l < NL; l++)
        for (int i = 0; i < p; i++) {
            do { val[l][i] = rndint(N_); } while (dup_dart(l, i));
        }
}

/* Cost = total unreached (source, target) pairs over the 2p fibre representatives. */
static long lift_cost(void) {
    int p = P_, N = N_, V = 2 * p * N, base = p * N;
    long cost = 0;
    if (vstamp >= 4000000000u) { memset(vis, 0, sizeof(vis)); vstamp = 0; }
    for (int f = 0; f < 2 * p; f++) {
        int src = f * N;
        vstamp++;
        int head = 0, tail = 0;
        bq[tail++] = src;
        vis[src] = vstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int level_end = tail;
            while (head < level_end) {
                int u = bq[head++];
                if (u < base) {
                    int i = u / N, x = u % N;
                    for (int l = 0; l < NL; l++) {
                        int w = base + sig[l][i] * N + gmul(x, val[l][i]);
                        if (vis[w] != vstamp) { vis[w] = vstamp; bq[tail++] = w; }
                    }
                } else {
                    int b = u - base, j = b / N, y = b % N;
                    for (int l = 0; l < NL; l++) {
                        int i = isig[l][j];
                        int w = i * N + gmul(y, INV[val[l][i]]);
                        if (vis[w] != vstamp) { vis[w] = vstamp; bq[tail++] = w; }
                    }
                }
            }
        }
        cost += V - tail;
    }
    return cost;
}

/* Simulated annealing on voltages and within-layer target swaps. Returns 1 on success. */
static int anneal(double deadline) {
    int p = P_, N = N_;
    random_init(p);
    long cost = lift_cost();
    long best_cost = cost;
    long since = 0;
    double T = 0.5 + 3.0 * rnd01();
    long it = 0;
    while (cost > 0) {
        if ((++it & 31) == 0 && now() > deadline) return 0;
        if (++since > PATIENCE) return 0;
        T *= 0.99998;
        if (T < 0.15) T = 0.15;
        int l = rndint(NL);
        if (p < 2 || rndint(10) < 6) {
            int i = rndint(p);
            int old = val[l][i];
            int nv = rndint(N);
            if (nv == old) continue;
            val[l][i] = nv;
            if (dup_dart(l, i)) { val[l][i] = old; continue; }
            long nc = lift_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) cost = nc;
            else val[l][i] = old;
        } else {
            int i1 = rndint(p), i2 = rndint(p - 1);
            if (i2 >= i1) i2++;
            swap_targets(l, i1, i2);
            if (dup_dart(l, i1) || dup_dart(l, i2)) { swap_targets(l, i1, i2); continue; }
            long nc = lift_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) cost = nc;
            else swap_targets(l, i1, i2);
        }
        if (cost < best_cost) { best_cost = cost; since = 0; }
    }
    return 1;
}

static void build_lift(Graph *g, int p, int N) {
    int base = p * N;
    g->n = 2 * base;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= base; }
    for (int l = 0; l < NL; l++)
        for (int i = 0; i < p; i++) {
            int j = sig[l][i], v = val[l][i];
            for (int x = 0; x < N; x++)
                add_edge(g, i * N + x, base + j * N + gmul(x, v));
        }
}

static void lift_search(double until) {
    long moore = moore_bound();
    long fails = 0;
    while (now() < until) {
        if (best.n + 2 > moore) return;
        int pick = rndint(100);
        int p = pick < 8 ? 1 : pick < 28 ? 2 : pick < 58 ? 3 : pick < 85 ? 4 : pick < 95 ? 5 : 6;
        long N = best.n / (2L * p) + 1 + rndint(3);
        if (N < d || 2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 100000) return;
            continue;
        }
        P_ = p;
        N_ = (int)N;
        NL = d;
        random_group(N_);
        for (int x = 0; x < N_; x++) INV[x] = ginv(x);
        double attempt_end = now() + 1.5 + 2.5 * rnd01();
        if (attempt_end > until) attempt_end = until;
        if (anneal(attempt_end)) {
            build_lift(&cand, p, N_);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
        }
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d >= MAXD || 2 * d > MAXN) {
        printf("0 0\n");
        return 0;
    }
    if (D == 1) {
        best.n = 2;
        best.deg[0] = best.deg[1] = 0;
        best.side[0] = 0;
        best.side[1] = 1;
        add_edge(&best, 0, 1);
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (d >= 2) lift_search(t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the best graph if the candidate is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 6)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
