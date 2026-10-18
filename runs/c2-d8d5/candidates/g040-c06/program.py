"""Orbit-representative lift search: voltage annealing over semidirect-product lifts of small base graphs."""
import itertools
import random
import time

import lib


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
# C engine.
#
# Lift model: base multigraph on P+P vertices (d-regular), group G = Z_m x| Z_k
# of order N, dart (i, j, g) joins A(i,x) to B(j, x*g). Left multiplication by
# any h in G is an automorphism, so the graph is vertex-transitive inside each
# of the 2P blocks. Validity therefore reduces to BFS from 2P representatives,
# which is far cheaper than an all-pairs check. Voltages and base edges are
# annealed to drive the unreached count to zero. Successful lifts are checked
# with a full all-pairs validation before they are accepted.
# ----------------------------------------------------------------------------

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
#define MAXP 6
#define MAXG (MAXN / 2)
#define MAXDARTS (MAXP * MAXD)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (full all-pairs check). */
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

/* ---- group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
typedef struct {
    int m, k, r, N;
    int rp[MAXG];
} Grp;

static Grp G;

static int gmul(int x, int y) {
    int a = x / G.k, b = x % G.k, c = y / G.k, e = y % G.k;
    return (int)((a + (long)G.rp[b] * c) % G.m) * G.k + (b + e) % G.k;
}

/* Inverse: (a,b)^-1 = (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / G.k, b = x % G.k;
    int nb = (G.k - b) % G.k;
    long c = (G.m - (long)G.rp[nb] * a % G.m) % G.m;
    return (int)(c * G.k + nb);
}

/* Pick a random semidirect group of order N (uniform over candidate (m,k,r)). */
static int random_group(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 2; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    count++;
    if (rndint((int)count) == 0) { bm = 1; bk = N; br = 0; }
    G.m = bm;
    G.k = bk;
    G.r = br;
    G.N = N;
    G.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G.rp[b] = (int)((long)G.rp[b - 1] * br % bm);
    return 1;
}

/* ---- lift state ---- */
static int P, NG, ND;
static int DA[MAXDARTS], DB[MAXDARTS], DG[MAXDARTS], DGI[MAXDARTS];
static int LA[MAXP][MAXD], LB[MAXP][MAXD];

static void rebuild_lists(void) {
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < ND; t++) {
        LA[DA[t]][ca[DA[t]]++] = t;
        LB[DB[t]][cb[DB[t]]++] = t;
    }
}

/* Random d-regular base multigraph on P+P vertices, as a sum of d permutation matrices. */
static int make_base(int p, int M[MAXP][MAXP]) {
    for (int tries = 0; tries < 200; tries++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP];
        memset(seen, 0, sizeof seen);
        int stack[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; ns++; stack[top++] = u; }
            }
        }
        if (ns == 2 * p) return 1;
    }
    return 0;
}

static int dup_dart(int t) {
    for (int s = 0; s < ND; s++)
        if (s != t && DA[s] == DA[t] && DB[s] == DB[t] && DG[s] == DG[t]) return 1;
    return 0;
}

static int init_lift(int p) {
    int M[MAXP][MAXP];
    if (!make_base(p, M)) return 0;
    ND = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                DA[ND] = i;
                DB[ND] = j;
                int g;
                for (;;) {
                    g = rndint(NG);
                    int clash = 0;
                    for (int s = 0; s < ND; s++)
                        if (DA[s] == i && DB[s] == j && DG[s] == g) { clash = 1; break; }
                    if (!clash) break;
                }
                DG[ND] = g;
                DGI[ND] = ginv(g);
                ND++;
            }
    P = p;
    rebuild_lists();
    return 1;
}

/* BFS from one representative vertex; returns the number of vertices within distance D. */
static int vis[MAXN], queue_[MAXN];
static int vstamp = 0;

static int reach_count(int src) {
    int half = P * NG;
    vstamp++;
    int head = 0, tail = 0;
    vis[src] = vstamp;
    queue_[tail++] = src;
    for (int dist = 0; dist < D && head < tail; dist++) {
        int end = tail;
        while (head < end) {
            int v = queue_[head++];
            if (v < half) {
                int i = v / NG, x = v - i * NG;
                for (int q = 0; q < d; q++) {
                    int t = LA[i][q];
                    int u = half + DB[t] * NG + gmul(x, DG[t]);
                    if (vis[u] != vstamp) { vis[u] = vstamp; queue_[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / NG, y = w - j * NG;
                for (int q = 0; q < d; q++) {
                    int t = LB[j][q];
                    int u = DA[t] * NG + gmul(y, DGI[t]);
                    if (vis[u] != vstamp) { vis[u] = vstamp; queue_[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2P representatives of unreached vertices; zero iff the lift is valid. */
static long eval_cost(void) {
    long V = 2L * P * NG, cost = 0;
    for (int i = 0; i < P; i++) {
        cost += V - reach_count(i * NG);
        cost += V - reach_count(P * NG + i * NG);
    }
    return cost;
}

static void build_full(Graph *g) {
    int half = P * NG;
    g->n = 2 * half;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= half; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < NG; x++)
            add_edge(g, DA[t] * NG + x, half + DB[t] * NG + gmul(x, DG[t]));
}

/* Anneal voltages and base edges. Returns final cost (0 = valid lift), or -1 if setup failed. */
static long try_lift(int p, long steps) {
    if (!init_lift(p)) return -1;
    long cur = eval_cost();
    double c0 = cur > 0 ? (double)cur : 1.0;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) break;
        double T = 0.3 + (1.0 + 0.02 * c0) * (1.0 - (double)s / (double)steps);
        if (P > 1 && rnd01() < 0.2) {
            int t1 = rndint(ND), t2 = rndint(ND);
            if (DA[t1] == DA[t2] || DB[t1] == DB[t2]) continue;
            int j1 = DB[t1], j2 = DB[t2];
            DB[t1] = j2;
            DB[t2] = j1;
            if (dup_dart(t1) || dup_dart(t2)) { DB[t1] = j1; DB[t2] = j2; continue; }
            rebuild_lists();
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                DB[t1] = j1;
                DB[t2] = j2;
                rebuild_lists();
            }
        } else {
            int t = rndint(ND);
            int old = DG[t];
            int g = rndint(NG);
            if (g == old) continue;
            DG[t] = g;
            DGI[t] = ginv(g);
            if (dup_dart(t)) { DG[t] = old; DGI[t] = ginv(old); continue; }
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                DG[t] = old;
                DGI[t] = ginv(old);
            }
        }
    }
    return cur;
}

static void lift_search(Graph *best) {
    static Graph cand;
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    while (now() < t_end) {
        long target = best->n + 2;
        if (target > moore) break;
        int r = rndint(12);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : r < 10 ? 4 : r < 11 ? 5 : 6;
        long N = (target + 2L * p - 1) / (2L * p) + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > MAXN || N > MAXG) continue;
        if (!random_group((int)N)) continue;
        long cur = try_lift(p, 6000);
        if (cur == 0) {
            build_full(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    if (d < 1 || d > 30) { printf("0 0\n"); return 0; }
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2) lift_search(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the current best if (n, e) is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2 or d > 30:
        return best

    # Exact constructions.
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

    # Search engine: orbit-representative voltage annealing, seeded by the best graph so far.
    c_budget = end - time.monotonic() - 1.0
    if c_budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=best, timeout=c_budget + 8)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
