"""Bipartite Cayley-graph search. Exact small constructions first, then a C engine that
searches connection sets S in semidirect-product groups G (|G| = N), where A_x ~ B_{x*s}
for s in S. Diameter is checked by two BFS runs (from A_e and B_e), and the order N
climbs with simulated annealing on the number of unreached pairs."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: bipartite Cayley graphs over semidirect products Z_m x| Z_k.
# Vertices A_x = x and B_y = N + y. Edge A_x ~ B_{x*s} for each s in S.
# Left multiplication is an automorphism, so the diameter test reduces to
# two BFS runs from A_e and B_e. Annealing moves one connection element at a time.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite Cayley-graph search.
 * Usage: prog d D seed time_limit N0
 * stdin is ignored. stdout: "n m" + edges, the largest valid graph found,
 * or K_{d,d} when nothing better is found.
 */
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
#define MAXG 2048
#define MAXGROUPS 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int m, k, r; } GDesc;

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

/* Number of unordered pairs at distance > D. */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
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
        uint64_t *t = cur; cur = nxt; nxt = t;
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

/* Group multiplication tables. T[s][x] = x*s; element (a,b) is coded a*k+b. */
static int T[MAXG][MAXG];
static int INV[MAXG];
static int A1[MAXG], B1[MAXG], RP[MAXG];

static int enum_groups(int N, GDesc *out, int cap) {
    int c = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < cap) { out[c].m = m; out[c].k = k; out[c].r = r; c++; }
        }
    }
    return c;
}

static void build_group(int N, const GDesc *g) {
    int m = g->m, k = g->k, r = g->r;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) { A1[x] = x / k; B1[x] = x % k; }
    for (int s = 0; s < N; s++) {
        int a2 = s / k, b2 = s % k;
        for (int x = 0; x < N; x++) {
            int a = (int)((A1[x] + (long)RP[B1[x]] * a2) % m);
            int b = (B1[x] + b2) % k;
            T[s][x] = a * k + b;
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int s = 0; s < N; s++)
            if (T[s][x] == 0) { INV[x] = s; break; }
    }
}

/* Connection set S (size d) and neighbour tables:
 * NA[x*d+i] = B-index of A_x through S[i]; NB[y*d+i] = A-index of B_y through S[i]. */
static int S[MAXD];
static int NA[MAXG * MAXD], NB[MAXG * MAXD];

static void set_col(int N, int i, int s) {
    S[i] = s;
    const int *row = T[s];
    const int *rowi = T[INV[s]];
    for (int x = 0; x < N; x++) {
        NA[x * d + i] = row[x];
        NB[x * d + i] = rowi[x];
    }
}

static int visv[2][MAXG];
static int gen_ = 0;
static int frA[2 * MAXG], nxA[2 * MAXG];

/* Number of vertices within distance D of (side0, x0). */
static int ball(int side0, int x0) {
    gen_++;
    int nf = 0, cnt = 1;
    visv[side0][x0] = gen_;
    frA[nf++] = side0 * MAXG + x0;
    for (int lvl = 0; lvl < D && nf > 0; lvl++) {
        int nn = 0;
        for (int t = 0; t < nf; t++) {
            int code = frA[t];
            int side = code >= MAXG;
            int x = code - side * MAXG;
            const int *nb = (side ? NB : NA) + (long)x * d;
            int os = 1 - side;
            for (int i = 0; i < d; i++) {
                int y = nb[i];
                if (visv[os][y] != gen_) {
                    visv[os][y] = gen_;
                    nxA[nn++] = os * MAXG + y;
                    cnt++;
                }
            }
        }
        memcpy(frA, nxA, sizeof(int) * nn);
        nf = nn;
    }
    return cnt;
}

/* Number of unreached (vertex, source) pairs; zero iff the graph has diameter <= D. */
static long cost_of(int N) {
    return (long)(2 * N - ball(0, 0)) + (long)(2 * N - ball(1, 0));
}

static int pick_fresh(int N) {
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int j = 0; j < d; j++)
            if (S[j] == g) { ok = 0; break; }
        if (ok) return g;
    }
}

static int anneal(int N, long maxit) {
    for (int i = 0; i < d; i++) {
        int g, ok;
        do {
            g = rndint(N); ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == g) { ok = 0; break; }
        } while (!ok);
        set_col(N, i, g);
    }
    long cost = cost_of(N);
    if (cost == 0) return 1;
    if (N <= d) return 0;
    double T0 = 1.0 + 0.02 * (double)cost;
    for (long it = 0; it < maxit; it++) {
        if ((it & 127) == 0 && now() > t_end) break;
        double temp = T0 * (1.0 - (double)it / (double)maxit) + 0.05;
        int i = rndint(d);
        int old = S[i];
        set_col(N, i, pick_fresh(N));
        long c2 = cost_of(N);
        long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            set_col(N, i, old);
        }
    }
    return cost == 0;
}

static Graph best, cand;
static GDesc groups[MAXGROUPS];

static void build_graph(Graph *g, int N) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int i = 0; i < d; i++)
        for (int x = 0; x < N; x++)
            add_edge(g, x, N + T[S[i]][x]);
}

static int try_order(int N, int tries) {
    int ng = enum_groups(N, groups, MAXGROUPS);
    if (ng == 0) return 0;
    for (int t = 0; t < tries && now() < t_end; t++) {
        build_group(N, &groups[rndint(ng)]);
        if (anneal(N, 50000)) {
            build_graph(&cand, N);
            if (is_valid(&cand)) {
                best = cand;
                return 1;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit N0\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long N0 = atol(argv[5]);
    t_end = now() + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    long maxN = moore_bound() / 2;
    if (maxN > MAXG) maxN = MAXG;
    long lo = N0 - 1;
    if (lo < d - 1) lo = d - 1;
    best.n = 0;
    long jump = 1 + lo / 50;
    while (now() < t_end) {
        long target = lo + jump;
        if (target > maxN) {
            if (jump == 1) break;
            jump = 1;
            continue;
        }
        if (try_order((int)target, 6)) {
            lo = target;
            long cap = 1 + lo / 25;
            jump = (jump * 2 < cap) ? jump * 2 : cap;
        } else {
            if (jump == 1) break;
            jump /= 2;
        }
    }

    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);
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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace best with (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Bipartite Cayley search in C, starting just above the current order.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            n0 = best[0] // 2 + 1
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), max(d, n0)],
                                 stdin_graph=None, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
