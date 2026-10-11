import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: valid-graph growth with edge-swap annealing.
#
# Keeps the best valid bipartite graph. Each round it reloads that graph, takes
# a few zero-cost plateau swaps to change its structure, adds one vertex whose
# neighbours greedily cover the radius-(D-1) balls, saturates spare degree, and
# anneals edge swaps (degree-preserving, bipartition-preserving) until the
# number of pairs at distance > D is zero. Success saves a larger graph.
# Only valid snapshots are printed. On any problem it prints "0 0", and the
# Python side then keeps its own valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define W 16
#define MAXD 40
#define WALK 100
#define ITERS 3000
#define TSTART 0.7

typedef uint64_t u64;

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} Snap;

static int N, DG, DIAM;
static int deg[MAXN], adj[MAXN][MAXD], col[MAXN];
static Snap best;
static double budget_s;
static u64 rs;
static u64 BA[MAXN][W], BB[MAXN][W], BR[MAXN][W], B1[MAXN][W];

static void fail_out(void) {
    printf("0 0\n");
    exit(0);
}

static u64 rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndint(int k) { return (int)(rnd64() % (u64)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int timeup(void) { return elapsed() >= budget_s; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* out[v] = bitmask of vertices within distance r of v (current graph). */
static void balls(int r, u64 (*out)[W]) {
    int n = N, words = (n + 63) >> 6;
    u64 (*cu)[W] = BA;
    u64 (*nx)[W] = BB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < words; w++) cu[v][w] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < words; w++) nx[v][w] = cu[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < words; w++) nx[v][w] |= cu[u][w];
            }
        }
        u64 (*t)[W] = cu;
        cu = nx;
        nx = t;
    }
    for (int v = 0; v < n; v++)
        for (int w = 0; w < words; w++) out[v][w] = cu[v][w];
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs count). */
static long long cost_now(void) {
    balls(DIAM, BR);
    int words = (N + 63) >> 6;
    long long c = 0;
    for (int v = 0; v < N; v++) {
        int s = 0;
        for (int w = 0; w < words; w++) s += pc64(BR[v][w]);
        c += N - s;
    }
    return c / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

static int pick_side(int s) {
    for (int t = 0; t < 2000; t++) {
        int v = rndint(N);
        if (col[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Proposal: a,c on side s; b in N(a), e in N(c); replace (a,b),(c,e) by (a,e),(c,b). */
static int propose(int *A, int *B, int *C, int *E) {
    int s = rndint(2);
    int a = pick_side(s), c = pick_side(s);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj[a][rndint(deg[a])];
    int e = adj[c][rndint(deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    *A = a;
    *B = b;
    *C = c;
    *E = e;
    return 1;
}

static void apply_swap(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_swap(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Zero-cost plateau moves on a valid graph. */
static void walk(int K) {
    for (int k = 0; k < K && !timeup(); k++) {
        int a, b, c, e;
        if (!propose(&a, &b, &c, &e)) continue;
        apply_swap(a, b, c, e);
        if (cost_now() != 0) undo_swap(a, b, c, e);
    }
}

/* Annealing on cost. Returns 1 if the graph is valid at the end. */
static int anneal(long long iters, double t0) {
    long long cur = cost_now();
    if (cur == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 15) == 0 && timeup()) break;
        double T = t0 * (1.0 - (double)it / (double)iters) + 0.01;
        int a, b, c, e;
        if (!propose(&a, &b, &c, &e)) continue;
        apply_swap(a, b, c, e);
        long long nc = cost_now();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_swap(a, b, c, e);
        }
    }
    return cur == 0;
}

/* Greedy choice of up to DG vertices on side 1-t maximising coverage of radius DIAM-1 balls. */
static int choose_nbrs(int t, int *chosen) {
    balls(DIAM - 1, B1);
    int words = (N + 63) >> 6;
    u64 cov[W];
    int used[MAXN];
    memset(cov, 0, sizeof cov);
    memset(used, 0, sizeof used);
    int k = 0, covc = 0;
    while (k < DG && covc < N) {
        int bi = -1, bg = 0, ties = 0;
        for (int s = 0; s < N; s++) {
            if (col[s] == t || deg[s] >= DG || used[s]) continue;
            int g = 0;
            for (int w = 0; w < words; w++) g += pc64(B1[s][w] & ~cov[w]);
            if (g > bg) {
                bg = g;
                bi = s;
                ties = 1;
            } else if (g == bg && g > 0) {
                ties++;
                if (rndint(ties) == 0) bi = s;
            }
        }
        if (bi < 0) break;
        used[bi] = 1;
        chosen[k++] = bi;
        covc = 0;
        for (int w = 0; w < words; w++) {
            cov[w] |= B1[bi][w];
            covc += pc64(cov[w]);
        }
    }
    return k;
}

static int grow_once(void) {
    if (N >= MAXN - 1) return 0;
    int order[2];
    order[0] = rndint(2);
    order[1] = 1 - order[0];
    for (int q = 0; q < 2; q++) {
        int t = order[q];
        int chosen[MAXD];
        int k = choose_nbrs(t, chosen);
        if (k == 0) continue;
        int v = N++;
        col[v] = t;
        deg[v] = 0;
        for (int i = 0; i < k; i++) add_edge(v, chosen[i]);
        return 1;
    }
    return 0;
}

static void shuffle_arr(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Add edges between spare-degree vertices on opposite sides (never increases cost). */
static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= DG) continue;
        if (col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_arr(L, nl);
    shuffle_arr(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (deg[a] >= DG) break;
            int b = R[j];
            if (deg[b] < DG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void save_best(void) {
    best.n = N;
    memcpy(best.deg, deg, sizeof deg);
    memcpy(best.adj, adj, sizeof adj);
    memcpy(best.col, col, sizeof col);
}

static void load_best(void) {
    N = best.n;
    memcpy(deg, best.deg, sizeof deg);
    memcpy(adj, best.adj, sizeof adj);
    memcpy(col, best.col, sizeof col);
}

static void print_best(void) {
    int m = 0;
    for (int v = 0; v < best.n; v++)
        for (int i = 0; i < best.deg[v]; i++)
            if (v < best.adj[v][i]) m++;
    printf("%d %d\n", best.n, m);
    for (int v = 0; v < best.n; v++)
        for (int i = 0; i < best.deg[v]; i++) {
            int u = best.adj[v][i];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    if (DG < 1 || DG > MAXD || DIAM < 2) fail_out();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) fail_out();
    if (n <= 0 || n > MAXN - 64 || m < 0) fail_out();
    N = n;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) fail_out();
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) fail_out();
        if (deg[u] >= DG || deg[v] >= DG || has_edge(u, v)) fail_out();
        add_edge(u, v);
    }

    /* Bipartition by BFS; an odd cycle is a failure. */
    for (int v = 0; v < n; v++) col[v] = -1;
    static int qu[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail) {
            int u = qu[head++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    qu[tail++] = w;
                } else if (col[w] == col[u]) {
                    fail_out();
                }
            }
        }
    }

    if (cost_now() != 0) anneal(20000, TSTART);
    saturate();
    if (cost_now() != 0) fail_out();
    save_best();

    while (!timeup()) {
        load_best();
        walk(WALK);
        if (!grow_once()) {
            walk(WALK * 5);
            if (!grow_once()) break;
        }
        saturate();
        if (anneal(ITERS, TSTART)) save_best();
    }
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _structured_base(d, D):
    """Best known structured graph for this (d, D), or None."""
    if D == 3:
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                pass
        return _best_pg(d)
    if D == 4:
        return _best_gq(d)
    return None


# ----------------------------------------------------------------------------
# Driver. Python builds the best structured start (always validated). The C
# engine then grows it for most of the time limit. Any failure keeps the
# Python graph, so the output is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    if best[0] >= lib.moore_bound(d, D):
        return best

    try:
        base = _structured_base(d, D)
        if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, D):
            best = base
    except Exception:
        pass
    if best[0] >= lib.moore_bound(d, D):
        return best

    elapsed = time.monotonic() - t0
    budget = 0.75 * time_limit - elapsed
    if budget > 1.0:
        timeout = min(budget + 6.0, time_limit - elapsed - 3.0)
        if timeout > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=timeout)
                n, e = lib.parse_graph_text(out)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, list(e))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
