import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-driven bad-pair annealing with vertex addition and twins.
#
# State: a valid bipartite graph (max degree d, diameter <= D). Moves:
#   * add_vertex: a new vertex joins a greedy ball-cover of the opposite side,
#     stealing one edge at any full cover vertex. Fill edges, then anneal.
#   * twin_add: duplicate a vertex whose neighbours all have spare degree.
#     This keeps the diameter bound and needs no repair.
#   * strict plateau switches: degree-preserving bipartite double-edge switches
#     that keep the bad-pair count at zero, to diversify valid graphs.
# Every saved state has zero bad pairs, so the output is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 64

typedef uint64_t u64;
typedef struct { int n; int adj[MAXN][MAXD]; int deg[MAXN]; int col[MAXN]; } State;

static int d, D, n;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static u64 BA[MAXN][MAXW], BB[MAXN][MAXW];
static u64 RC[MAXN][MAXW], RV[MAXN][MAXW];
static double t_end;
static u64 rs = 88172645463325252ULL;
static State SNAP, BEST;

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int timeup(void) { return now() >= t_end; }

static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd64() % (u64)k); }
static double rndf(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}

static void addE(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void delE(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; break; }
    for (int k = 0; k < deg[v]; k++) if (adj[v][k] == u) { adj[v][k] = adj[v][--deg[v]]; break; }
}

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* res[v] = bitmask of vertices within distance r of v. */
static void ball_compute(int r, u64 (*res)[MAXW]) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) BA[v][w] = 0;
        BA[v][v >> 6] |= 1ULL << (v & 63);
    }
    u64 (*cur)[MAXW] = BA;
    u64 (*nxt)[MAXW] = BB;
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        u64 (*tmp)[MAXW] = cur; cur = nxt; nxt = tmp;
    }
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) res[v][w] = cur[v][w];
}

/* Number of unordered vertex pairs at distance > D. */
static long cost_bad(void) {
    int W = (n + 63) >> 6;
    ball_compute(D, RC);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(RC[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_state(State *s) {
    s->n = n;
    memcpy(s->adj, adj, sizeof adj);
    memcpy(s->deg, deg, sizeof deg);
    memcpy(s->col, col, sizeof col);
}

static void load_state(const State *s) {
    n = s->n;
    memcpy(adj, s->adj, sizeof adj);
    memcpy(deg, s->deg, sizeof deg);
    memcpy(col, s->col, sizeof col);
}

static void build_kdd(void) {
    memset(deg, 0, sizeof deg);
    n = 2 * d;
    for (int i = 0; i < d; i++) { col[i] = 0; col[d + i] = 1; }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            addE(i, d + j);
}

static int load_graph(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || n0 > MAXN - 2 || m0 < 0) return 0;
    n = n0;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        if (has(u, v)) return 0;
        addE(u, v);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] == -1) { col[w] = 1 - col[u]; stk[sp++] = w; }
                else if (col[w] == col[u]) return 0;
            }
        }
    }
    return 1;
}

/* Add cross edges between deficient opposite-side vertices (never increases bad pairs). */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (deg[a] >= d) break;
            int b = R[j];
            if (deg[b] < d && !has(a, b)) addE(a, b);
        }
    }
}

/* New vertex on `side`, joined to a greedy cover of the opposite side's radius-(D-1) balls. */
static void add_vertex(int side) {
    if (n >= MAXN - 1) return;
    int W = (n + 63) >> 6;
    ball_compute(D - 1, RV);
    u64 covered[MAXW];
    for (int w = 0; w < W; w++) covered[w] = 0;
    static int used[MAXN];
    for (int v = 0; v < n; v++) used[v] = 0;
    int chosen[MAXD];
    int nc = 0;
    while (nc < d) {
        int best = -1;
        double bs = -1.0;
        for (int c = 0; c < n; c++) {
            if (col[c] == side || used[c]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(RV[c][w] & ~covered[w]);
            if (g == 0) continue;
            double sc = g + 0.5 * rndf();
            if (sc > bs) { bs = sc; best = c; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) covered[w] |= RV[best][w];
    }
    if (nc == 0) return;
    int v = n;
    n++;
    col[v] = side;
    deg[v] = 0;
    for (int k = 0; k < nc; k++) {
        int c = chosen[k];
        if (deg[c] >= d) {
            int t = adj[c][rndi(deg[c])];
            delE(c, t);
        }
        addE(v, c);
    }
}

/* Duplicate a vertex whose neighbours all have spare degree (non-adjacent twin). */
static int twin_add(void) {
    if (n >= MAXN - 1) return 0;
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] == 0) continue;
        int ok = 1;
        for (int k = 0; k < deg[v]; k++) if (deg[adj[v][k]] >= d) { ok = 0; break; }
        if (ok) cand[nc++] = v;
    }
    if (nc == 0) return 0;
    int v = cand[rndi(nc)];
    int w = n++;
    col[w] = col[v];
    deg[w] = 0;
    for (int k = 0; k < deg[v]; k++) addE(w, adj[v][k]);
    return 1;
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs.
   strict = 1: only zero-cost moves are accepted (keeps the graph valid). */
static long anneal(int iters, int strict) {
    static int S0[MAXN];
    int ns = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) S0[ns++] = v;
    long cur = cost_bad();
    if (ns < 2) return cur;
    for (int it = 0; it < iters; it++) {
        if (!strict && cur == 0) break;
        if (timeup()) break;
        int a = S0[rndi(ns)];
        if (deg[a] == 0) continue;
        int b = adj[a][rndi(deg[a])];
        int c = S0[rndi(ns)];
        if (c == a || deg[c] == 0) continue;
        int e = adj[c][rndi(deg[c])];
        if (has(a, e) || has(c, b)) continue;
        delE(a, b); delE(c, e);
        addE(a, e); addE(c, b);
        long nw = cost_bad();
        if (nw <= cur || (!strict && nw == cur + 1 && rndf() < 0.08)) {
            cur = nw;
        } else {
            delE(a, e); delE(c, b);
            addE(a, b); addE(c, e);
        }
    }
    return cur;
}

static void print_state(const State *s) {
    long m = 0;
    for (int v = 0; v < s->n; v++) m += s->deg[v];
    m /= 2;
    printf("%d %ld\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++) {
            int u = s->adj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1) d = 1;
    if (d > MAXD - 1) d = MAXD - 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    t_end = now() + tl;

    if (!load_graph()) build_kdd();
    if (D < 2) {
        save_state(&BEST);
        print_state(&BEST);
        return 0;
    }
    if (cost_bad() != 0) build_kdd();

    save_state(&BEST);
    int fails = 0;
    while (!timeup()) {
        save_state(&SNAP);

        if (rndi(4) == 0 && twin_add()) {
            fill_edges();
            if (n > BEST.n) save_state(&BEST);
            anneal(60, 1);
            fails = 0;
            continue;
        }

        add_vertex(rndi(2));
        fill_edges();
        long c = anneal(900, 0);
        if (c == 0) {
            if (n > BEST.n) save_state(&BEST);
            anneal(120, 1);
            fill_edges();
            if (n > BEST.n) save_state(&BEST);
            fails = 0;
            continue;
        }
        load_state(&SNAP);
        fails++;
        if (fails > 300) {
            load_state(&BEST);
            fails = 0;
        }
    }

    load_state(&BEST);
    print_state(&BEST);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (starting points for the C engine).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """PG(2, q) incidence for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    base = None
    if D >= 4:
        base = _best_gq(d)
    elif D == 3:
        base = _best_pg(d)
    if base is not None and base[0] > best_n and lib.is_valid(base[0], base[1], d, D):
        best_n, best_e = base

    # Hand the structured base to the C engine, which grows and repairs it.
    budget = max(0.3, min(0.8 * time_limit - 2.0, time_limit - 4.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(best_n, best_e), timeout=budget + 3.0)
        n1, e1 = lib.parse_graph_text(out)
        if n1 > best_n and lib.is_valid(n1, e1, d, D):
            best_n, best_e = n1, e1
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
