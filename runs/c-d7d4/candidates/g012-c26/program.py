import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-accelerated annealing with kill / regrow moves.
#
# State: a bipartite graph with max degree DD and diameter DIAM, kept as adjacency
# arrays plus a side colouring. Cost = number of vertex pairs at distance > DIAM,
# computed exactly with 64-bit bitsets. Moves:
#   - grow: add a vertex whose neighbours form a greedy cover of the deficient
#     radius-(DIAM-1) balls, then anneal the cost back to zero;
#   - kill: delete a random vertex (its neighbours regain spare degree), then anneal;
#   - perturb: random degree-preserving switches, then anneal.
# Double-edge switches keep degrees and bipartiteness; fills only add edges, which
# never increases the cost. The best valid graph seen is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define WMAX (MAXN / 64)
#define ITERS 1500

typedef uint64_t u64;
typedef u64 Row[WMAX];

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} State;

static State cur, snap, best;
static int DD, DIAM;
static u64 rs = 88172645463325252ULL;
static Row bufA[MAXN], bufB[MAXN];

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (u64)k); }

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < cur.deg[a]; k++) if (cur.adj[a][k] == b) return 1;
    return 0;
}

static void del_one(int a, int b) {
    for (int k = 0; k < cur.deg[a]; k++) {
        if (cur.adj[a][k] == b) {
            cur.adj[a][k] = cur.adj[a][--cur.deg[a]];
            return;
        }
    }
}

static void add_e(int a, int b) {
    cur.adj[a][cur.deg[a]++] = b;
    cur.adj[b][cur.deg[b]++] = a;
}

static void del_e(int a, int b) { del_one(a, b); del_one(b, a); }

/* Bitmask rows: row v has bit w set iff w is within distance r of v. */
static Row *balls(int r) {
    int n = cur.n, W = (n + 63) / 64;
    Row *X = bufA, *Y = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) X[v][w] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) Y[v][w] = X[v][w];
            for (int k = 0; k < cur.deg[v]; k++) {
                int u = cur.adj[v][k];
                for (int w = 0; w < W; w++) Y[v][w] |= X[u][w];
            }
        }
        Row *t = X; X = Y; Y = t;
    }
    return X;
}

static long cost(void) {
    int n = cur.n, W = (n + 63) / 64;
    Row *B = balls(DIAM);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(B[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Random vertex on `side` with spare degree (want_free) or positive degree. -1 if none found. */
static int pick(int side, int want_free) {
    for (int t = 0; t < 200; t++) {
        int x = rndi(cur.n);
        if (cur.col[x] != side) continue;
        if (want_free ? cur.deg[x] < DD : cur.deg[x] > 0) return x;
    }
    return -1;
}

static long anneal(long iters, clock_t end) {
    long c = cost();
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 63) == 0 && clock() > end) break;
        if (rndi(4) == 0) {
            int a = pick(0, 1), b = pick(1, 1);
            if (a >= 0 && b >= 0 && !has_edge(a, b)) { add_e(a, b); c = cost(); }
            continue;
        }
        int a = pick(0, 0);
        if (a < 0) continue;
        int cc = pick(0, 0);
        if (cc < 0 || cc == a) continue;
        int b = cur.adj[a][rndi(cur.deg[a])];
        int e = cur.adj[cc][rndi(cur.deg[cc])];
        if (has_edge(a, e) || has_edge(cc, b)) continue;
        del_e(a, b); del_e(cc, e); add_e(a, e); add_e(cc, b);
        long nc = cost();
        if (nc <= c || (nc == c + 1 && rndi(10) == 0)) {
            c = nc;
        } else {
            del_e(a, e); del_e(cc, b); add_e(a, b); add_e(cc, e);
        }
    }
    return c;
}

static void perturb(void) {
    for (int t = 0; t < 10; t++) {
        int a = pick(0, 0), cc = pick(0, 0);
        if (a < 0 || cc < 0 || cc == a) continue;
        int b = cur.adj[a][rndi(cur.deg[a])];
        int e = cur.adj[cc][rndi(cur.deg[cc])];
        if (has_edge(a, e) || has_edge(cc, b)) continue;
        del_e(a, b); del_e(cc, e); add_e(a, e); add_e(cc, b);
    }
}

/* Add a vertex on a random side, joined to a greedy cover of the other side's balls. */
static int grow(void) {
    if (cur.n >= MAXN - 1) return 0;
    int c = rndi(2), n = cur.n, W = (n + 63) / 64;
    Row *B = balls(DIAM - 1);
    Row covered;
    for (int w = 0; w < W; w++) covered[w] = 0;
    int chosen[MAXD], nch = 0;
    for (int k = 0; k < DD; k++) {
        int bs = -1;
        long bsc = -1;
        for (int s = 0; s < n; s++) {
            if (cur.col[s] == c || cur.deg[s] >= DD) continue;
            int skip = 0;
            for (int j = 0; j < nch; j++) if (chosen[j] == s) { skip = 1; break; }
            if (skip) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc(B[s][w] & ~covered[w]);
            if (g == 0) continue;
            long sc = (long)g * 8 + rndi(8);
            if (sc > bsc) { bsc = sc; bs = s; }
        }
        if (bs < 0) break;
        chosen[nch++] = bs;
        for (int w = 0; w < W; w++) covered[w] |= B[bs][w];
    }
    if (nch == 0) return 0;
    int v = n;
    cur.n = n + 1;
    cur.col[v] = c;
    cur.deg[v] = 0;
    for (int j = 0; j < nch; j++) add_e(chosen[j], v);
    return 1;
}

/* Delete vertex k; the last vertex is relabelled to k to keep labels dense. */
static void kill_vertex(int k) {
    int last = cur.n - 1;
    while (cur.deg[k] > 0) {
        int u = cur.adj[k][cur.deg[k] - 1];
        cur.deg[k]--;
        del_one(u, k);
    }
    if (k != last) {
        for (int i = 0; i < cur.deg[last]; i++) {
            int u = cur.adj[last][i];
            for (int j = 0; j < cur.deg[u]; j++) {
                if (cur.adj[u][j] == last) { cur.adj[u][j] = k; break; }
            }
        }
        cur.deg[k] = cur.deg[last];
        for (int i = 0; i < cur.deg[k]; i++) cur.adj[k][i] = cur.adj[last][i];
        cur.col[k] = cur.col[last];
    }
    cur.deg[last] = 0;
    cur.n--;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (u64)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double secs = atof(argv[4]);
    clock_t end = clock() + (clock_t)(secs * CLOCKS_PER_SEC);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || n > MAXN - 2 || DD < 2 || DD > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    memset(&cur, 0, sizeof cur);
    cur.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (cur.deg[u] >= DD || cur.deg[v] >= DD || has_edge(u, v)) continue;
        add_e(u, v);
    }

    /* Two-colour the input; a conflict means it is not bipartite. */
    for (int i = 0; i < n; i++) cur.col[i] = -1;
    int *q = malloc(sizeof(int) * (size_t)n);
    int bad = 0;
    for (int s = 0; s < n; s++) {
        if (cur.col[s] != -1) continue;
        cur.col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < cur.deg[u]; k++) {
                int v = cur.adj[u][k];
                if (cur.col[v] == -1) { cur.col[v] = 1 - cur.col[u]; q[qt++] = v; }
                else if (cur.col[v] == cur.col[u]) bad = 1;
            }
        }
    }
    free(q);
    if (bad || cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    best = cur;
    int fails = 0;
    while (clock() < end) {
        if (cur.n < 3) break;
        snap = cur;
        int r = rndi(10);
        if (r < 6) {
            if (!grow()) continue;
        } else if (r < 8) {
            kill_vertex(rndi(cur.n));
        } else {
            perturb();
        }
        long c = anneal(ITERS, end);
        if (c == 0) {
            fails = 0;
            if (cur.n > best.n) best = cur;
            else if (cur.n < best.n - 3) cur = best;
        } else {
            cur = snap;
            if (++fails > 300) { cur = best; fails = 0; }
        }
    }

    int out_m = 0;
    for (int v = 0; v < best.n; v++)
        for (int k = 0; k < best.deg[v]; k++)
            if (v < best.adj[v][k]) out_m++;
    printf("%d %d\n", best.n, out_m);
    for (int v = 0; v < best.n; v++)
        for (int k = 0; k < best.deg[v]; k++)
            if (v < best.adj[v][k]) printf("%d %d\n", v, best.adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            consider(*base)

    # C annealing stage from the best structured graph. The C program prints its best
    # valid graph; any failure (compile, timeout, parse) keeps the Python result.
    left = time_limit - (time.monotonic() - t0)
    if D >= 2 and d >= 2 and left > 3:
        budget = max(1.0, 0.7 * left - 1.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(best_n, best_e), timeout=left * 0.92)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
