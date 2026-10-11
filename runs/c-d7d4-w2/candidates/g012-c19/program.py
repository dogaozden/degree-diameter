import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-based vertex-addition and repair search.
#
# The engine keeps a valid bipartite graph (max degree d, diameter <= D). Each
# step:
#   1. adds one vertex, joined to a greedy cover of one side (cover radius D-1,
#      bitset balls), and frees degree on saturated neighbours by deleting one
#      random edge each;
#   2. fills spare degree with cross-side edges (this can only shorten paths);
#   3. repairs the diameter with simulated annealing over bipartite double-edge
#      switches (degrees and bipartiteness preserved), minimising the number of
#      vertex pairs at distance > D, computed exactly with bitset balls;
#   4. on success prunes redundant edges (deletions that keep diameter <= D),
#      which frees degree for later additions; on failure reverts to the snapshot.
# Every stored state has cost 0, so the output is always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 40
#define MAXW (MAXN / 64)

typedef unsigned long long u64;
typedef u64 Row[MAXW];

typedef struct {
    int n;
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} State;

static State cur, best, snap;
static int dd, DD;
static u64 rs = 88172645463325252ULL;
static Row BA[MAXN], BB[MAXN];
static double t_stop = 1.0;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return (double)clock() / CLOCKS_PER_SEC >= t_stop; }
static int words(int n) { return (n + 63) / 64; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int idx_of(const State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++)
        if (s->adj[a][k] == b) return k;
    return -1;
}
static int has_edge(const State *s, int a, int b) { return idx_of(s, a, b) >= 0; }

static void add_edge(State *s, int a, int b) {
    s->adj[a][s->deg[a]++] = b;
    s->adj[b][s->deg[b]++] = a;
}
static void rm_idx(State *s, int a, int k) {
    s->adj[a][k] = s->adj[a][--s->deg[a]];
}
static void del_edge(State *s, int a, int b) {
    rm_idx(s, a, idx_of(s, a, b));
    rm_idx(s, b, idx_of(s, b, a));
}

/* Double-edge switch: a-x, c-y become a-y, c-x (a,c on side 0; x,y on side 1).
   Applying the same call twice restores the original graph. */
static void switch_edges(State *s, int a, int ia, int c, int ic) {
    int x = s->adj[a][ia], y = s->adj[c][ic];
    s->adj[a][ia] = y;
    s->adj[c][ic] = x;
    s->adj[x][idx_of(s, x, a)] = c;
    s->adj[y][idx_of(s, y, c)] = a;
}

/* X[v] = ball of radius r around v. Returns whichever buffer holds the result. */
static Row *ballsR(const State *s, int r, Row *X, Row *Y) {
    int n = s->n, W = words(n);
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) X[v][w] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < r; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) Y[v][w] = X[v][w];
            for (int k = 0; k < s->deg[v]; k++) {
                const u64 *src = X[s->adj[v][k]];
                for (int w = 0; w < W; w++) Y[v][w] |= src[w];
            }
        }
        Row *t = X;
        X = Y;
        Y = t;
    }
    return X;
}

/* Number of unordered vertex pairs at distance > DD. */
static long cost_of(const State *s) {
    int n = s->n, W = words(n);
    Row *B = ballsR(s, DD, BA, BB);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(B[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add cross-side edges between deficient vertices. Only shortens distances. */
static void fill(State *s) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < s->n; v++) {
        if (s->deg[v] >= dd) continue;
        if (s->col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && s->deg[a] < dd; j++) {
            int b = R[j];
            if (s->deg[b] < dd && !has_edge(s, a, b)) add_edge(s, a, b);
        }
    }
}

/* New vertex on the side opposite to `side`, joined to a greedy cover of `side`.
   B holds balls of radius DD-1 for the current graph. */
static void add_vertex(State *s, int side, Row *B) {
    int n = s->n, W = words(n);
    u64 covered[MAXW];
    char used[MAXN];
    int chosen[MAXD], nc = 0;
    for (int w = 0; w < W; w++) covered[w] = 0;
    for (int v = 0; v < n; v++) used[v] = 0;
    for (int k = 0; k < dd && k < MAXD; k++) {
        int bv = -1;
        long bs = -1;
        for (int v = 0; v < n; v++) {
            if (s->col[v] != side || used[v]) continue;
            long g = 0;
            for (int w = 0; w < W; w++) g += popc(B[v][w] & ~covered[w]);
            long sc = g * 8 + rndi(8);
            if (sc > bs) {
                bs = sc;
                bv = v;
            }
        }
        if (bv < 0) break;
        used[bv] = 1;
        chosen[nc++] = bv;
        for (int w = 0; w < W; w++) covered[w] |= B[bv][w];
    }
    int v = n;
    s->n = n + 1;
    s->col[v] = 1 - side;
    s->deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (s->deg[c] >= dd) {
            int t = s->adj[c][rndi(s->deg[c])];
            del_edge(s, c, t);
        }
        add_edge(s, c, v);
    }
}

/* Simulated annealing over double-edge switches minimising cost_of. Returns final cost. */
static long anneal(State *s, int iters, double T0) {
    static int side0[MAXN];
    long cc = cost_of(s);
    int m = 0;
    for (int v = 0; v < s->n; v++)
        if (s->col[v] == 0 && s->deg[v] > 0) side0[m++] = v;
    if (m < 2) return cc;
    for (int it = 0; it < iters && cc > 0; it++) {
        if ((it & 15) == 0 && timeup()) break;
        int a = side0[rndi(m)], c = side0[rndi(m)];
        if (a == c || s->deg[a] == 0 || s->deg[c] == 0) continue;
        int ia = rndi(s->deg[a]), ic = rndi(s->deg[c]);
        int x = s->adj[a][ia], y = s->adj[c][ic];
        if (has_edge(s, a, y) || has_edge(s, c, x)) continue;
        switch_edges(s, a, ia, c, ic);
        long nw = cost_of(s);
        double T = T0 * (1.0 - (double)it / iters) + 0.02;
        if (nw <= cc || rnd01() < exp(-(double)(nw - cc) / T)) {
            cc = nw;
        } else {
            switch_edges(s, a, ia, c, ic);
        }
    }
    return cc;
}

/* Delete random edges whose removal keeps diameter <= DD (state must be valid). */
static void prune(State *s, int tests) {
    static int EU[MAXN * MAXD / 2 + 8], EV[MAXN * MAXD / 2 + 8];
    int m = 0;
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++) {
            int u = s->adj[v][k];
            if (v < u && m < MAXN * MAXD / 2) {
                EU[m] = v;
                EV[m] = u;
                m++;
            }
        }
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = EU[i];
        EU[i] = EU[j];
        EU[j] = t;
        t = EV[i];
        EV[i] = EV[j];
        EV[j] = t;
    }
    int done = 0;
    for (int i = 0; i < m && done < tests; i++) {
        if ((i & 7) == 0 && timeup()) break;
        if (!has_edge(s, EU[i], EV[i])) continue;
        done++;
        del_edge(s, EU[i], EV[i]);
        if (cost_of(s) != 0) add_edge(s, EU[i], EV[i]);
    }
}

static int read_graph(State *s) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0) return 0;
    s->n = n;
    for (int v = 0; v < n; v++) s->deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (s->deg[u] >= MAXD || s->deg[v] >= MAXD) return 0;
        if (has_edge(s, u, v)) return 0;
        add_edge(s, u, v);
    }
    return 1;
}

static int bipartite(State *s) {
    static int stk[MAXN];
    int n = s->n;
    for (int v = 0; v < n; v++) s->col[v] = -1;
    for (int st = 0; st < n; st++) {
        if (s->col[st] != -1) continue;
        s->col[st] = 0;
        int sp = 0;
        stk[sp++] = st;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < s->deg[u]; k++) {
                int w = s->adj[u][k];
                if (s->col[w] == -1) {
                    s->col[w] = 1 - s->col[u];
                    stk[sp++] = w;
                } else if (s->col[w] == s->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void complete_bip(State *s, int k) {
    s->n = 2 * k;
    for (int v = 0; v < s->n; v++) {
        s->deg[v] = 0;
        s->col[v] = v < k ? 0 : 1;
    }
    for (int a = 0; a < k; a++)
        for (int b = 0; b < k; b++) add_edge(s, a, k + b);
}

static void print_graph(const State *s) {
    int m = 0;
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++)
            if (s->adj[v][k] > v) m++;
    printf("%d %d\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++)
            if (s->adj[v][k] > v) printf("%d %d\n", v, s->adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    t_stop = atof(argv[4]);
    if (dd < 2 || dd >= MAXD || DD < 2) {
        printf("0 0\n");
        return 0;
    }

    int ok = read_graph(&cur);
    if (ok)
        for (int v = 0; v < cur.n; v++)
            if (cur.deg[v] > dd) ok = 0;
    if (ok) ok = bipartite(&cur);
    if (ok) ok = (cost_of(&cur) == 0);
    if (!ok) complete_bip(&cur, dd);

    best = cur;
    while (!timeup() && cur.n + 2 < MAXN) {
        snap = cur;
        Row *B = ballsR(&cur, DD - 1, BA, BB);
        add_vertex(&cur, rndi(2), B);
        fill(&cur);
        long c = anneal(&cur, 1500, 1.0);
        if (c == 0) {
            prune(&cur, 300);
            best = cur;
        } else {
            cur = snap;
        }
    }
    print_graph(&best);
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order (keeps bipartite, only shortens paths)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _duplicate_twins(n, edges, d, rng):
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured starts: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            consider(*base)

    # Cheap twin-duplication starts (bounded to a small share of the time).
    if D >= 2:
        n0, e0 = best_n, list(best_e)
        for _ in range(4):
            if time.monotonic() - start > 0.08 * time_limit:
                break
            n1, e1 = _duplicate_twins(n0, e0, d, rng)
            consider(n1, _saturate_edges(n1, e1, d, rng))

    # Calibration cases already at the Moore bound need no search.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Main search: C engine grows the best valid graph.
    elapsed = time.monotonic() - start
    budget = 0.80 * time_limit - elapsed - 1.5
    if D >= 2 and budget >= 1.0 and best_n + 2 < 2048 and d < 40:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(best_n, best_e),
                            timeout=0.9 * time_limit - elapsed)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
