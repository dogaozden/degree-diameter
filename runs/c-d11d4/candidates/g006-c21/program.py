"""Vertex-growth search for bipartite graphs with max degree d and diameter D.

Pipeline:
1. Python builds a starting graph: the Generalized Quadrangle W(q) for D >= 4,
   or PG(2, q) for D = 3, grown by twin and cover extension within a time slice.
2. A C engine (C_SOURCE) improves it. Its moves are degree-preserving bipartite
   double-edge swaps, which walk along the set of valid graphs, and exchange
   augmentation: remove an edge, insert a vertex whose neighbourhood covers all
   vertices within distance D-1, then fill spare degree with edges. Every
   accepted state is checked for diameter <= D with bitset BFS.
3. The output is validated in Python and the best valid graph is returned.
"""
import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 6000
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)

typedef uint64_t row_t[MAXW];

static int n, dmax, D;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t rs = 88172645463325252ULL;
static row_t BUF0[MAXN], BUF1[MAXN];
static int LL[MAXN], RR[MAXN], CAND[MAXN], STK[MAXN];
static char USED[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) {
    return (int)(rnd() % (uint64_t)k);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void add_arc(int a, int b) {
    adj[a][deg[a]++] = b;
}

static void add_edge(int a, int b) {
    add_arc(a, b);
    add_arc(b, a);
}

static void del_arc(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Bitset ball of radius r around every vertex. Returns a pointer to one of the buffers. */
static row_t *ball_of(int r) {
    int W = (n + 63) >> 6;
    row_t *cur = BUF0, *nxt = BUF1;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(row_t));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt[v];
            memcpy(x, cur[v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *y = cur[adj[v][i]];
                for (int w = 0; w < W; w++) x[w] |= y[w];
            }
        }
        row_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

static int diam_ok(void) {
    row_t *R = ball_of(D);
    int W = (n + 63) >> 6;
    int rem = n & 63;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) {
            uint64_t full = ~0ULL;
            if (w == W - 1 && rem) full = (1ULL << rem) - 1;
            if ((R[v][w] & full) != full) return 0;
        }
    }
    return 1;
}

/* Greedy cover of all n vertices by at most dmax candidates of colour != nc with spare degree. */
static int cover_pick(int nc, row_t *B, int *chosen) {
    int W = (n + 63) >> 6;
    row_t cov;
    memset(cov, 0, sizeof(cov));
    int nca = 0;
    for (int s = 0; s < n; s++) {
        USED[s] = 0;
        if (col[s] != nc && deg[s] < dmax) CAND[nca++] = s;
    }
    int covered = 0, k = 0;
    while (covered < n && k < dmax) {
        int best = -1, bestg = 0;
        long bestscore = -1;
        for (int i = 0; i < nca; i++) {
            int s = CAND[i];
            if (USED[s]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(B[s][w] & ~cov[w]);
            if (g == 0) continue;
            long sc = (long)g * 1024 + rndint(1024);
            if (sc > bestscore) {
                bestscore = sc;
                best = s;
                bestg = g;
            }
        }
        if (best < 0) break;
        USED[best] = 1;
        chosen[k++] = best;
        for (int w = 0; w < W; w++) cov[w] |= B[best][w];
        covered += bestg;
    }
    return covered >= n ? k : 0;
}

/* Remove a random edge, then insert a covering vertex; keep only if the graph stays valid. */
static int exchange_step(void) {
    if (n + 2 >= MAXN) return 0;
    int a = rndint(n);
    if (deg[a] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    del_edge(a, b);
    int first = rndint(2);
    int ok = 0;
    for (int t = 0; t < 2 && !ok; t++) {
        int nc = first ^ t;
        row_t *B = ball_of(D - 1);
        int S[MAXD];
        int k = cover_pick(nc, B, S);
        if (!k) continue;
        int v = n;
        n++;
        col[v] = nc;
        deg[v] = 0;
        for (int i = 0; i < k; i++) add_edge(v, S[i]);
        if (diam_ok()) {
            ok = 1;
        } else {
            for (int i = 0; i < k; i++) del_edge(v, S[i]);
            deg[v] = 0;
            n--;
        }
    }
    if (!ok) add_edge(a, b);
    return ok;
}

/* Degree-preserving bipartite double-edge swap (a-b, c-e) -> (a-e, c-b). Plateau move. */
static int swap_step(void) {
    int a = rndint(n);
    if (!deg[a]) return 0;
    int b = adj[a][rndint(deg[a])];
    int c = rndint(n);
    if (c == a || col[c] != col[a] || !deg[c]) return 0;
    int e = adj[c][rndint(deg[c])];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    if (diam_ok()) return 1;
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
    return 0;
}

static void shuffle(int *x, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Add edges between deficient opposite-colour vertices. This never increases any distance. */
static void saturate(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= dmax) continue;
        if (col[v] == 0) LL[nl++] = v;
        else RR[nr++] = v;
    }
    if (!nl || !nr) return;
    shuffle(LL, nl);
    shuffle(RR, nr);
    for (int i = 0; i < nl; i++) {
        int x = LL[i];
        for (int j = 0; j < nr && deg[x] < dmax; j++) {
            int y = RR[j];
            if (deg[y] < dmax && !has_edge(x, y)) add_edge(x, y);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    double budget = atof(argv[4]);

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || n >= MAXN - 2 || dmax < 1 || dmax > MAXD || m < 0) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= dmax || deg[v] >= dmax || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        STK[sp++] = s;
        while (sp) {
            int u = STK[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    STK[sp++] = w;
                }
            }
        }
    }

    if (n >= 2 && diam_ok()) {
        saturate();
        clock_t t0 = clock();
        long it = 0;
        for (;;) {
            if ((it & 3) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el >= budget) break;
            }
            it++;
            if (rndint(100) < 40) {
                swap_step();
            } else if (exchange_step()) {
                saturate();
            }
        }
    }

    long M = 0;
    for (int v = 0; v < n; v++) M += deg[v];
    M /= 2;
    printf("%d %ld\n", n, M);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) printf("%d %d\n", v, adj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python growth phase: twins and cover-based vertex insertion.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices, or None on failure."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover every vertex within distance D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(20):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices. Adding edges never breaks diameter."""
    edges = list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, [list(s) for s in adj])
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(right)
    for a in left:
        for b in right:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                edges.append((a, b))
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Cover extension, then saturation, repeated while growth continues."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Starting graphs: W(q) for D >= 4, PG(2, q) for D = 3.
    starts = []
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    if not starts and D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            starts.append(pg)
    for n0, e0 in starts:
        consider(n0, e0)

    # Python growth phase, using 30% of the budget.
    for i, (n0, e0) in enumerate(starts):
        end_i = t0 + 0.30 * time_limit * (i + 1) / len(starts)
        pn, pe = _pipeline(n0, e0, d, D, end_i, rng)
        consider(pn, pe)

    # C phase: degree-preserving swaps plus exchange augmentation from the best graph.
    if D >= 2 and d <= 60 and best[0] >= 2:
        remaining = t0 + 0.88 * time_limit - time.monotonic() - 2.0
        if remaining > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, f"{remaining:.2f}"],
                                stdin_graph=best, timeout=remaining + 8.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
