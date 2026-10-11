import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 32

typedef struct {
    int nv;
    int deg[MAXN];
    int side[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static Graph G, SNAP, BEST;
static int dg = 3, Dd = 2;
static int bestn = 0;
static uint64_t rs = 1;
static clock_t t_end;
static int timed_out = 0;
static unsigned char PT[65536];

static void init_pt(void) {
    PT[0] = 0;
    for (int i = 1; i < 65536; i++) PT[i] = (unsigned char)(PT[i >> 1] + (i & 1));
}

static int popc(uint64_t x) {
    return PT[x & 0xFFFFu] + PT[(x >> 16) & 0xFFFFu] + PT[(x >> 32) & 0xFFFFu] + PT[(x >> 48) & 0xFFFFu];
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    for (int i = 0; i < G.deg[a]; i++)
        if (G.adj[a][i] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    for (int i = 0; i < G.deg[a]; i++) {
        if (G.adj[a][i] == b) {
            G.adj[a][i] = G.adj[a][--G.deg[a]];
            return;
        }
    }
}

static void add_arc(int a, int b) { G.adj[a][G.deg[a]++] = b; }

static void add_edge(int a, int b) {
    add_arc(a, b);
    add_arc(b, a);
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* res[v] = bitmask of vertices within distance radius of v. */
static void compute_balls(int radius, uint64_t (*res)[MAXW]) {
    static uint64_t bA[MAXN][MAXW], bB[MAXN][MAXW];
    int n = G.nv;
    int W = (n + 63) >> 6;
    uint64_t (*a)[MAXW] = bA;
    uint64_t (*b)[MAXW] = bB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) a[v][w] = 0;
        a[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < radius; s++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) b[v][w] = a[v][w];
            for (int i = 0; i < G.deg[v]; i++) {
                const uint64_t *src = a[G.adj[v][i]];
                for (int w = 0; w < W; w++) b[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = a;
        a = b;
        b = t;
    }
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) res[v][w] = a[v][w];
}

/* Number of unordered pairs at distance > Dd (unreachable pairs included). */
static long long cost(void) {
    static uint64_t R[MAXN][MAXW];
    int n = G.nv;
    int W = (n + 63) >> 6;
    compute_balls(Dd, R);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add cross-side edges between deficient vertices (never increases cost). */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int n = G.nv, nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (G.deg[v] < dg) {
            if (G.side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    int tries = 4 * (nl + nr) + 8;
    for (int t = 0; t < tries; t++) {
        int a = L[rndint(nl)];
        int b = R[rndint(nr)];
        if (G.deg[a] < dg && G.deg[b] < dg && !has_edge(a, b)) add_edge(a, b);
    }
}

/* Bipartite double-edge switches (degrees preserved) minimising bad pairs. */
static long long anneal(long long cur, int iters) {
    int n = G.nv;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && clock() > t_end) {
            timed_out = 1;
            break;
        }
        int a = rndint(n);
        if (G.side[a] != 0 || G.deg[a] == 0) continue;
        int c = rndint(n);
        if (c == a || G.side[c] != 0 || G.deg[c] == 0) continue;
        int b = G.adj[a][rndint(G.deg[a])];
        int e = G.adj[c][rndint(G.deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.1)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

/* Add a vertex on side 1-s joined to a greedy cover of side s. */
static void add_vertex(int s) {
    int n = G.nv;
    if (n >= MAXN - 1) return;
    static uint64_t BR[MAXN][MAXW];
    int W = (n + 63) >> 6;
    compute_balls(Dd - 1, BR);
    uint64_t covered[MAXW];
    for (int w = 0; w < W; w++) covered[w] = 0;
    int used[MAXN];
    for (int v = 0; v < n; v++) used[v] = 0;
    int chosen[MAXD];
    int nc = 0;
    for (int k = 0; k < dg; k++) {
        int best = -1;
        double bsc = -1.0;
        for (int v = 0; v < n; v++) {
            if (G.side[v] != s || used[v]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(BR[v][w] & ~covered[w]);
            if (g == 0) continue;
            double sc = g + 0.5 * rnd01();
            if (sc > bsc) {
                bsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) covered[w] |= BR[best][w];
    }
    if (nc == 0) return;
    int v = n;
    G.nv = n + 1;
    G.deg[v] = 0;
    G.side[v] = 1 - s;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (G.deg[c] >= dg) {
            int t = G.adj[c][rndint(G.deg[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
}

/* Delete vertex v; the last vertex is relabelled into its slot. */
static void remove_vertex(int v) {
    for (int i = 0; i < G.deg[v]; i++) del_arc(G.adj[v][i], v);
    G.deg[v] = 0;
    int L = G.nv - 1;
    if (v != L) {
        for (int i = 0; i < G.deg[L]; i++) {
            int u = G.adj[L][i];
            for (int j = 0; j < G.deg[u]; j++) {
                if (G.adj[u][j] == L) {
                    G.adj[u][j] = v;
                    break;
                }
            }
        }
        G.deg[v] = G.deg[L];
        for (int i = 0; i < G.deg[L]; i++) G.adj[v][i] = G.adj[L][i];
        G.side[v] = G.side[L];
    }
    G.deg[L] = 0;
    G.nv--;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    Dd = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    dg = d;
    init_pt();
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    t_end = clock() + (clock_t)(tl * CLOCKS_PER_SEC);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (d < 1 || d > MAXD || Dd < 2 || n < 2 || n > MAXN - 64 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    memset(&G, 0, sizeof(G));
    G.nv = n;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (a < 0 || a >= n || b < 0 || b >= n || a == b || has_edge(a, b) ||
            G.deg[a] >= dg || G.deg[b] >= dg) {
            printf("0 0\n");
            return 0;
        }
        add_edge(a, b);
    }

    /* Bipartition check. */
    for (int v = 0; v < n; v++) G.side[v] = -1;
    int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (G.side[s] != -1) continue;
        G.side[s] = 0;
        int top = 0;
        stk[top++] = s;
        while (top > 0) {
            int u = stk[--top];
            for (int i = 0; i < G.deg[u]; i++) {
                int x = G.adj[u][i];
                if (G.side[x] == -1) {
                    G.side[x] = 1 - G.side[u];
                    stk[top++] = x;
                } else if (G.side[x] == G.side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    long long c = cost();
    if (c > 0) c = anneal(c, 20000);
    if (c != 0) {
        printf("0 0\n");
        return 0;
    }
    BEST = G;
    bestn = G.nv;

    while (clock() < t_end) {
        SNAP = G;
        timed_out = 0;
        if (rndint(3) == 0) {
            add_vertex(rndint(2));
        } else {
            int k = 1 + rndint(3);
            for (int j = 0; j < k && G.nv > 8; j++) remove_vertex(rndint(G.nv));
            fill_edges();
            anneal(cost(), 300);
            add_vertex(rndint(2));
        }
        fill_edges();
        c = anneal(cost(), 1000);
        if (c == 0) {
            if (G.nv > bestn) {
                BEST = G;
                bestn = G.nv;
            }
            if (G.nv < bestn - 2) G = BEST;
        } else {
            G = SNAP;
        }
    }

    int em = 0;
    for (int u = 0; u < BEST.nv; u++)
        for (int i = 0; i < BEST.deg[u]; i++)
            if (BEST.adj[u][i] > u) em++;
    printf("%d %d\n", BEST.nv, em);
    for (int u = 0; u < BEST.nv; u++)
        for (int i = 0; i < BEST.deg[u]; i++)
            if (BEST.adj[u][i] > u) printf("%d %d\n", u, BEST.adj[u][i]);
    return 0;
}
'''


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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Python-side annealing (used by the voltage-lift stage).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


# ----------------------------------------------------------------------------
# Random voltage lifts of small bipartite base multigraphs.
# ----------------------------------------------------------------------------

def _random_lift(k, m, d, rng):
    """Random Z_m lift of a d-regular bipartite multigraph on k + k base vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, k + perm[i], rng.randrange(m)))
    return lib.voltage_lift(2 * k, darts, m)


def _vlift_search(d, D, deadline, rng, best_n, consider):
    """Search random voltage lifts whose order is slightly above best_n, repair, then grow."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        if best_n >= moore:
            return
        k = rng.choice((1, 1, 2, 3))
        target = min(moore, best_n + rng.randint(1, 12))
        m = -(-target // (2 * k))
        if 2 * k * m > moore:
            m = moore // (2 * k)
        if m < 2 or 2 * k * m <= best_n:
            continue
        n, e = _random_lift(k, m, d, rng)
        adj = _to_sets(n, e)
        color = [0 if v < k * m else 1 for v in range(n)]
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(n) for v in adj[u] if u < v]
        consider(n, e3)
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=30)
        consider(n4, e4)
        if n4 > best_n:
            best_n = n4


# ----------------------------------------------------------------------------
# Group lifts over Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _groups_of_order(order):
    """All (m, k, r) with m*k = order giving a semidirect product Z_m x| Z_k."""
    out = []
    for m in range(1, order + 1):
        if order % m:
            continue
        k = order // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _glift_cost(kb, order, T, d, D, tgt, lab):
    """Sum over base vertices of unreached lifted vertices within distance D of (u, identity)."""
    n = 2 * kb * order
    nbr = [[] for _ in range(n)]
    for t in range(d):
        tt = tgt[t]
        lt = lab[t]
        for i in range(kb):
            j = kb + tt[i]
            g = lt[i]
            for x in range(order):
                a = i * order + x
                b = j * order + T[x][g]
                nbr[a].append(b)
                nbr[b].append(a)
    total = 0
    for u in range(2 * kb):
        s = u * order
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for w in nbr[v]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _glift_search(kb, order, T, d, D, deadline, rng):
    """Anneal dart labels and slot permutations until the lift has diameter <= D. Returns (n, edges) or None."""
    n = 2 * kb * order
    tgt = []
    lab = []
    for _ in range(d):
        p = list(range(kb))
        rng.shuffle(p)
        tgt.append(p)
        lab.append([rng.randrange(order) for _ in range(kb)])
    cur = _glift_cost(kb, order, T, d, D, tgt, lab)
    temp = 2.0
    while cur > 0 and time.monotonic() < deadline:
        if kb >= 2 and rng.random() < 0.3:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(kb), 2)
            tt = tgt[t]
            tt[i1], tt[i2] = tt[i2], tt[i1]
            c = _glift_cost(kb, order, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                tt[i1], tt[i2] = tt[i2], tt[i1]
        else:
            t = rng.randrange(d)
            i = rng.randrange(kb)
            old = lab[t][i]
            new = rng.randrange(order)
            if new == old:
                continue
            lab[t][i] = new
            c = _glift_cost(kb, order, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                lab[t][i] = old
    if cur != 0:
        return None
    edges = set()
    for t in range(d):
        for i in range(kb):
            j = kb + tgt[t][i]
            g = lab[t][i]
            for x in range(order):
                edges.add((i * order + x, j * order + T[x][g]))
    return n, sorted(edges)


def _glift_stage(d, D, rng, deadline, floor_n, limit_n):
    """Ladder over group-lift sizes above floor_n. Returns the largest valid lift found, or None."""
    cands = []
    for kb in range(1, 7):
        lo = floor_n // (2 * kb) + 1
        hi = limit_n // (2 * kb)
        for G_ in range(lo, hi + 1):
            n = 2 * kb * G_
            if floor_n < n <= limit_n:
                cands.append((n, kb, G_))
    cands.sort()
    best = None
    best_n = floor_n
    for n, kb, G_ in cands:
        if n <= best_n:
            continue
        if time.monotonic() >= deadline:
            break
        groups = _groups_of_order(G_)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        slice_end = min(deadline, time.monotonic() + 4.0)
        res = _glift_search(kb, G_, T, d, D, slice_end, rng)
        if res is not None:
            cn, ce = res
            if cn > best_n and lib.is_valid(cn, ce, d, D):
                best_n = cn
                best = (cn, ce)
    return best


# ----------------------------------------------------------------------------
# Pipeline.
# ----------------------------------------------------------------------------

def _python_phase(d, D, rng, t0, T, consider, best):
    """Structured bases, twin trials, voltage lifts and group lifts. Updates `best` in place via consider."""
    if D >= 3:
        cands = []
        if D >= 4:
            g = _best_gq(d)
            if g is not None:
                cands.append(g)
        g = _best_pg(d)
        if g is not None:
            cands.append(g)
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
        for n0, e0 in cands:
            consider(n0, e0)
        grow_end = t0 + 0.12 * T
        n1, e1 = _grow(best[0], best[1], d, D, grow_end, rng)
        consider(n1, e1)

    if D >= 2:
        trial_end = t0 + 0.22 * T
        base_n, base_e = best[0], list(best[1])
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2:
        _vlift_search(d, D, t0 + 0.32 * T, rng, best[0], consider)

    if D >= 4 and d >= 3:
        limit_n = min(lib.moore_bound(d, D), 1200)
        res = _glift_stage(d, D, rng, t0 + 0.40 * T, best[0], limit_n)
        if res is not None:
            consider(res[0], res[1])


def _c_refine(d, D, seed, n, edges, budget):
    """Run the C annealing/LNS engine from the given valid graph. Returns (n, edges) or None."""
    if budget < 1.0 or d < 1 or d > 32:
        return None
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, edges), timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback_n, fallback_e = lib.haar_graph(d, range(d))
    best = [fallback_n, list(fallback_e)]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, list(e)

    rng = random.Random(seed)
    try:
        _python_phase(d, D, rng, t0, time_limit, consider, best)
    except Exception:
        pass

    if D >= 2 and d <= 32:
        budget = t0 + 0.88 * time_limit - time.monotonic() - 3.0
        try:
            res = _c_refine(d, D, seed, best[0], best[1], budget)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    n, e = best[0], best[1]
    if not lib.is_valid(n, e, d, D):
        return fallback_n, list(fallback_e)
    return n, list(e)
