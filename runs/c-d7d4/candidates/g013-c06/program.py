import itertools
import random
import time

import lib


# C engine: kill / repair / regrow search on a valid graph, using bitset balls for
# the cost (number of pairs at distance > D). Degrees are kept <= d, the graph stays
# bipartite, and only states with cost 0 are accepted, so every printed graph is valid.
C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)

typedef uint64_t row_t[MAXW];

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} graph_t;

static graph_t G, SNAP, SNAP2, BEST;
static int DEGC = 3, DIAM = 3;
static uint64_t rs = 88172645463325252ULL;
static row_t BUF0[MAXN], BUF1[MAXN];

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    for (int k = 0; k < G.deg[a]; k++)
        if (G.adj[a][k] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    for (int k = 0; k < G.deg[a]; k++) {
        if (G.adj[a][k] == b) {
            G.adj[a][k] = G.adj[a][--G.deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

static void add_edge(int a, int b) {
    G.adj[a][G.deg[a]++] = b;
    G.adj[b][G.deg[b]++] = a;
}

/* Bitset of vertices within distance r of each vertex. Returns a pointer to BUF0 or BUF1. */
static row_t *ball_radius(int r) {
    int w = (G.n + 63) >> 6;
    row_t *cur = BUF0, *nxt = BUF1;
    for (int v = 0; v < G.n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)w);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < G.n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < G.deg[v]; k++) {
                const uint64_t *src = cur[G.adj[v][k]];
                for (int i = 0; i < w; i++) nxt[v][i] |= src[i];
            }
        }
        row_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

static long bad_pairs(void) {
    int w = (G.n + 63) >> 6;
    row_t *b = ball_radius(DIAM);
    long s = 0;
    for (int v = 0; v < G.n; v++) {
        int c = 0;
        for (int i = 0; i < w; i++) c += pc64(b[v][i]);
        s += G.n - c;
    }
    return s / 2;
}

/* Delete vertex v; the last vertex is moved into slot v. */
static void remove_vertex(int v) {
    for (int k = 0; k < G.deg[v]; k++) del_arc(G.adj[v][k], v);
    G.deg[v] = 0;
    int L = G.n - 1;
    if (v != L) {
        for (int k = 0; k < G.deg[L]; k++) {
            int u = G.adj[L][k];
            for (int j = 0; j < G.deg[u]; j++) {
                if (G.adj[u][j] == L) {
                    G.adj[u][j] = v;
                    break;
                }
            }
        }
        G.deg[v] = G.deg[L];
        memcpy(G.adj[v], G.adj[L], sizeof(int) * (size_t)G.deg[L]);
        G.col[v] = G.col[L];
    }
    G.deg[L] = 0;
    G.n--;
}

/* Join deficient opposite-side pairs in random order (only shortens distances). */
static void fill(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < G.n; v++) {
        if (G.deg[v] < DEGC) {
            if (G.col[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    if (n0 == 0 || n1 == 0) return;
    long np = (long)n0 * n1;
    if (np > 4000000L) return;
    int *idx = (int *)malloc(sizeof(int) * (size_t)np);
    if (!idx) return;
    for (long i = 0; i < np; i++) idx[i] = (int)i;
    for (long i = np - 1; i > 0; i--) {
        long j = (long)(rnd() % (uint64_t)(i + 1));
        int t = idx[i];
        idx[i] = idx[j];
        idx[j] = t;
    }
    for (long i = 0; i < np; i++) {
        int a = L0[idx[i] / n1];
        int b = L1[idx[i] % n1];
        if (G.deg[a] < DEGC && G.deg[b] < DEGC && !has_edge(a, b)) add_edge(a, b);
    }
    free(idx);
}

/* Add a vertex on side opposite to `side`, joined to a greedy cover of `side`'s balls. */
static int add_vertex(int side) {
    if (G.n >= MAXN) return -1;
    int w = (G.n + 63) >> 6;
    row_t *b = ball_radius(DIAM - 1);
    row_t cov;
    memset(cov, 0, sizeof(uint64_t) * (size_t)w);
    char used[MAXN];
    memset(used, 0, sizeof used);
    int chosen[MAXD];
    int nch = 0;
    for (int step = 0; step < DEGC; step++) {
        int best = -1;
        double bg = -1.0;
        for (int s = 0; s < G.n; s++) {
            if (G.col[s] != side || used[s]) continue;
            int g = 0;
            for (int i = 0; i < w; i++) g += pc64(b[s][i] & ~cov[i]);
            double sc = (double)g + 0.5 * rndf();
            if (sc > bg) {
                bg = sc;
                best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int i = 0; i < w; i++) cov[i] |= b[best][i];
    }
    int v = G.n;
    G.n++;
    G.col[v] = 1 - side;
    G.deg[v] = 0;
    for (int k = 0; k < nch; k++) {
        int s = chosen[k];
        if (G.deg[s] >= DEGC) {
            int t = G.adj[s][rndi(G.deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    return v;
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. Returns final cost. */
static long anneal(int iters, double tend) {
    long cur = bad_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now_s() > tend) break;
        int a = -1, c = -1;
        for (int t = 0; t < 64 && a < 0; t++) {
            int x = rndi(G.n);
            if (G.col[x] == 0 && G.deg[x] > 0) a = x;
        }
        for (int t = 0; t < 64 && c < 0; t++) {
            int x = rndi(G.n);
            if (G.col[x] == 0 && G.deg[x] > 0 && x != a) c = x;
        }
        if (a < 0 || c < 0) continue;
        int b = G.adj[a][rndi(G.deg[a])];
        int e = G.adj[c][rndi(G.deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = bad_pairs();
        if (nw <= cur || (nw == cur + 1 && rndf() < 0.1)) {
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

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN || m < 0) return 0;
    G.n = n;
    for (int v = 0; v < n; v++) {
        G.deg[v] = 0;
        G.col[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (G.deg[u] >= DEGC || G.deg[v] >= DEGC) return 0;
        if (has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (G.col[s] != -1) continue;
        G.col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int k = 0; k < G.deg[x]; k++) {
                int y = G.adj[x][k];
                if (G.col[y] == -1) {
                    G.col[y] = 1 - G.col[x];
                    q[t++] = y;
                } else if (G.col[y] == G.col[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    DEGC = d;
    DIAM = D;
    rs = (uint64_t)seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    if (!read_input() || G.n < 1 || bad_pairs() != 0) {
        printf("0 0\n");
        return 0;
    }

    double tend = now_s() + tl;
    BEST = G;
    static const int ks[4] = {1, 1, 2, 3};

    while (now_s() < tend) {
        SNAP = G;
        int snapN = G.n;
        if (rndi(2) == 0 && G.n > 8) {
            int k = ks[rndi(4)];
            for (int j = 0; j < k; j++) remove_vertex(rndi(G.n));
        }
        fill();
        if (anneal(200, tend) != 0) {
            G = SNAP;
            continue;
        }
        for (int g = 0; g < 6 && now_s() < tend; g++) {
            SNAP2 = G;
            if (add_vertex(rndi(2)) < 0) break;
            fill();
            if (anneal(1000, tend) != 0) G = SNAP2;
        }
        if (G.n > BEST.n) BEST = G;
        if (G.n < BEST.n - 3) G = BEST;
        else if (G.n < snapN - 1) G = SNAP;
    }

    long m = 0;
    for (int v = 0; v < BEST.n; v++) m += BEST.deg[v];
    m /= 2;
    printf("%d %ld\n", BEST.n, m);
    for (int u = 0; u < BEST.n; u++)
        for (int k = 0; k < BEST.deg[u]; k++) {
            int v = BEST.adj[u][k];
            if (u < v) printf("%d %d\n", u, v);
        }
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
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
# Python fallback search (used only if the C engine fails).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
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


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    hard = start + 0.93 * time_limit
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

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin / cover pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Kill / repair / regrow search in C, starting from the best valid graph so far.
    if D >= 2 and time.monotonic() < deadline - 2:
        budget = deadline - time.monotonic() - 2.0
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                            stdin_graph=(best_n, best_e),
                            timeout=max(1.0, hard - time.monotonic()))
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            # C engine unavailable or failed: continue with the Python search.
            _lns(best_n, best_e, d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
