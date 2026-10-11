import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: ruin-and-recreate plateau search with diameter-preserving growth.
#
# Growth: a new vertex v on side t joins a set S of side-(1-t) vertices with
# spare degree whose radius-(D-1) balls cover every vertex. Adding a vertex never
# increases an old distance, so the diameter stays <= D and bipartiteness holds.
# Plateau moves: delete 1-3 random vertices, repair with random saturating edges
# between deficient opposite-side vertices (which only shorten distances), keep the
# result if it is valid and regrows to at least the current size.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 6000
#define MAXDEG 64
#define WMAX ((MAXN + 63) / 64)
#define INF 255

typedef struct {
    int n;
    int deg[MAXN];
    int side[MAXN];
    int adj[MAXN][MAXDEG];
} Gr;

static Gr CUR, TMP, BEST;
static int DEG, DIAM, NW;
static uint8_t DIST[MAXN * MAXN];
static uint64_t BALL[MAXN][WMAX];
static int QU[MAXN];
static uint64_t rs = 88172645463325252ULL;
static clock_t T0;
static double TL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void gr_copy(Gr *dst, const Gr *src) { memcpy(dst, src, sizeof(Gr)); }

static int has_edge(const Gr *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Gr *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_arc(Gr *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) {
        if (g->adj[u][i] == v) { g->adj[u][i] = g->adj[u][--g->deg[u]]; return; }
    }
}

static void remove_vertex(Gr *g, int v) {
    for (int i = 0; i < g->deg[v]; i++) del_arc(g, g->adj[v][i], v);
    g->deg[v] = 0;
    int last = g->n - 1;
    if (v != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int w = g->adj[last][i];
            for (int j = 0; j < g->deg[w]; j++) {
                if (g->adj[w][j] == last) { g->adj[w][j] = v; break; }
            }
        }
        memcpy(g->adj[v], g->adj[last], sizeof(int) * MAXDEG);
        g->deg[v] = g->deg[last];
        g->side[v] = g->side[last];
    }
    g->deg[last] = 0;
    g->n--;
}

static void add_vertex(Gr *g, int t, const int *nb, int k) {
    int v = g->n++;
    g->side[v] = t;
    g->deg[v] = 0;
    for (int i = 0; i < k; i++) add_edge(g, v, nb[i]);
}

static void all_bfs(const Gr *g) {
    int n = g->n, R = DIAM - 1;
    NW = (n + 63) / 64;
    for (int s = 0; s < n; s++) {
        uint8_t *row = DIST + (size_t)s * n;
        memset(row, INF, n);
        row[s] = 0;
        int h = 0, t = 0;
        QU[t++] = s;
        while (h < t) {
            int u = QU[h++];
            int du = row[u];
            if (du >= INF - 1) continue;
            for (int i = 0; i < g->deg[u]; i++) {
                int w = g->adj[u][i];
                if (row[w] == INF) { row[w] = (uint8_t)(du + 1); QU[t++] = w; }
            }
        }
        for (int k = 0; k < NW; k++) BALL[s][k] = 0;
        for (int w = 0; w < n; w++) {
            if (row[w] <= R) BALL[s][w >> 6] |= 1ULL << (w & 63);
        }
    }
}

static int valid(const Gr *g) {
    all_bfs(g);
    int n = g->n;
    size_t tot = (size_t)n * n;
    for (size_t i = 0; i < tot; i++) if (DIST[i] > DIAM) return 0;
    for (int u = 0; u < n; u++) {
        if (g->deg[u] > DEG) return 0;
        for (int i = 0; i < g->deg[u]; i++) {
            int w = g->adj[u][i];
            if (w == u || g->side[w] == g->side[u]) return 0;
        }
    }
    return 1;
}

/* Greedy (randomised when noise > 0) cover of all vertices by radius-(DIAM-1)
   balls of side-(1-t) vertices with spare degree. Returns count or -1. */
static int cover(const Gr *g, int t, int *out, int noise) {
    int n = g->n, W = (n + 63) / 64;
    static uint64_t U[WMAX];
    static int cnt[MAXN];
    static char used[MAXN];
    for (int k = 0; k < W; k++) U[k] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1;
    memset(used, 0, n);
    int nunc = n, k = 0;
    while (nunc > 0 && k < DEG) {
        int best = 0;
        for (int s = 0; s < n; s++) {
            cnt[s] = -1;
            if (g->side[s] != 1 - t || g->deg[s] >= DEG || used[s]) continue;
            int c = 0;
            for (int j = 0; j < W; j++) c += pc(BALL[s][j] & U[j]);
            cnt[s] = c;
            if (c > best) best = c;
        }
        if (best == 0) break;
        int thr = best;
        if (noise && best > 1 && rndint(100) < noise) thr = best - 1;
        int nc = 0, pick = -1;
        for (int s = 0; s < n; s++) {
            if (cnt[s] >= thr && cnt[s] > 0) {
                nc++;
                if (rndint(nc) == 0) pick = s;
            }
        }
        if (pick < 0) break;
        used[pick] = 1;
        out[k++] = pick;
        for (int j = 0; j < W; j++) U[j] &= ~BALL[pick][j];
        nunc = 0;
        for (int j = 0; j < W; j++) nunc += pc(U[j]);
    }
    return nunc == 0 ? k : -1;
}

/* Try to add one vertex. Assumes g is valid. */
static int grow(Gr *g) {
    if (g->n >= MAXN) return 0;
    all_bfs(g);
    int out[MAXDEG];
    for (int a = 0; a < 6; a++) {
        int t = a & 1;
        int noise = (a >= 2) ? 25 : 0;
        int k = cover(g, t, out, noise);
        if (k > 0) {
            add_vertex(g, t, out, k);
            return 1;
        }
    }
    return 0;
}

/* Add random edges between deficient opposite-side vertices. Only shortens distances. */
static void saturate(Gr *g) {
    static int L[2][MAXN];
    int c[2] = {0, 0};
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] < DEG) {
            int s = g->side[v];
            L[s][c[s]++] = v;
        }
    }
    int fails = 0;
    while (c[0] > 0 && c[1] > 0 && fails < 300) {
        int i = rndint(c[0]), j = rndint(c[1]);
        int u = L[0][i], w = L[1][j];
        if (has_edge(g, u, w)) { fails++; continue; }
        add_edge(g, u, w);
        if (g->deg[u] >= DEG) L[0][i] = L[0][--c[0]];
        if (g->deg[w] >= DEG) L[1][j] = L[1][--c[1]];
    }
}

static void output(const Gr *g) {
    int m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++) if (g->adj[u][i] > u) m++;
    printf("%d %d\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++) {
            int w = g->adj[u][i];
            if (w > u) printf("%d %d\n", u, w);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    TL = atof(argv[4]);
    DEG = d;
    DIAM = D;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || DIAM > 200) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    T0 = clock();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int ok = 1;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
    }
    memset(&CUR, 0, sizeof(Gr));
    CUR.n = n;
    for (int i = 0; ok && i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (CUR.deg[u] >= DEG || CUR.deg[v] >= DEG) { ok = 0; break; }
        add_edge(&CUR, u, v);
    }
    free(eu);
    free(ev);
    if (ok) {
        int *col = malloc(sizeof(int) * (size_t)n);
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int top = 0;
            QU[top++] = s;
            while (top > 0 && ok) {
                int u = QU[--top];
                for (int i = 0; i < CUR.deg[u]; i++) {
                    int w = CUR.adj[u][i];
                    if (col[w] == -1) { col[w] = 1 - col[u]; QU[top++] = w; }
                    else if (col[w] == col[u]) { ok = 0; break; }
                }
            }
        }
        for (int v = 0; v < n; v++) CUR.side[v] = col[v] < 0 ? 0 : col[v];
        free(col);
    }
    if (!ok || !valid(&CUR)) { printf("0 0\n"); return 0; }

    gr_copy(&BEST, &CUR);
    while (elapsed() < TL) {
        gr_copy(&TMP, &CUR);
        if (grow(&TMP)) {
            gr_copy(&CUR, &TMP);
        } else {
            gr_copy(&TMP, &CUR);
            int r = 1 + rndint(3);
            for (int i = 0; i < r && TMP.n > 2; i++) remove_vertex(&TMP, rndint(TMP.n));
            saturate(&TMP);
            if (!valid(&TMP)) continue;
            while (grow(&TMP)) { }
            if (TMP.n >= CUR.n) gr_copy(&CUR, &TMP);
        }
        if (CUR.n > BEST.n) gr_copy(&BEST, &CUR);
    }
    output(&BEST);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions and Python helpers.
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedy set cover of `full` by at most d candidate vertices, or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of radius D-1 balls."""
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
            for attempt in range(8):
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


def _grow(n, edges, d, D, deadline, rng):
    """Cover-extend, then saturate edges with spare degree. Both keep diameter and bipartiteness."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Starting structure. For D >= 4 use W(q) (new emphasis); for D = 3 use PG(2, q).
    if D >= 3:
        base = None
        if D >= 4:
            base = _best_gq(d)
        if base is None:
            base = _best_pg(d)
        if base is not None:
            consider(base[0], base[1])
            pn, pe = _pipeline(base[0], base[1], d, D, start + 0.2 * time_limit, rng)
            consider(pn, pe)

    # New engine: C ruin-and-recreate search from the best current graph.
    if D >= 3 and d <= 64 and best_n > 2:
        remaining = end - time.monotonic()
        budget = remaining * 0.85 - 2.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=max(1.0, remaining - 1.5))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
