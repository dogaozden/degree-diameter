import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair annealing on bad-pair count.
# State is a bipartite graph with max degree d. Moves are degree-preserving
# 2-switches, edge additions between deficient vertices, and deficiency slides.
# A vertex is inserted when the graph has zero bad pairs; the engine then
# anneals back to zero. Only zero-bad-pair states are ever reported.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXDEG 32
#define MAXW ((MAXN + 63) / 64)
#define STALL_LIMIT 4000

typedef struct {
    int n;
    int deg[MAXN];
    int color[MAXN];
    int adj[MAXN][MAXDEG];
} State;

static State cur, tmp, best;
static int D, DD;
static uint64_t rs = 88172645463325252ULL;
static uint64_t ballA[MAXN][MAXW];
static uint64_t ballB[MAXN][MAXW];
static clock_t c0;
static double budget;

static uint64_t rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void copy_state(State *dst, const State *src) {
    dst->n = src->n;
    memcpy(dst->deg, src->deg, sizeof(int) * src->n);
    memcpy(dst->color, src->color, sizeof(int) * src->n);
    for (int v = 0; v < src->n; v++)
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
}

/* Number of unordered pairs at distance > D (unreachable counts as bad). */
static long long bad_pairs(const State *s) {
    int n = s->n;
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(ballA[v], 0, sizeof(uint64_t) * W);
        ballA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *b = ballB[v];
            memcpy(b, ballA[v], sizeof(uint64_t) * W);
            for (int k = 0; k < s->deg[v]; k++) {
                const uint64_t *src = ballA[s->adj[v][k]];
                for (int w = 0; w < W; w++) b[w] |= src[w];
            }
        }
        for (int v = 0; v < n; v++)
            memcpy(ballA[v], ballB[v], sizeof(uint64_t) * W);
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(ballA[v][w]);
        tot += n - pc;
    }
    return tot / 2;
}

static int has_edge(const State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++)
        if (s->adj[a][k] == b) return 1;
    return 0;
}

static void del_half(State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++) {
        if (s->adj[a][k] == b) {
            s->deg[a]--;
            s->adj[a][k] = s->adj[a][s->deg[a]];
            return;
        }
    }
}

static void del_edge(State *s, int a, int b) {
    del_half(s, a, b);
    del_half(s, b, a);
}

static void add_edge(State *s, int a, int b) {
    s->adj[a][s->deg[a]] = b;
    s->deg[a]++;
    s->adj[b][s->deg[b]] = a;
    s->deg[b]++;
}

static int defi_list(const State *s, int *out) {
    int k = 0;
    for (int v = 0; v < s->n; v++)
        if (s->deg[v] < DD) out[k++] = v;
    return k;
}

/* Degree-preserving 2-switch between two same-side vertices. */
static int mv_switch(State *s) {
    int n = s->n;
    int a = rndi(n), c = rndi(n);
    if (a == c || s->color[a] != s->color[c]) return 0;
    if (s->deg[a] == 0 || s->deg[c] == 0) return 0;
    int b = s->adj[a][rndi(s->deg[a])];
    int e = s->adj[c][rndi(s->deg[c])];
    if (b == e) return 0;
    if (has_edge(s, a, e) || has_edge(s, c, b)) return 0;
    del_edge(s, a, b);
    del_edge(s, c, e);
    add_edge(s, a, e);
    add_edge(s, c, b);
    return 1;
}

/* Add an edge between two deficient opposite-side vertices. */
static int mv_add(State *s) {
    static int dl[MAXN];
    int k = defi_list(s, dl);
    if (k < 2) return 0;
    for (int t = 0; t < 60; t++) {
        int a = dl[rndi(k)], x = dl[rndi(k)];
        if (a == x || s->color[a] == s->color[x]) continue;
        if (s->deg[a] >= DD || s->deg[x] >= DD) continue;
        if (has_edge(s, a, x)) continue;
        add_edge(s, a, x);
        return 1;
    }
    return 0;
}

/* Move one endpoint of an edge to a deficient vertex (same side as the edge's kept end). */
static int mv_slide(State *s) {
    static int dl[MAXN];
    int k = defi_list(s, dl);
    if (k < 1) return 0;
    for (int t = 0; t < 60; t++) {
        int a = dl[rndi(k)];
        int x = rndi(s->n);
        if (x == a || s->color[x] != s->color[a] || s->deg[x] == 0) continue;
        int y = s->adj[x][rndi(s->deg[x])];
        if (y == a || has_edge(s, a, y)) continue;
        del_edge(s, x, y);
        add_edge(s, a, y);
        return 1;
    }
    return 0;
}

/* Insert a new vertex adjacent to DD vertices of the opposite side,
   freeing one edge at each saturated neighbour. */
static void grow_vertex(State *s) {
    static int cand[MAXN];
    int sd = rndi(2);
    int nc = 0;
    for (int v = 0; v < s->n; v++)
        if (s->color[v] != sd) cand[nc++] = v;
    if (nc == 0) return;
    int want = DD < nc ? DD : nc;
    for (int i = 0; i < want; i++) {
        int j = i + rndi(nc - i);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int v = s->n;
    s->n++;
    s->color[v] = sd;
    s->deg[v] = 0;
    for (int i = 0; i < want; i++) {
        int c = cand[i];
        if (s->deg[c] >= DD) {
            int y = s->adj[c][rndi(s->deg[c])];
            del_edge(s, c, y);
        }
        add_edge(s, c, v);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    c0 = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int ok = (n >= 1 && n <= MAXN && DD >= 1 && DD <= MAXDEG && D >= 2 && m >= 0);
    if (ok) {
        cur.n = n;
        for (int v = 0; v < n; v++) cur.deg[v] = 0;
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
            if (cur.deg[u] >= DD || cur.deg[v] >= DD || has_edge(&cur, u, v)) { ok = 0; break; }
            add_edge(&cur, u, v);
        }
    }
    if (ok) {
        static int q[MAXN];
        for (int v = 0; v < n; v++) cur.color[v] = -1;
        for (int s0 = 0; s0 < n && ok; s0++) {
            if (cur.color[s0] != -1) continue;
            cur.color[s0] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s0;
            while (qh < qt && ok) {
                int u = q[qh++];
                for (int k = 0; k < cur.deg[u]; k++) {
                    int v = cur.adj[u][k];
                    if (cur.color[v] == -1) {
                        cur.color[v] = 1 - cur.color[u];
                        q[qt++] = v;
                    } else if (cur.color[v] == cur.color[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    long long f = bad_pairs(&cur);
    if (f != 0) { printf("0 0\n"); return 0; }

    copy_state(&best, &cur);
    int bestN = cur.n;
    long long minf = f;
    int stall = 0;

    while (elapsed() < budget) {
        if (f == 0) {
            if (cur.n > bestN) {
                copy_state(&best, &cur);
                bestN = cur.n;
            }
            if (cur.n + 1 >= MAXN) break;
            grow_vertex(&cur);
            f = bad_pairs(&cur);
            minf = f;
            stall = 0;
            continue;
        }
        copy_state(&tmp, &cur);
        double u = rnd01();
        int moved;
        if (u < 0.4) moved = mv_switch(&cur);
        else if (u < 0.7) moved = mv_add(&cur);
        else moved = mv_slide(&cur);
        if (!moved) continue;

        long long f2 = bad_pairs(&cur);
        double T = 1.0 + (double)f / 300.0;
        int acc = (f2 <= f) || (rnd01() < exp(-(double)(f2 - f) / T));
        if (acc) f = f2;
        else copy_state(&cur, &tmp);

        if (f < minf) { minf = f; stall = 0; }
        else stall++;
        if (stall > STALL_LIMIT) {
            copy_state(&cur, &best);
            f = 0;
            stall = 0;
        }
    }
    if (f == 0 && cur.n > bestN) {
        copy_state(&best, &cur);
        bestN = cur.n;
    }

    long long m2 = 0;
    for (int v = 0; v < best.n; v++) m2 += best.deg[v];
    m2 /= 2;
    printf("%d %lld\n", best.n, m2);
    for (int u = 0; u < best.n; u++)
        for (int k = 0; k < best.deg[u]; k++) {
            int v = best.adj[u][k];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: generalized quadrangle W(q), projective planes, and
# cover-based vertex growth used to produce the C engine's start graph.
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


def _best_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


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
    """Greedy set cover of `full` by at most d candidates; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
            for attempt in range(200):
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
    """Alternate cover-vertex extension and edge saturation until no growth or deadline."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    # Trivial cases.
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Start graph: W(q) for D >= 4, PG(2, q) for D = 3, grown by cover extension.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)
    elif D == 3:
        q = _best_pg_q(d)
        if q is not None:
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            n2, e2 = _grow(pn, pe, d, D, start + 0.35 * time_limit, rng)
            consider(n2, e2)

    # C grow-and-repair search from the best valid graph found so far.
    # Skip when already at the Moore bound (calibration cases).
    if D >= 3 and best[0] >= 2 and best[0] < lib.moore_bound(d, D):
        elapsed = time.monotonic() - start
        cap = 0.93 * time_limit - elapsed
        if cap > 2.0:
            c_budget = cap - 1.5
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=best, timeout=cap)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
