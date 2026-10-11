import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Python construction stage: generalized quadrangle W(q), then cover growth.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q + 1, diameter 4."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods are cover sets of the other side."""
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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
    """Cover vertices first, then saturate with spare degree. Both preserve diameter."""
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


# ----------------------------------------------------------------------------
# C stage: simulated annealing over degree-preserving 2-switches, interleaved
# with vertex insertion. Insertion adds a vertex and rewires existing edges
# to attach it, then saturates. Only states with zero bad pairs are kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int d, D, n, cap, W;
static int *deg, *adjl, *side;
static unsigned char *M;
static uint64_t *bufA, *bufB;
static uint64_t rs = 88172645463325252ULL;
static double t_start, t_limit;
static int sv[4], savedeg[4];
static int *save;
static int snap_n;
static int *sdeg, *sadj, *sside;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}
static int timeup(void) { return now() - t_start > t_limit; }

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static int has_edge(int u, int v) { return M[(size_t)u * cap + v]; }
static void setM(int u, int v, int x) {
    M[(size_t)u * cap + v] = (unsigned char)x;
    M[(size_t)v * cap + u] = (unsigned char)x;
}

static void link_add(int u, int v) {
    adjl[(size_t)u * d + deg[u]++] = v;
    adjl[(size_t)v * d + deg[v]++] = u;
    setM(u, v, 1);
}
static void drop(int u, int x) {
    int *r = adjl + (size_t)u * d;
    for (int i = 0; i < deg[u]; i++)
        if (r[i] == x) { r[i] = r[--deg[u]]; return; }
}
static void replace_nb(int u, int x, int y) {
    int *r = adjl + (size_t)u * d;
    for (int i = 0; i < deg[u]; i++)
        if (r[i] == x) { r[i] = y; return; }
}
static void edge_remove(int u, int v) { drop(u, v); drop(v, u); setM(u, v, 0); }

/* Number of ordered-pair-halved vertex pairs at distance > D. */
static long long bad_pairs(void) {
    int Wn = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        uint64_t *r = cur + (size_t)v * W;
        memset(r, 0, sizeof(uint64_t) * Wn);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * Wn);
            const int *nb = adjl + (size_t)v * d;
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *x = cur + (size_t)nb[i] * W;
                for (int w = 0; w < Wn; w++) o[w] |= x[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *x = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += popc(x[w]);
        tot += n - c;
    }
    return tot / 2;
}

/* Greedily add edges between deficient opposite-side vertices. Only adds edges. */
static void saturate(void) {
    int *L = malloc(sizeof(int) * (n + 1));
    int *R = malloc(sizeof(int) * (n + 1));
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++)
        if (deg[v] < d) {
            if (side[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d; j++) {
            int b = R[j];
            if (deg[b] < d && !has_edge(a, b)) link_add(a, b);
        }
    }
    free(L);
    free(R);
}

/* Insert a new vertex on side s and attach it to d opposite-side vertices,
   displacing one edge per attachment when no spare-degree vertex is available. */
static void add_vertex(int s) {
    if (n >= cap) return;
    int v = n++;
    side[v] = s;
    deg[v] = 0;
    int t = 1 - s, guard = 0;
    while (deg[v] < d && guard < 20 * d) {
        guard++;
        int b = -1;
        for (int k = 0; k < 60 && b < 0; k++) {
            int c = rndint(n);
            if (side[c] == t && deg[c] < d && !has_edge(v, c)) b = c;
        }
        if (b >= 0) { link_add(v, b); continue; }
        for (int k = 0; k < 400 && b < 0; k++) {
            int c = rndint(n);
            if (side[c] == t && deg[c] > 0 && !has_edge(v, c)) b = c;
        }
        if (b < 0) break;
        int a = adjl[(size_t)b * d + rndint(deg[b])];
        edge_remove(a, b);
        link_add(v, b);
    }
}

/* Degree-preserving 2-switch: (a,b),(c,e) -> (a,e),(c,b). a,c same side. */
static int move_switch(void) {
    for (int tries = 0; tries < 50; tries++) {
        int a = rndint(n);
        if (deg[a] == 0) continue;
        int b = adjl[(size_t)a * d + rndint(deg[a])];
        int c = rndint(n);
        if (c == a || side[c] != side[a] || deg[c] == 0) continue;
        int e = adjl[(size_t)c * d + rndint(deg[c])];
        if (e == b || has_edge(a, e) || has_edge(c, b)) continue;
        sv[0] = a; sv[1] = b; sv[2] = c; sv[3] = e;
        for (int k = 0; k < 4; k++) {
            savedeg[k] = deg[sv[k]];
            memcpy(save + k * d, adjl + (size_t)sv[k] * d, sizeof(int) * deg[sv[k]]);
        }
        replace_nb(a, b, e);
        replace_nb(b, a, c);
        replace_nb(c, e, b);
        replace_nb(e, c, a);
        setM(a, b, 0); setM(c, e, 0);
        setM(a, e, 1); setM(c, b, 1);
        return 1;
    }
    return 0;
}

static void undo_switch(void) {
    for (int k = 0; k < 4; k++) {
        deg[sv[k]] = savedeg[k];
        memcpy(adjl + (size_t)sv[k] * d, save + k * d, sizeof(int) * savedeg[k]);
    }
    int a = sv[0], b = sv[1], c = sv[2], e = sv[3];
    setM(a, e, 0); setM(c, b, 0);
    setM(a, b, 1); setM(c, e, 1);
}

static void take_snapshot(void) {
    snap_n = n;
    memcpy(sdeg, deg, sizeof(int) * n);
    memcpy(sside, side, sizeof(int) * n);
    memcpy(sadj, adjl, sizeof(int) * (size_t)n * d);
}

static void restore_snapshot(void) {
    n = snap_n;
    memcpy(deg, sdeg, sizeof(int) * n);
    memcpy(side, sside, sizeof(int) * n);
    memcpy(adjl, sadj, sizeof(int) * (size_t)n * d);
    memset(M, 0, (size_t)cap * cap);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            M[(size_t)v * cap + adjl[(size_t)v * d + i]] = 1;
}

static long long anneal(long long c, long iters, double T0, double T1) {
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (!move_switch()) continue;
        long long c2 = bad_pairs();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
        else undo_switch();
    }
    return c;
}

static void output_snapshot(void) {
    long m = 0;
    for (int v = 0; v < snap_n; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[(size_t)v * d + i] > v) m++;
    printf("%d %ld\n", snap_n, m);
    for (int v = 0; v < snap_n; v++)
        for (int i = 0; i < sdeg[v]; i++) {
            int u = sadj[(size_t)v * d + i];
            if (u > v) printf("%d %d\n", v, u);
        }
}

#define GROW_ITERS 2500

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)(atoll(argv[3]) + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    t_limit = atof(argv[4]);
    t_start = now();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || d < 1) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    cap = n0 + 800;
    deg = calloc(cap, sizeof(int));
    side = calloc(cap, sizeof(int));
    adjl = calloc((size_t)cap * d, sizeof(int));
    M = calloc((size_t)cap * cap, 1);
    sdeg = calloc(cap, sizeof(int));
    sside = calloc(cap, sizeof(int));
    sadj = calloc((size_t)cap * d, sizeof(int));
    save = calloc(4 * (size_t)d, sizeof(int));
    W = (cap + 63) / 64;
    bufA = calloc((size_t)cap * W, sizeof(uint64_t));
    bufB = calloc((size_t)cap * W, sizeof(uint64_t));

    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (has_edge(u, v) || deg[u] >= d || deg[v] >= d) continue;
        link_add(u, v);
    }

    /* Two-colour the input (BFS per component). */
    for (int v = 0; v < n; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * cap);
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjl[(size_t)u * d + i];
                if (side[w] < 0) { side[w] = 1 - side[u]; q[t++] = w; }
            }
        }
    }
    free(q);

    take_snapshot();
    long long c = bad_pairs();
    if (c > 0) c = anneal(c, 20000, 3.0, 0.3);
    if (c > 0) {
        output_snapshot();
        return 0;
    }
    saturate();
    take_snapshot();

    while (!timeup() && n < cap) {
        restore_snapshot();
        add_vertex(rndint(2));
        saturate();
        c = bad_pairs();
        c = anneal(c, GROW_ITERS, 3.0, 0.3);
        if (c == 0) {
            saturate();
            take_snapshot();
        }
    }
    output_snapshot();
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane (D >= 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Generalized quadrangle start (D >= 4), grown by cover vertices.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, t0 + 0.2 * time_limit, rng)
            consider(n2, e2)

    # New stage: C annealing that inserts vertices and repairs diameter.
    if D >= 3 and d >= 4:
        c_end = t0 + 0.85 * time_limit
        budget = c_end - time.monotonic() - 1.0
        if budget > 2:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=best, timeout=budget + 10)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
