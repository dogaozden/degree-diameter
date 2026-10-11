import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving annealing with vertex insertion.
#
# Starting from a valid bipartite graph, repeatedly (1) insert a new vertex on
# one side, attached to up to d spare vertices of the other side, (2) anneal
# with double-edge swaps and spare-endpoint moves to drive the number of
# vertex pairs at distance > D to zero, and (3) keep the result when it reaches
# zero, otherwise roll back to the last valid state. Edges are only ever added
# when both endpoints have spare degree, so degrees stay <= d and the graph
# stays bipartite. The output is always a valid graph or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 6000
#define WMAX ((NMAX + 63) / 64)

static int DEG = 0, DIAM = 0;
static int n = 0;
static int side[NMAX];
static int deg[NMAX];
static int *adj = NULL;
static int *sv_adj = NULL;
static int sv_deg[NMAX], sv_side[NMAX], sv_n = 0;
static uint64_t *bufA = NULL, *bufB = NULL;
static uint64_t rs = 88172645463325252ULL;
static double t_budget = 1.0;
static clock_t t_start;
static long long cur_bad = 0;
static int cand[NMAX];
static int qbuf[NMAX];

typedef struct { int a, b, add; } Op;
static Op ops[64];
static int nops = 0;

#define ADJ(v, i) adj[(size_t)(v) * DEG + (i)]

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int out_of_time(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC >= t_budget;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int is_adj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (ADJ(a, i) == b) return 1;
    return 0;
}

static void add_half(int a, int b) { ADJ(a, deg[a]) = b; deg[a]++; }
static void add_e(int a, int b) { add_half(a, b); add_half(b, a); }

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (ADJ(a, i) == b) {
            ADJ(a, i) = ADJ(a, deg[a] - 1);
            deg[a]--;
            return;
        }
    }
}
static void del_e(int a, int b) { del_half(a, b); del_half(b, a); }

/* Number of ordered-pair misses / 2: unordered pairs at distance > DIAM. */
static long long compute_bad(void) {
    int W = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)ADJ(v, i) * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(s[w]);
        miss += n - c;
    }
    return miss / 2;
}

static void op_del(int a, int b) {
    del_e(a, b);
    ops[nops].a = a; ops[nops].b = b; ops[nops].add = 0; nops++;
}
static void op_add(int a, int b) {
    add_e(a, b);
    ops[nops].a = a; ops[nops].b = b; ops[nops].add = 1; nops++;
}
static void undo_ops(void) {
    while (nops > 0) {
        nops--;
        if (ops[nops].add) del_e(ops[nops].a, ops[nops].b);
        else add_e(ops[nops].a, ops[nops].b);
    }
}

static int rand_vertex_with_edge(int *a_out, int *b_out) {
    for (int t = 0; t < 100; t++) {
        int a = rndi(n);
        if (deg[a] > 0) {
            *a_out = a;
            *b_out = ADJ(a, rndi(deg[a]));
            return 1;
        }
    }
    return 0;
}

/* Random edge oriented so that x is on side 0 and y on side 1. */
static int rand_edge_side0(int *x, int *y) {
    int a, b;
    if (!rand_vertex_with_edge(&a, &b)) return 0;
    if (side[a] == 0) { *x = a; *y = b; }
    else { *x = b; *y = a; }
    return 1;
}

static int rand_spare(int s, int *z) {
    for (int t = 0; t < 2000; t++) {
        int c = rndi(n);
        if (side[c] == s && deg[c] < DEG) { *z = c; return 1; }
    }
    return 0;
}

/* Propose one local move (ops recorded). Returns 0 with no ops applied on failure. */
static int propose(void) {
    nops = 0;
    int x, y, x2, y2, z;
    if (rndu() < 0.7) {
        if (!rand_edge_side0(&x, &y) || !rand_edge_side0(&x2, &y2)) return 0;
        if (x == x2 || y == y2) return 0;
        if (is_adj(x, y2) || is_adj(x2, y)) return 0;
        op_del(x, y);
        op_del(x2, y2);
        op_add(x, y2);
        op_add(x2, y);
        return 1;
    }
    if (!rand_edge_side0(&x, &y)) return 0;
    if (rndi(2)) {
        if (!rand_spare(1, &z) || z == y || is_adj(x, z)) return 0;
        op_del(x, y);
        op_add(x, z);
    } else {
        if (!rand_spare(0, &z) || z == x || is_adj(z, y)) return 0;
        op_del(x, y);
        op_add(z, y);
    }
    return 1;
}

static void sa_run(int iters, double T0, double T1) {
    for (int it = 0; it < iters && cur_bad > 0; it++) {
        if (out_of_time()) return;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (!propose()) continue;
        long long nb = compute_bad();
        long long delta = nb - cur_bad;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur_bad = nb;
        else undo_ops();
    }
}

/* Add every edge between spare vertices of opposite sides (never hurts distances). */
static void saturate(void) {
    for (int a = 0; a < n; a++) {
        if (side[a] != 0 || deg[a] >= DEG) continue;
        for (int b = 0; b < n && deg[a] < DEG; b++) {
            if (side[b] != 1 || deg[b] >= DEG) continue;
            if (is_adj(a, b)) continue;
            add_e(a, b);
        }
    }
    cur_bad = compute_bad();
}

static void save_state(void) {
    sv_n = n;
    memcpy(sv_adj, adj, sizeof(int) * (size_t)n * DEG);
    memcpy(sv_deg, deg, sizeof(int) * (size_t)n);
    memcpy(sv_side, side, sizeof(int) * (size_t)n);
}

static void load_state(void) {
    n = sv_n;
    memcpy(adj, sv_adj, sizeof(int) * (size_t)n * DEG);
    memcpy(deg, sv_deg, sizeof(int) * (size_t)n);
    memcpy(side, sv_side, sizeof(int) * (size_t)n);
}

/* Add a vertex on the side opposite to a random side, attached to up to DEG spare vertices. */
static int insert_vertex(void) {
    if (n + 1 >= NMAX) return 0;
    int s = rndi(2);
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (side[u] == s && deg[u] < DEG) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int v = n;
    n++;
    side[v] = 1 - s;
    deg[v] = 0;
    int take = nc < DEG ? nc : DEG;
    for (int i = 0; i < take; i++) add_e(v, cand[i]);
    return 1;
}

static int read_graph(void) {
    long long N, M;
    if (scanf("%lld %lld", &N, &M) != 2) return 0;
    if (N < 1 || N >= NMAX || M < 0) return 0;
    n = (int)N;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (long long k = 0; k < M; k++) {
        long long u, v;
        if (scanf("%lld %lld", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= DEG || deg[v] >= DEG) return 0;
        if (is_adj((int)u, (int)v)) return 0;
        add_e((int)u, (int)v);
    }
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t) {
            int x = qbuf[h++];
            for (int i = 0; i < deg[x]; i++) {
                int y = ADJ(x, i);
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    qbuf[t++] = y;
                } else if (side[y] == side[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_state(void) {
    long long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    printf("%d %lld\n", n, m / 2);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = ADJ(v, i);
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    t_budget = atof(argv[4]);
    t_start = clock();
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || DIAM < 1) { printf("0 0\n"); return 0; }
    adj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    sv_adj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    bufA = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    bufB = malloc(sizeof(uint64_t) * (size_t)NMAX * WMAX);
    if (!adj || !sv_adj || !bufA || !bufB) { printf("0 0\n"); return 0; }

    if (!read_graph()) { printf("0 0\n"); return 0; }

    cur_bad = compute_bad();
    if (cur_bad > 0) {
        sa_run(4000, 2.0, 0.1);
        if (cur_bad > 0) { printf("0 0\n"); return 0; }
    }
    saturate();
    save_state();

    while (!out_of_time()) {
        if (!insert_vertex()) break;
        cur_bad = compute_bad();
        sa_run(1200, 3.0, 0.15);
        if (cur_bad == 0) {
            saturate();
            save_state();
        } else {
            load_state();
            cur_bad = 0;
        }
    }
    print_state();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (unchanged from the parent except for the time split).
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


def _remove_twins(n, edges, frac, rng):
    """Delete a random fraction of redundant twins; the diameter is preserved."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    classes = {}
    for v in range(n):
        if adj[v]:
            classes.setdefault(frozenset(adj[v]), []).append(v)
    cands = []
    for grp in classes.values():
        if len(grp) >= 2:
            cands.extend(grp[1:])
    if not cands:
        return n, list(edges)
    k = max(1, int(frac * len(cands)))
    drop = set(rng.sample(cands, min(k, len(cands))))
    keep = [v for v in range(n) if v not in drop]
    idx = {v: i for i, v in enumerate(keep)}
    new_e = [(idx[u], idx[v]) for u, v in edges if u not in drop and v not in drop]
    return len(keep), new_e


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
    """Greedy set cover of `full` by at most d candidate vertices."""
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


def _ball_rows(ball, idx, n):
    """float32 membership matrix: row r is the ball of idx[r] as a 0/1 vector over n vertices."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover of all n vertices by at most d candidate rows of sub."""
    k = sub.shape[0]
    uncovered = np.ones(n, dtype=np.float32)
    avail_b = np.ones(k, dtype=bool)
    chosen = []
    while uncovered.sum() > 0:
        if len(chosen) >= d or not avail_b.any():
            return None
        avail = avail_b.astype(np.float32)
        cnt = avail @ sub
        if np.any((uncovered > 0) & (cnt < 0.5)):
            return None
        w = np.where(uncovered > 0, 1.0 / np.maximum(cnt, 1.0), 0.0).astype(np.float32)
        gain = sub @ w
        gain[~avail_b] = -1.0
        best = float(gain.max())
        if best <= 0:
            return None
        if randomize:
            thr = best * (0.9 if rng.random() < 0.3 else 1.0)
            opts = np.flatnonzero((gain >= thr) & avail_b)
            i = int(opts[rng.randrange(len(opts))])
        else:
            i = int(np.argmax(gain))
        chosen.append(cands[i])
        avail_b[i] = False
        uncovered[sub[i] > 0] = 0.0
    return chosen


def _weighted_cover_search(cands, ball, n, d, rng, tries, deadline):
    """Try several weighted covers (first deterministic, then randomised)."""
    sub = _ball_rows(ball, cands, n)
    for t in range(tries):
        if time.monotonic() >= deadline:
            break
        ch = _weighted_cover(sub, cands, n, d, rng, t > 0)
        if ch:
            return ch
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
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
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _weighted_cover_search(cands, ball, n, d, rng, 15, deadline)
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
    """Extend by cover vertices FIRST, then saturate edges with the remaining spare degree."""
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


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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

    # Phase 1 (construction) takes roughly the first 40% of the budget.
    # Phase 2 (C annealing with vertex insertion) gets the rest.

    # D >= 3: projective planes grown by the twin + cover pipeline.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            ext_deadline = start + 0.2 * T
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown by an iterated search.
    pipe_end = start + 0.35 * T
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            cur = None
            top = None
            while time.monotonic() < pipe_end:
                if cur is None or rng.random() < 0.2:
                    src_n, src_e = gq[0], gq[1]
                else:
                    frac = rng.uniform(0.05, 0.3)
                    src_n, src_e = _remove_twins(cur[0], cur[1], frac, rng)
                    src_e = _saturate_edges(src_n, src_e, d, rng)
                pn, pe = _pipeline(src_n, src_e, d, D, pipe_end, rng)
                consider(pn, pe)
                if top is None or pn > top[0]:
                    top = (pn, pe)
                if cur is None or pn >= cur[0]:
                    cur = (pn, pe)
                elif pn >= cur[0] - 2 and rng.random() < 0.15:
                    cur = (pn, pe)
                if cur[0] < top[0] - 4:
                    cur = top

    # Secondary families: group lifts (D >= 4) and cyclic/Haar lifts.
    deadline = start + 0.4 * T
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    # Phase 2: C engine grows the best graph by vertex insertion with annealing repair.
    elapsed = time.monotonic() - start
    remain = T - elapsed - 4.0
    c_budget = min(0.5 * T - 1.0, 0.9 * remain)
    if c_budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                            stdin_graph=best,
                            timeout=max(1.0, T - elapsed - 2.0))
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
