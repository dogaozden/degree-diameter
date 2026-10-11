import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving 2-switch annealing that adds one vertex at a time.
# Each step adds a vertex, saturates spare degree, then anneals the number of
# vertex pairs at distance > D toward zero with bitset ball computations.
# Every accepted state has max degree <= d, is bipartite, and has diameter <= D.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4200
#define MAXW 66
#define MAXD 64
#define ITERS 2500
#define MAXFAILS 4

typedef struct {
    int n;
    int deg[MAXN];
    int side[MAXN];
    int adj[MAXN][MAXD];
} State;

static int N, DMAX, DIAM, W;
static int side[MAXN], deg[MAXN], adj[MAXN][MAXD];
static uint64_t BA[MAXN][MAXW], BB[MAXN][MAXW];
static State SAVE, BEST;
static uint64_t rs = 88172645463325252ULL;
static clock_t T_START;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T_START) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long bad_pairs(void) {
    uint64_t (*X)[MAXW] = BA, (*Y)[MAXW] = BB, (*T)[MAXW];
    int v, k, w, r;
    for (v = 0; v < N; v++) {
        memset(X[v], 0, sizeof(uint64_t) * W);
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            uint64_t *y = Y[v];
            memcpy(y, X[v], sizeof(uint64_t) * W);
            for (k = 0; k < deg[v]; k++) {
                const uint64_t *x = X[adj[v][k]];
                for (w = 0; w < W; w++) y[w] |= x[w];
            }
        }
        T = X; X = Y; Y = T;
    }
    long long bad = 0;
    for (v = 0; v < N; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc(X[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int has_edge(int x, int y) {
    int k;
    for (k = 0; k < deg[x]; k++) if (adj[x][k] == y) return 1;
    return 0;
}
static void repl(int x, int old, int nw) {
    int k;
    for (k = 0; k < deg[x]; k++) if (adj[x][k] == old) { adj[x][k] = nw; return; }
}
static void add_nb(int x, int y) { adj[x][deg[x]++] = y; }
static void del_nb(int x, int y) {
    int k;
    for (k = 0; k < deg[x]; k++) if (adj[x][k] == y) {
        adj[x][k] = adj[x][deg[x] - 1];
        deg[x]--;
        return;
    }
}
static void add_edge(int x, int y) { add_nb(x, y); add_nb(y, x); }
static void del_edge(int x, int y) { del_nb(x, y); del_nb(y, x); }

/* Edges (a,b),(c,e) become (a,e),(c,b). Degrees are preserved. */
static void swap_apply(int a, int b, int c, int e) {
    repl(a, b, e);
    repl(b, a, c);
    repl(c, e, b);
    repl(e, c, a);
}

static void shuffle(int *a, int n) {
    int i;
    for (i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void take(State *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof(int) * N);
    memcpy(s->side, side, sizeof(int) * N);
    memcpy(s->adj, adj, sizeof(int) * MAXD * N);
}
static void put(const State *s) {
    N = s->n;
    memcpy(deg, s->deg, sizeof(int) * N);
    memcpy(side, s->side, sizeof(int) * N);
    memcpy(adj, s->adj, sizeof(int) * MAXD * N);
}

/* Add a vertex on side c, attached to up to DMAX opposite-side vertices.
   Full vertices give up one edge to the newcomer; the freed neighbour gets spare degree. */
static void add_vertex(int c) {
    static int cand[MAXN];
    int v = N++, nc = 0, i, attached = 0;
    side[v] = c;
    deg[v] = 0;
    for (i = 0; i < v; i++) if (side[i] != c) cand[nc++] = i;
    shuffle(cand, nc);
    for (i = 0; i < nc && attached < DMAX; i++) {
        int y = cand[i];
        if (deg[y] < DMAX) { add_edge(v, y); attached++; }
    }
    for (i = 0; i < nc && attached < DMAX; i++) {
        int y = cand[i], x;
        if (deg[y] < DMAX || has_edge(v, y)) continue;
        x = adj[y][rndi(deg[y])];
        del_edge(x, y);
        add_edge(v, y);
        attached++;
    }
}

/* Add edges between non-adjacent opposite-side vertices with spare degree. */
static void fill_spares(void) {
    static int A[MAXN], B[MAXN];
    int na = 0, nb = 0, i, j;
    for (i = 0; i < N; i++) {
        if (deg[i] < DMAX) {
            if (side[i] == 0) A[na++] = i; else B[nb++] = i;
        }
    }
    shuffle(A, na);
    shuffle(B, nb);
    for (i = 0; i < na; i++) {
        int a = A[i];
        for (j = 0; j < nb && deg[a] < DMAX; j++) {
            int b = B[j];
            if (deg[b] < DMAX && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void print_state(const State *s) {
    long long m2 = 0;
    int v, k;
    for (v = 0; v < s->n; v++) m2 += s->deg[v];
    printf("%d %lld\n", s->n, m2 / 2);
    for (v = 0; v < s->n; v++)
        for (k = 0; k < s->deg[v]; k++)
            if (s->adj[v][k] > v) printf("%d %d\n", v, s->adj[v][k]);
}

int main(int argc, char **argv) {
    int n, m, i, u, v, k;
    double budget;
    if (argc < 5) return 1;
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    T_START = clock();

    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 1 || n > MAXN - 200 || DMAX < 1 || DMAX > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) / 64;
    for (i = 0; i < N; i++) deg[i] = 0;
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || deg[u] >= DMAX || deg[v] >= DMAX) {
            printf("0 0\n");
            return 0;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    {
        static int q[MAXN];
        int h = 0, t = 0, s;
        for (i = 0; i < N; i++) side[i] = -1;
        for (s = 0; s < N; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            q[t++] = s;
            while (h < t) {
                int x = q[h++];
                for (k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (side[y] == -1) { side[y] = 1 - side[x]; q[t++] = y; }
                }
            }
        }
    }

    {
        int c0 = 0;
        for (i = 0; i < N; i++) if (side[i] == 0) c0++;
        take(&BEST);
        if (c0 == 0 || c0 == N) {
            print_state(&BEST);
            return 0;
        }
    }

    fill_spares();
    {
        int fails = 0;
        while (elapsed() < budget && fails < MAXFAILS && N < MAXN - 2) {
            long long cur;
            int it = 0;
            take(&SAVE);
            add_vertex(rndi(2));
            fill_spares();
            cur = bad_pairs();
            while (cur > 0 && it < ITERS && elapsed() < budget) {
                double T = pow(0.05, (double)it / ITERS);
                int a, c, b, e;
                long long nb;
                it++;
                a = rndi(N);
                if (deg[a] == 0) continue;
                b = adj[a][rndi(deg[a])];
                do { c = rndi(N); } while (side[c] != side[a]);
                if (c == a || deg[c] == 0) continue;
                e = adj[c][rndi(deg[c])];
                if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
                swap_apply(a, b, c, e);
                nb = bad_pairs();
                if (nb <= cur || rndf() < exp(-(double)(nb - cur) / T)) {
                    cur = nb;
                } else {
                    swap_apply(a, e, c, b);
                }
            }
            if (cur == 0) {
                fails = 0;
                if (N > BEST.n) take(&BEST);
            } else {
                put(&SAVE);
                fails++;
            }
        }
    }
    print_state(&BEST);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions and growth (unchanged base pipeline).
# ----------------------------------------------------------------------------

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


def _ball_rows(ball, idx, n):
    """float32 membership matrix: row r is the ball of idx[r] as a 0/1 vector."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover of all n vertices by at most d candidate rows."""
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
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
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
    t0 = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
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

    # Projective planes (used for D = 3, and for D >= 5 when no quadrangle applies).
    gq = _best_gq(d) if D >= 4 else None
    if gq is None and D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            slice_end = t0 + 0.25 * time_limit * (i + 1) / len(pg_qs)
            n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
            consider(n2, e2)

    # Generalized quadrangle base, grown by an iterated twin/cover pipeline.
    if gq is not None:
        consider(gq[0], gq[1])
        stage_end = t0 + 0.30 * time_limit
        cur = None
        top = None
        while time.monotonic() < stage_end:
            if cur is None or rng.random() < 0.2:
                src_n, src_e = gq[0], gq[1]
            else:
                frac = rng.uniform(0.05, 0.3)
                src_n, src_e = _remove_twins(cur[0], cur[1], frac, rng)
                src_e = _saturate_edges(src_n, src_e, d, rng)
            pn, pe = _pipeline(src_n, src_e, d, D, stage_end, rng)
            consider(pn, pe)
            if top is None or pn > top[0]:
                top = (pn, pe)
            if cur is None or pn >= cur[0]:
                cur = (pn, pe)
            elif pn >= cur[0] - 2 and rng.random() < 0.15:
                cur = (pn, pe)
            if cur[0] < top[0] - 4:
                cur = top

    # Bold stage: C annealing that adds vertices to the best graph so far.
    # Skipped when the Moore bound is already reached (e.g. calibration cases).
    if D >= 3 and best_n < lib.moore_bound(d, D):
        now = time.monotonic()
        budget = t0 + 0.82 * time_limit - now - 1.5
        if budget >= 2.0:
            try:
                timeout = max(1.0, t0 + 0.93 * time_limit - time.monotonic() - 1.0)
                txt = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=timeout)
                n2, e2 = lib.parse_graph_text(txt)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
