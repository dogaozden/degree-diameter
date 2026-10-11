import itertools
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4200
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)

static int DEG_MAX = 3;
static int DIAM = 2;

static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];

static int bn = 0;
static int bcol[MAXN];
static int bdeg[MAXN];
static int badj[MAXN][MAXD];

static uint64_t RA[MAXN * MAXW];
static uint64_t RB[MAXN * MAXW];
static uint64_t RC[MAXN * MAXW];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_idx(int x, int y) {
    for (int i = 0; i < deg[x]; i++)
        if (adj[x][i] == y) return i;
    return -1;
}

static int is_adj(int x, int y) { return find_idx(x, y) >= 0; }

static void add_e(int x, int y) {
    adj[x][deg[x]++] = y;
    adj[y][deg[y]++] = x;
}

static void del_e(int x, int y) {
    int i = find_idx(x, y);
    adj[x][i] = adj[x][--deg[x]];
    int j = find_idx(y, x);
    adj[y][j] = adj[y][--deg[y]];
}

/* Bitset reach: out[v] = set of vertices within distance r of v. */
static uint64_t *reach(int n, int r, uint64_t *out) {
    int W = (n + 63) >> 6;
    size_t tot = (size_t)n * (size_t)W;
    uint64_t *A = out, *B = RB;
    memset(A, 0, sizeof(uint64_t) * tot);
    for (int v = 0; v < n; v++)
        A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *bv = B + (size_t)v * W;
            const uint64_t *av = A + (size_t)v * W;
            memcpy(bv, av, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *au = A + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) bv[w] |= au[w];
            }
        }
        uint64_t *t = A; A = B; B = t;
    }
    if (A != out) memcpy(out, A, sizeof(uint64_t) * tot);
    return out;
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long cost_bad(int n) {
    int W = (n + 63) >> 6;
    uint64_t *R = reach(n, DIAM, RA);
    long long tot = 0;
    size_t cnt = (size_t)n * (size_t)W;
    for (size_t i = 0; i < cnt; i++) tot += popc(R[i]);
    return ((long long)n * n - tot) / 2;
}

static void shuffle_int(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add edges between deficient opposite-side vertices (never hurts validity). */
static void saturate(int n) {
    static int L0[MAXN], L1[MAXN];
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < DEG_MAX) {
            if (col[v] == 0) L0[c0++] = v; else L1[c1++] = v;
        }
    }
    shuffle_int(L0, c0);
    shuffle_int(L1, c1);
    for (int i = 0; i < c0; i++) {
        int a = L0[i];
        for (int j = 0; j < c1 && deg[a] < DEG_MAX; j++) {
            int b = L1[j];
            if (deg[b] < DEG_MAX && !is_adj(a, b)) add_e(a, b);
        }
    }
}

/* Insert vertex n whose neighbourhood greedily covers the radius-(DIAM-1) balls. */
static int insert_vertex(int n) {
    if (n >= MAXN - 1) return 0;
    int W = (n + 63) >> 6;
    int s = rnd(2);
    uint64_t *R = reach(n, DIAM - 1, RC);
    uint64_t unc[MAXW];
    for (int w = 0; w < W; w++) unc[w] = ~0ULL;
    if (n & 63) unc[W - 1] = (1ULL << (n & 63)) - 1ULL;
    static char taken[MAXN];
    memset(taken, 0, sizeof(char) * (size_t)n);
    int chosen[MAXD];
    int nc = 0;
    for (int t = 0; t < DEG_MAX; t++) {
        long long best_s = -1;
        int best_v = -1;
        for (int v = 0; v < n; v++) {
            if (col[v] == s || taken[v]) continue;
            const uint64_t *rv = R + (size_t)v * W;
            long long g = 0;
            for (int w = 0; w < W; w++) g += popc(rv[w] & unc[w]);
            long long sc = g * 64 + (deg[v] < DEG_MAX ? 32 : 0) + rnd(32);
            if (sc > best_s) { best_s = sc; best_v = v; }
        }
        if (best_v < 0) break;
        taken[best_v] = 1;
        chosen[nc++] = best_v;
        const uint64_t *rb = R + (size_t)best_v * W;
        for (int w = 0; w < W; w++) unc[w] &= ~rb[w];
    }
    if (nc < DEG_MAX) return 0;
    col[n] = s;
    deg[n] = 0;
    for (int t = 0; t < nc; t++) {
        int b = chosen[t];
        if (deg[b] >= DEG_MAX) {
            int x = adj[b][rnd(deg[b])];
            del_e(b, x);
        }
        add_e(n, b);
    }
    return 1;
}

/* Moves: degree-preserving 2-switch, or endpoint shift into spare degree. */
enum { MV_SW = 0, MV_B1 = 1, MV_B2 = 2 };
static int mv_t, mv_a, mv_b, mv_c, mv_d;

static int propose(int n) {
    static int D0[MAXN], D1[MAXN];
    int a = -1;
    for (int t = 0; t < 200; t++) {
        int x = rnd(n);
        if (col[x] == 0 && deg[x] > 0) { a = x; break; }
    }
    if (a < 0) return 0;
    int b = adj[a][rnd(deg[a])];
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < DEG_MAX) {
            if (col[v] == 0) D0[c0++] = v; else D1[c1++] = v;
        }
    }
    double r = rnd01();
    if (r < 0.6 || (c0 == 0 && c1 == 0)) {
        int c = -1;
        for (int t = 0; t < 200; t++) {
            int x = rnd(n);
            if (col[x] == 0 && deg[x] > 0 && x != a) { c = x; break; }
        }
        if (c < 0) return 0;
        int dd = adj[c][rnd(deg[c])];
        if (dd == b || is_adj(a, dd) || is_adj(c, b)) return 0;
        mv_t = MV_SW; mv_a = a; mv_b = b; mv_c = c; mv_d = dd;
        return 1;
    }
    if (c1 > 0 && (c0 == 0 || rnd(2) == 0)) {
        int b2 = D1[rnd(c1)];
        if (b2 == b || is_adj(a, b2)) return 0;
        mv_t = MV_B1; mv_a = a; mv_b = b; mv_c = b2; mv_d = 0;
        return 1;
    }
    int a2 = D0[rnd(c0)];
    if (a2 == a || is_adj(a2, b)) return 0;
    mv_t = MV_B2; mv_a = a; mv_b = b; mv_c = a2; mv_d = 0;
    return 1;
}

static void apply_mv(void) {
    switch (mv_t) {
    case MV_SW:
        del_e(mv_a, mv_b); del_e(mv_c, mv_d);
        add_e(mv_a, mv_d); add_e(mv_c, mv_b);
        break;
    case MV_B1:
        del_e(mv_a, mv_b); add_e(mv_a, mv_c);
        break;
    default:
        del_e(mv_a, mv_b); add_e(mv_c, mv_b);
        break;
    }
}

static void undo_mv(void) {
    switch (mv_t) {
    case MV_SW:
        del_e(mv_a, mv_d); del_e(mv_c, mv_b);
        add_e(mv_a, mv_b); add_e(mv_c, mv_d);
        break;
    case MV_B1:
        del_e(mv_a, mv_c); add_e(mv_a, mv_b);
        break;
    default:
        del_e(mv_c, mv_b); add_e(mv_a, mv_b);
        break;
    }
}

static long long anneal(int n, int iters, double T0, double T1, clock_t end) {
    long long cur = cost_bad(n);
    for (int it = 0; it < iters && cur > 0; it++) {
        if (clock() >= end) break;
        if (!propose(n)) continue;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        apply_mv();
        long long nc = cost_bad(n);
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nc;
        else undo_mv();
    }
    return cur;
}

static void snapshot(int n) {
    bn = n;
    memcpy(bcol, col, sizeof(int) * (size_t)n);
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(adj[0]) * (size_t)n);
}

static int restore(void) {
    memcpy(col, bcol, sizeof(int) * (size_t)bn);
    memcpy(deg, bdeg, sizeof(int) * (size_t)bn);
    memcpy(adj, badj, sizeof(adj[0]) * (size_t)bn);
    return bn;
}

static int EU[MAXN * MAXD];
static int EV[MAXN * MAXD];
static int Q[MAXN];

static void print_fail(void) { printf("0 0\n"); }

int main(int argc, char **argv) {
    if (argc < 5) { print_fail(); return 0; }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    rs ^= 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    int iters = argc > 5 ? atoi(argv[5]) : 1500;
    if (iters < 10) iters = 10;
    clock_t end = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);
    if (d < 1 || d > MAXD || DIAM < 2) { print_fail(); return 0; }
    DEG_MAX = d;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { print_fail(); return 0; }
    if (n < 1 || n > MAXN - 2 || m < 0 || m > MAXN * MAXD) { print_fail(); return 0; }
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { print_fail(); return 0; }
        EU[i] = u; EV[i] = v;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { print_fail(); return 0; }
        if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX || is_adj(u, v)) { print_fail(); return 0; }
        add_e(u, v);
    }

    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        Q[tail++] = s;
        while (head < tail) {
            int x = Q[head++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (col[y] < 0) { col[y] = 1 - col[x]; Q[tail++] = y; }
                else if (col[y] == col[x]) { print_fail(); return 0; }
            }
        }
    }

    saturate(n);
    if (cost_bad(n) != 0) { print_fail(); return 0; }
    snapshot(n);

    int cn = n;
    while (clock() < end && cn < MAXN - 2) {
        if (!insert_vertex(cn)) break;
        cn++;
        saturate(cn);
        long long c = anneal(cn, iters, 3.0, 0.2, end);
        if (c == 0) {
            saturate(cn);
            snapshot(cn);
        } else {
            cn = restore();
        }
    }

    long long me = 0;
    for (int v = 0; v < bn; v++) me += bdeg[v];
    me /= 2;
    printf("%d %lld\n", bn, me);
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[v][k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): order 2(q+1)(q^2+1), degree q+1, diameter 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q)."""
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
    """W(q) for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Twin growth: a twin of x (same side, same neighbourhood) keeps old distances.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
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


# ----------------------------------------------------------------------------
# Cover-based vertex extension (Python side).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _ball_rows(ball, idx, n):
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
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
    sub = _ball_rows(ball, cands, n)
    for t in range(tries):
        if time.monotonic() >= deadline:
            break
        ch = _weighted_cover(sub, cands, n, d, rng, t > 0)
        if ch:
            return ch
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
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
# C augmentation: insert vertices and anneal (2-switches and endpoint shifts)
# until the diameter is restored, keeping the last valid graph.
# ----------------------------------------------------------------------------

def _c_augment(d, D, seed, n, edges, deadline):
    remaining = deadline - time.monotonic()
    if remaining < 3.0:
        return None
    budget = remaining - 2.5
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", 1500],
                         stdin_graph=(n, edges), timeout=remaining)
        return lib.parse_graph_text(text)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

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

    py_end = start + 0.40 * time_limit

    # D = 3: projective planes, grown by the Python pipeline.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, py_end - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown by the Python pipeline.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            cur = None
            while time.monotonic() < py_end:
                if cur is None or rng.random() < 0.2:
                    src_n, src_e = gq[0], gq[1]
                else:
                    src_n, src_e = _remove_twins(cur[0], cur[1], 0.15, rng)
                pn, pe = _pipeline(src_n, src_e, d, D, py_end, rng)
                consider(pn, pe)
                if cur is None or pn >= cur[0]:
                    cur = (pn, pe)

    # Remaining time: C vertex insertion and annealing from the best graph so far.
    if d >= 2 and D >= 2:
        res = _c_augment(d, D, seed, best[0], best[1], start + 0.90 * time_limit)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
