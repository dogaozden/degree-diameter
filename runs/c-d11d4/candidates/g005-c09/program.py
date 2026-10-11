import itertools
import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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


# ----------------------------------------------------------------------------
# Twin extension. A twin v of x (same side, N(v) = N(x)) keeps all old distances,
# has dist(v, x) = 2, and preserves bipartiteness. It needs one spare degree on
# each neighbour of x. Twins are added greedily in random passes until none remain.
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


def _remove_twins(n, edges, frac, rng):
    """Delete a random fraction of redundant twins; the diameter is preserved.

    In each class of vertices with identical neighbourhoods, one representative is
    kept. Freed degree lets growth try again.
    """
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
# Cover-based vertex extension.
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
    """Greedy set cover of `full` by at most d candidate vertices.

    With randomize=True, ties are broken at random and, fairly often, a
    slightly weaker candidate is taken, so repeated calls explore different covers.
    Returns the chosen list, or None if the cover fails.
    """
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


# ----------------------------------------------------------------------------
# Rarity-weighted set cover. Greedy covers can fail when a few vertices are
# hard to reach from the remaining candidates. Here each uncovered vertex w gets
# weight 1 / (number of still-available candidates covering w), so rare vertices
# dominate the choice. Vectorised with numpy on 0/1 membership rows.
# ----------------------------------------------------------------------------

def _ball_rows(ball, idx, n):
    """float32 membership matrix: row r is the ball (as 0/1 vector over n vertices) of idx[r]."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover of all n vertices by at most d candidate rows of sub.

    Returns the chosen candidate vertex list, or None if the cover fails.
    """
    k = sub.shape[0]
    uncovered = np.ones(n, dtype=np.float32)
    avail_b = np.ones(k, dtype=bool)
    chosen = []
    while uncovered.sum() > 0:
        if len(chosen) >= d or not avail_b.any():
            return None
        avail = avail_b.astype(np.float32)
        cnt = avail @ sub                      # available covers per vertex
        if np.any((uncovered > 0) & (cnt < 0.5)):
            return None                        # some uncovered vertex is unreachable now
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
    """Extend by cover vertices FIRST, then saturate edges with the remaining spare degree.

    Extension only adds vertices, and saturation only adds edges, so diameter is preserved.
    """
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
    """Alternate twin growth and cover growth until neither adds a vertex.

    Every step keeps diameter <= D and bipartiteness, so the result is valid
    whenever the input is.
    """
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
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Haar and cyclic-lift families, kept for D = 3 and as a secondary family.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# C engine: semidirect-product voltage lifts with a fast diameter check.
#
# The group acts on each lift by left multiplication, which is an automorphism.
# So the distances from (u, x) equal the distances from (u, identity) after a
# relabelling. Diameter <= D therefore needs only one BFS per base vertex, not one
# per vertex. The cost is the number of far vertices summed over base roots.
# A hill climb over the voltages runs in C. Output is the best lift larger than min_n.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NMAX 2000000
#define MTMAX 2000
#define KB 8
#define DMAX 64
#define ITERS 1500

static int d, D;
static int K, G, M, K2, R;
static int *PW, *MT, *vis, *Q;
static int useT = 0, stamp = 0;
static int nbv[2 * KB][DMAX], nbw[2 * KB][DMAX];
static int P[DMAX][KB];
static int dg[KB * DMAX];
static unsigned long long rs = 88172645463325252ULL;

static int found = 0, bK, bG, bM, bK2, bR;
static int bP[DMAX][KB];
static int bDg[KB * DMAX];

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd() % (unsigned long long)n); }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

/* Element (a,b) is coded as a*K2+b. (a,b)*(c,e) = (a + R^b c, b+e). */
static int gmul_f(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long A = ((long long)a + (long long)PW[b] * c) % M;
    int B = (b + e) % K2;
    return (int)(A * K2 + B);
}

static inline int gmul(int x, int y) {
    return useT ? MT[x * G + y] : gmul_f(x, y);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = (long long)PW[nb] * a % M;
    long long A = (M - t) % M;
    return (int)(A * K2 + nb);
}

static void set_group(int g) {
    int divs[256], nd = 0;
    G = g;
    for (int k2 = 1; k2 <= g / 2 && nd < 256; k2++)
        if (g % k2 == 0) divs[nd++] = k2;
    K2 = divs[rndi(nd)];
    M = G / K2;
    R = 1;
    if (K2 > 1 && M >= 3) {
        for (int t = 0; t < 60; t++) {
            int r = 1 + rndi(M - 1);
            if (gcd_i(r, M) == 1 && powmod(r, K2, M) == 1) { R = r; break; }
        }
    }
    PW[0] = 1 % M;
    for (int b = 1; b < K2; b++) PW[b] = (int)((long long)PW[b - 1] * R % M);
    useT = (G <= MTMAX);
    if (useT) {
        for (int x = 0; x < G; x++)
            for (int y = 0; y < G; y++)
                MT[x * G + y] = gmul_f(x, y);
    }
}

/* Far-vertex count summed over the base roots (u, identity). Zero iff diameter <= D. */
static long long cost(void) {
    int NV = 2 * K * G;
    long long c = 0;
    for (int u = 0; u < 2 * K; u++) {
        stamp++;
        int src = u * G;
        int head = 0, tail = 1;
        Q[0] = src;
        vis[src] = stamp;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int v = Q[head++];
                int bu = v / G, x = v - bu * G;
                for (int j = 0; j < d; j++) {
                    int w = nbv[bu][j];
                    int y = gmul(x, nbw[bu][j]);
                    int nv = w * G + y;
                    if (vis[nv] != stamp) {
                        vis[nv] = stamp;
                        Q[tail++] = nv;
                    }
                }
            }
        }
        c += NV - tail;
    }
    return c;
}

static void init_darts(void) {
    int perm[KB];
    for (int j = 0; j < d; j++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[r]; perm[r] = t;
        }
        for (int i = 0; i < K; i++) P[j][i] = perm[i];
    }
    for (int i = 0; i < K; i++) {
        for (int j = 0; j < d; j++) {
            int e = i * d + j;
            dg[e] = rndi(G);
            int t = K + P[j][i];
            nbv[i][j] = t;
            nbv[t][j] = i;
            nbw[i][j] = dg[e];
            nbw[t][j] = ginv(dg[e]);
        }
    }
}

static void set_dart(int i, int j, int g) {
    int e = i * d + j;
    dg[e] = g;
    int t = K + P[j][i];
    nbw[i][j] = g;
    nbw[t][j] = ginv(g);
}

static int attempt(int k, int g, int iters, clock_t dl) {
    K = k;
    set_group(g);
    init_darts();
    long long c = cost();
    for (int it = 0; it < iters && c > 0; it++) {
        if ((it & 63) == 0 && clock() > dl) break;
        int e = rndi(K * d);
        int i = e / d, j = e % d;
        int old = dg[e];
        int nw = (old + 1 + rndi(G - 1)) % G;
        set_dart(i, j, nw);
        long long c2 = cost();
        if (c2 <= c) c = c2;
        else set_dart(i, j, old);
    }
    return c == 0;
}

static void save_best(int k, int g) {
    bK = k; bG = g; bM = M; bK2 = K2; bR = R;
    for (int j = 0; j < d; j++)
        for (int i = 0; i < k; i++)
            bP[j][i] = P[j][i];
    for (int e = 0; e < k * d; e++)
        bDg[e] = dg[e];
    found = 1;
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

static void output(void) {
    if (!found) { printf("0 0\n"); return; }
    M = bM; K2 = bK2; R = bR;
    PW[0] = 1 % M;
    for (int b = 1; b < K2; b++) PW[b] = (int)((long long)PW[b - 1] * R % M);
    int k = bK, g = bG;
    int NV = 2 * k * g;
    long long total = (long long)k * d * g;
    long long *keys = malloc(sizeof(long long) * (size_t)total);
    if (!keys) { printf("0 0\n"); return; }
    long long cnt = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < d; j++) {
            int e = i * d + j;
            int t = k + bP[j][i];
            int gv = bDg[e];
            for (int x = 0; x < g; x++) {
                long long a = (long long)i * g + x;
                long long b = (long long)t * g + gmul_f(x, gv);
                keys[cnt++] = a * NV + b;
            }
        }
    qsort(keys, (size_t)cnt, sizeof(long long), cmp_ll);
    long long u = 0;
    for (long long q = 0; q < cnt; q++)
        if (u == 0 || keys[q] != keys[u - 1])
            keys[u++] = keys[q];
    printf("%d %lld\n", NV, u);
    for (long long q = 0; q < u; q++)
        printf("%lld %lld\n", keys[q] / NV, keys[q] % NV);
    free(keys);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int ch;
    while ((ch = getchar()) != EOF) {}
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > DMAX || D < 2) { printf("0 0\n"); return 0; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    vis = calloc(NMAX, sizeof(int));
    Q = malloc(sizeof(int) * NMAX);
    PW = malloc(sizeof(int) * NMAX);
    MT = malloc(sizeof(int) * (size_t)MTMAX * MTMAX);
    if (!vis || !Q || !PW || !MT) { printf("0 0\n"); return 0; }

    double budget = tl - 0.3;
    if (budget < 0) budget = 0;
    clock_t dl = clock() + (clock_t)(budget * CLOCKS_PER_SEC);
    int best_n = min_n;
    while (clock() < dl) {
        int k = 1 + rndi(4);
        int fl = best_n / (2 * k) + 1;
        if (fl < 2) fl = 2;
        if ((long long)2 * k * fl > NMAX) break;
        if (attempt(k, fl, ITERS, dl)) {
            save_best(k, fl);
            best_n = 2 * k * fl;
        }
    }
    output();
    return 0;
}
"""


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
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

    # D == 3: projective planes for the few largest prime powers q with q + 1 <= d,
    # each grown by the twin + cover pipeline within its time slice.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            ext_deadline = start + 0.5 * time_limit
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q) grown by an iterated search. Projective
    # planes are skipped here because they are far smaller than the W(q) growth.
    # Each round either restarts from the base W(q) or ruins the current best by
    # deleting redundant twins, then regrows with the pipeline. Every result is
    # checked by consider().
    if D >= 4:
        pipe_end = start + 0.35 * time_limit
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            cur = None
            while time.monotonic() < pipe_end:
                if cur is None or rng.random() < 0.2:
                    src_n, src_e = gq[0], gq[1]
                else:
                    src_n, src_e = _remove_twins(cur[0], cur[1], 0.15, rng)
                pn, pe = _pipeline(src_n, src_e, d, D, pipe_end, rng)
                consider(pn, pe)
                if cur is None or pn >= cur[0]:
                    cur = (pn, pe)

        # C voltage-lift search over semidirect products, starting from the current best
        # order. It runs until 0.88 of the time limit, leaving slack for compile and checks.
        c_end = start + 0.88 * time_limit
        if d >= 4:
            budget = c_end - time.monotonic() - 1.0
            if budget > 2.0:
                try:
                    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                                    timeout=budget + 10.0)
                    n2, e2 = lib.parse_graph_text(out)
                    consider(n2, e2)
                except Exception:
                    pass

    # Main Python search for the remaining time (group, Haar and cyclic lifts).
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
