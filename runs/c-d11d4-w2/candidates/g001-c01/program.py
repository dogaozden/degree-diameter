"""Combined search: Python constructions and growth, then C annealing with grow-by-two.

Pipeline:
  1. D = 3: projective plane PG(2, d-1) if d-1 is a prime power (Moore graph, returned at once).
     Otherwise the Araujo-Pardo and Lopez graph for d-2 when that is a prime power.
  2. D >= 4: the generalized quadrangle incidence graph W(q), q the largest prime power <= d-1.
  3. D >= 3: twin growth and cover-based vertex extension (from the best Python start).
  4. C simulated annealing: insert one new vertex pair (x, y) joined to each other, then anneal
     degree-preserving moves until every pair is within D. Each success becomes the new start.
Every candidate is checked with lib.is_valid before it can replace the best graph.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on a fixed vertex set. The input graph gets one
# extra isolated vertex. Moves are degree-preserving edge swaps, edge additions
# and endpoint rewires. The cost is the number of vertex pairs at distance > D,
# computed with bitset balls. The first zero-cost graph is printed and the run
# stops. Otherwise it prints "0 0" and Python keeps its fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int N, DEGMAX, DIAM, W, EM, CM, CAP;
static int *eu, *ev, *cu, *cv;
static int *side, *deg, *off, *adj, *cdeg, *coff, *cadj;
static int *pos, *sp0, *sp1, *bfsq;
static u64 *bx, *by;
static u64 rs;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int *ialloc(size_t k) {
    int *p = (int *)calloc(k ? k : 1, sizeof(int));
    if (!p) exit(0);
    return p;
}

static void build_csr(int m, const int *a, const int *b, int *dg, int *of, int *ad) {
    int i;
    for (i = 0; i < N; i++) dg[i] = 0;
    for (i = 0; i < m; i++) { dg[a[i]]++; dg[b[i]]++; }
    of[0] = 0;
    for (i = 0; i < N; i++) of[i + 1] = of[i] + dg[i];
    for (i = 0; i < N; i++) pos[i] = of[i];
    for (i = 0; i < m; i++) {
        ad[pos[a[i]]++] = b[i];
        ad[pos[b[i]]++] = a[i];
    }
}

static int isadj(const int *dg, const int *of, const int *ad, int x, int y) {
    int i;
    for (i = of[x]; i < of[x] + dg[x]; i++)
        if (ad[i] == y) return 1;
    return 0;
}

static long long bad_cost(const int *dg, const int *of, const int *ad) {
    u64 *X = bx, *Y = by, *t;
    int v, r, w, i;
    long long cov = 0;
    memset(X, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (v = 0; v < N; v++) X[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            u64 *y = Y + (size_t)v * W;
            const u64 *x = X + (size_t)v * W;
            memcpy(y, x, sizeof(u64) * (size_t)W);
            for (i = of[v]; i < of[v] + dg[v]; i++) {
                const u64 *z = X + (size_t)ad[i] * W;
                for (w = 0; w < W; w++) y[w] |= z[w];
            }
        }
        t = X; X = Y; Y = t;
    }
    for (i = 0; i < N * W; i++) cov += popc(X[i]);
    return ((long long)N * N - cov) / 2;
}

static int collect(int s, int *out) {
    int v, c = 0;
    for (v = 0; v < N; v++)
        if (side[v] == s && deg[v] < DEGMAX) out[c++] = v;
    return c;
}

static int move_add(void) {
    int n0, n1, t, a, b;
    if (CM >= CAP) return 0;
    n0 = collect(0, sp0);
    n1 = collect(1, sp1);
    if (n0 == 0 || n1 == 0) return 0;
    for (t = 0; t < 20; t++) {
        a = sp0[rndint(n0)];
        b = sp1[rndint(n1)];
        if (!isadj(deg, off, adj, a, b)) {
            cu[CM] = a;
            cv[CM] = b;
            CM++;
            return 1;
        }
    }
    return 0;
}

static int move_swap(void) {
    int i, j, a, b, c, e;
    if (CM < 2) return 0;
    i = rndint(CM);
    j = rndint(CM);
    if (i == j) return 0;
    a = cu[i]; b = cv[i];
    c = cu[j]; e = cv[j];
    if (a == c || b == e) return 0;
    if (isadj(deg, off, adj, a, e) || isadj(deg, off, adj, c, b)) return 0;
    cv[i] = e;
    cv[j] = b;
    return 1;
}

static int move_rewire(void) {
    int i, a, b, n, t, c;
    if (CM == 0) return 0;
    i = rndint(CM);
    a = cu[i]; b = cv[i];
    if (rnd() & 1ULL) {
        n = collect(0, sp0);
        for (t = 0; t < 20 && n > 0; t++) {
            c = sp0[rndint(n)];
            if (c != a && !isadj(deg, off, adj, c, b)) { cu[i] = c; return 1; }
        }
    } else {
        n = collect(1, sp1);
        for (t = 0; t < 20 && n > 0; t++) {
            c = sp1[rndint(n)];
            if (c != b && !isadj(deg, off, adj, a, c)) { cv[i] = c; return 1; }
        }
    }
    return 0;
}

static void emit(const int *a, const int *b, int m) {
    int i;
    printf("%d %d\n", N, m);
    for (i = 0; i < m; i++) printf("%d %d\n", a[i], b[i]);
}

int main(int argc, char **argv) {
    int n, m, i, k, s, qh, qt, ok, x, y;
    int *ru, *rv;
    double budget, T, el, frac, r, T0 = 8.0, T1 = 0.25;
    long long cur, cand, delta;
    clock_t c0;

    if (argc < 5) return 1;
    DEGMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);

    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    W = (N + 63) / 64;
    CAP = N * DEGMAX + 16;
    if (m > CAP) { printf("0 0\n"); return 0; }

    ru = ialloc(CAP);
    rv = ialloc(CAP);
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) { printf("0 0\n"); return 0; }
        if (ru[i] < 0 || ru[i] >= N || rv[i] < 0 || rv[i] >= N || ru[i] == rv[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    side = ialloc(N); deg = ialloc(N); off = ialloc(N + 1); adj = ialloc(2 * CAP);
    cdeg = ialloc(N); coff = ialloc(N + 1); cadj = ialloc(2 * CAP);
    pos = ialloc(N); sp0 = ialloc(N); sp1 = ialloc(N); bfsq = ialloc(N);
    eu = ialloc(CAP); ev = ialloc(CAP); cu = ialloc(CAP); cv = ialloc(CAP);
    bx = (u64 *)calloc((size_t)N * W, sizeof(u64));
    by = (u64 *)calloc((size_t)N * W, sizeof(u64));
    if (!bx || !by) return 0;

    EM = m;
    build_csr(EM, ru, rv, deg, off, adj);
    for (i = 0; i < N; i++) if (deg[i] > DEGMAX) { printf("0 0\n"); return 0; }

    for (i = 0; i < N; i++) side[i] = -1;
    for (s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        qh = 0; qt = 0;
        bfsq[qt++] = s;
        while (qh < qt) {
            x = bfsq[qh++];
            for (k = off[x]; k < off[x] + deg[x]; k++) {
                y = adj[k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    bfsq[qt++] = y;
                } else if (side[y] == side[x]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    for (i = 0; i < EM; i++) {
        if (side[ru[i]] == 0) { eu[i] = ru[i]; ev[i] = rv[i]; }
        else { eu[i] = rv[i]; ev[i] = ru[i]; }
    }
    build_csr(EM, eu, ev, deg, off, adj);
    cur = bad_cost(deg, off, adj);
    if (cur == 0) { emit(eu, ev, EM); return 0; }

    c0 = clock();
    for (;;) {
        el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= budget) break;
        frac = el / budget;
        T = T0 * pow(T1 / T0, frac);

        memcpy(cu, eu, sizeof(int) * (size_t)EM);
        memcpy(cv, ev, sizeof(int) * (size_t)EM);
        CM = EM;

        r = rnd01();
        if (r < 0.25) ok = move_add();
        else if (r < 0.65) ok = move_swap();
        else ok = move_rewire();
        if (!ok) continue;

        build_csr(CM, cu, cv, cdeg, coff, cadj);
        cand = bad_cost(cdeg, coff, cadj);
        delta = cand - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            int *tp;
            tp = eu; eu = cu; cu = tp;
            tp = ev; ev = cv; cv = tp;
            tp = deg; deg = cdeg; cdeg = tp;
            tp = off; off = coff; coff = tp;
            tp = adj; adj = cadj; cadj = tp;
            EM = CM;
            cur = cand;
            if (cur == 0) { emit(eu, ev, EM); return 0; }
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Algebraic starting graphs.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Python growth: twins, then cover-based vertex extension, then edge saturation.
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
    """Greedy set cover of `full` by at most d candidate vertices. None if it fails."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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
    """Extend by cover vertices first, then saturate edges with the remaining spare degree."""
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
# C annealing grow-by-two: add a vertex pair (x, y) joined to each other, anneal.
# ----------------------------------------------------------------------------

def _anneal_grow(d, D, base, seed, budget):
    """Run the C annealer on base plus a new edge x-y (two new vertices). Returns (n, edges) or None."""
    n, edges = base
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(n + 2, list(edges) + [(n, n + 1)]),
                        timeout=budget + 4.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 != n + 2 or not e2:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    # Trivial cases: K_2 is optimal for D = 1 or d = 1.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(res):
        nonlocal best, best_n
        if res is None:
            return False
        n, e = res
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n
            return True
        return False

    done = False
    try:
        # D = 3: optimal Moore graph when d-1 is a prime power; otherwise the record family.
        if D == 3:
            if lib.is_prime_power(d - 1):
                consider(lib.projective_plane_incidence(d - 1))
                done = True
            elif d - 2 >= 3 and lib.is_prime_power(d - 2):
                consider(lib.araujo_lopez_graph(d - 2))

        # D >= 4: generalized quadrangle W(q), q the largest prime power <= d - 1.
        if D >= 4 and not done:
            q = next((q for q in range(d - 1, 1, -1) if q <= 16 and lib.is_prime_power(q)), None)
            if q is not None:
                consider(_gq_w(q))

        # Python growth: twins plus cover extension, several rounds from the start graph.
        if D >= 3 and not done:
            pipe_end = t0 + (0.35 if D >= 4 else 0.30) * time_limit
            start_graph = best
            cur = best
            rounds = 0
            while time.monotonic() < pipe_end and rounds < 6:
                rounds += 1
                if rounds == 1 or rng.random() < 0.2:
                    src = start_graph
                else:
                    src = _remove_twins(cur[0], cur[1], 0.15, rng)
                pn, pe = _pipeline(src[0], src[1], d, D, pipe_end, rng)
                consider((pn, pe))
                if pn >= cur[0]:
                    cur = (pn, pe)

        # C annealing: repeatedly grow the best graph by a vertex pair.
        if not done and best_n > 1:
            c_end = t0 + 0.86 * time_limit
            fails = 0
            while fails < 3:
                rem = c_end - time.monotonic()
                if rem < 6.0:
                    break
                budget = max(3.0, (rem - 3.0) * 0.5)
                res = _anneal_grow(d, D, best, rng.randrange(1, 1 << 30), budget)
                if not consider(res):
                    fails += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
