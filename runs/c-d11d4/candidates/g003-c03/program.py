import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: hill-climbing over voltage lifts on abelian groups Z_A x Z_B.
#
# The base multigraph has K vertices per side and is d-regular (d permutations).
# Because the group is abelian, the lift has translation symmetry, so the
# distance from (u, x) to (w, y) equals the distance from (u, 0) to (w, y - x).
# Therefore only the 2K base vertices need BFS from their zero-fibre vertex.
# Cost = total number of vertices not reached within distance D over those BFS.
# Cost 0 means the lift has diameter <= D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define MAXN 65536

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d, D, K, A, B, G;
static int perm[MAXD][MAXK];
static int vu[MAXD][MAXK], vv[MAXD][MAXK];
static int nbw[2 * MAXK][MAXD], nbhu[2 * MAXK][MAXD], nbhv[2 * MAXK][MAXD];
static int dist[MAXN], qu[MAXN];

static void build_base(void) {
    int cnt[2 * MAXK];
    memset(cnt, 0, sizeof cnt);
    for (int j = 0; j < d; j++) {
        for (int i = 0; i < K; i++) {
            int m = perm[j][i];
            int b = K + m;
            int c = cnt[i]++;
            nbw[i][c] = b; nbhu[i][c] = vu[j][i]; nbhv[i][c] = vv[j][i];
            c = cnt[b]++;
            nbw[b][c] = i; nbhu[b][c] = (A - vu[j][i]) % A; nbhv[b][c] = (B - vv[j][i]) % B;
        }
    }
}

static long cost_eval(void) {
    int N = 2 * K * G;
    long cost = 0;
    build_base();
    for (int s = 0; s < 2 * K; s++) {
        for (int t = 0; t < N; t++) dist[t] = -1;
        int head = 0, tail = 0;
        qu[tail++] = s * G;
        dist[s * G] = 0;
        while (head < tail) {
            int y = qu[head++];
            if (dist[y] >= D) continue;
            int u = y / G, x = y % G;
            int xu = x / B, xv = x % B;
            for (int t = 0; t < d; t++) {
                int w = nbw[u][t];
                int z = w * G + ((xu + nbhu[u][t]) % A) * B + (xv + nbhv[u][t]) % B;
                if (dist[z] < 0) { dist[z] = dist[y] + 1; qu[tail++] = z; }
            }
        }
        cost += N - tail;
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 8) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 1;
    if (rs == 0) rs = 1;
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    A = atoi(argv[6]);
    B = atoi(argv[7]);
    int iters = argc > 8 ? atoi(argv[8]) : 6000;
    if (d < 1 || d > MAXD || K < 1 || K > MAXK || A < 1 || B < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    G = A * B;
    if (2 * K * G > MAXN) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    int found = 0;
    long c = 0;
    while (!found && now() - t0 < limit) {
        for (int j = 0; j < d; j++) {
            for (int i = 0; i < K; i++) perm[j][i] = i;
            for (int i = K - 1; i > 0; i--) {
                int r = rndi(i + 1);
                int tmp = perm[j][i];
                perm[j][i] = perm[j][r];
                perm[j][r] = tmp;
            }
            for (int i = 0; i < K; i++) {
                vu[j][i] = rndi(A);
                vv[j][i] = rndi(B);
            }
        }
        c = cost_eval();
        for (int it = 0; it < iters && c > 0; it++) {
            if ((it & 31) == 0 && now() - t0 >= limit) break;
            int j = rndi(d), i = rndi(K);
            int ou = vu[j][i], ov = vv[j][i];
            vu[j][i] = rndi(A);
            vv[j][i] = rndi(B);
            long c2 = cost_eval();
            if (c2 <= c) {
                c = c2;
            } else {
                vu[j][i] = ou;
                vv[j][i] = ov;
            }
        }
        if (c == 0) found = 1;
    }
    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int N = 2 * K * G, M = K * d * G;
    printf("%d %d\n", N, M);
    for (int j = 0; j < d; j++) {
        for (int i = 0; i < K; i++) {
            int m = perm[j][i];
            for (int x = 0; x < G; x++) {
                int xu = x / B, xv = x % B;
                int z = ((xu + vu[j][i]) % A) * B + (xv + vv[j][i]) % B;
                printf("%d %d\n", i * G + x, (K + m) * G + z);
            }
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Fallback constructions (kept from the parent): W(q) quadrangle and growth.
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


def _twin_grow(n, edges, d, rng, deadline):
    """Add twins of vertices while all neighbours have spare degree (keeps diameter)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = list(range(n))
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
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


def _extend_cover(n, edges, d, D, deadline, rng):
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


# ----------------------------------------------------------------------------
# New family: abelian (not necessarily cyclic) voltage lifts, run by the C engine.
# The parent only sampled cyclic groups for prime-square orders (e.g. 289 = 17^2),
# which is where the non-cyclic Z_17 x Z_17 lifts live.
# ----------------------------------------------------------------------------

def _abelian_groups(G):
    """Invariant-factor pairs (a, b) with a | b and a * b = G."""
    out = []
    for a in range(1, math.isqrt(G) + 1):
        if G % a == 0 and (G // a) % a == 0:
            out.append((a, G // a))
    return out


def _configs(d, bound, best_n, max_k=6, max_n=60000):
    """(N, k, a, b) configurations with N = 2*k*a*b in (best_n, bound]; non-cyclic first, then by N."""
    cfgs = []
    for k in range(1, max_k + 1):
        lo = best_n // (2 * k) + 1
        hi = min(bound, max_n) // (2 * k)
        for G in range(lo, hi + 1):
            for a, b in _abelian_groups(G):
                cfgs.append((2 * k * G, k, a, b))
    cfgs.sort(key=lambda t: (t[2] == 1, t[0]))
    return cfgs


def _lift_search(d, D, best_n, deadline, rng, slice_s):
    """Run the C lift search over abelian configurations. Returns (n, edges) or None."""
    bound = lib.moore_bound(d, D)
    best = None
    for N, k, a, b in _configs(d, bound, best_n):
        if N <= best_n:
            continue
        now = time.monotonic()
        if deadline - now < 1.0:
            break
        budget = min(slice_s, deadline - now)
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, rng.randrange(1 << 30), round(budget, 2), k, a, b, 6000],
                             timeout=budget + 20.0)
            n, edges = lib.parse_graph_text(text)
        except (RuntimeError, ValueError):
            continue
        if n == 0 or not edges:
            continue
        edges = sorted({(min(u, v), max(u, v)) for u, v in edges})
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    bound = lib.moore_bound(d, D)

    # D = 3: projective plane incidence graphs, grown by cover extension.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, start + 0.15 * time_limit - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown by twins and cover extension.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            base_n, base_e = gq
            stage_end = start + 0.3 * time_limit
            for restart in range(4):
                if time.monotonic() >= stage_end:
                    break
                if restart % 2 == 0:
                    tn, te = _twin_grow(base_n, base_e, d, rng, stage_end)
                    n4, e4 = _grow(tn, te, d, D, stage_end, rng)
                else:
                    gn, ge = _grow(base_n, base_e, d, D, stage_end, rng)
                    tn, te = _twin_grow(gn, ge, d, rng, stage_end)
                    n4, e4 = _grow(tn, te, d, D, stage_end, rng)
                consider(n4, e4)

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= bound:
        return best

    # Main search: abelian voltage lifts from the C engine.
    if d >= 2 and D >= 2:
        try:
            res = _lift_search(d, D, best_n, deadline, rng, 2.0)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
