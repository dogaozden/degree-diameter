import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Simulated annealing on bipartite edge switches.
   Input: graph (n m, then m edges), max degree d, diameter D, seed, CPU budget (s).
   Objective: number of unordered vertex pairs at distance > D.
   Moves keep the bipartition (edge endpoints stay on their colour side):
     switch  (a,b),(c,e) -> (a,e),(c,b)
     rewire  move one endpoint of an edge onto a vertex with spare degree.
   Greedy edge additions between deficient opposite-side vertices come first,
   since they never increase any distance.
   Prints the zero-cost graph ("n m" + edges) or "0 0". */

static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int rndint(int k) {
    return (int)(rnd() % (uint64_t)k);
}

static int N, DEG, DIAM, W, M;
static int *eA, *eB, *colr, *nb, *dg;
static unsigned char *adj;
static uint64_t *bufA, *bufB;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void nb_del(int v, int u) {
    int *p = nb + (size_t)v * DEG;
    for (int i = 0; i < dg[v]; i++) {
        if (p[i] == u) {
            p[i] = p[dg[v] - 1];
            dg[v]--;
            return;
        }
    }
}

static void nb_add(int v, int u) {
    nb[(size_t)v * DEG + dg[v]] = u;
    dg[v]++;
}

static void unlink_e(int i) {
    int a = eA[i], b = eB[i];
    adj[(size_t)a * N + b] = 0;
    adj[(size_t)b * N + a] = 0;
    nb_del(a, b);
    nb_del(b, a);
}

static void add_e(int i, int a, int b) {
    eA[i] = a;
    eB[i] = b;
    adj[(size_t)a * N + b] = 1;
    adj[(size_t)b * N + a] = 1;
    nb_add(a, b);
    nb_add(b, a);
}

/* Number of ordered (v,w) pairs with dist(v,w) > DIAM, divided by 2. */
static long eval_bad(void) {
    uint64_t *cur = bufA, *nxt = bufB, *t;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                int u = nb[(size_t)v * DEG + i];
                uint64_t *q = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) o[w] |= q[w];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc64(s[w]);
        tot += N - c;
    }
    return tot / 2;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int k = 0; k < 20; k++) rnd();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    DEG = d;
    DIAM = D;
    N = n;
    W = (N + 63) / 64;
    int MCAP = N * DEG / 2 + m + 2;
    eA = malloc(sizeof(int) * (size_t)MCAP);
    eB = malloc(sizeof(int) * (size_t)MCAP);
    colr = malloc(sizeof(int) * (size_t)N);
    nb = malloc(sizeof(int) * (size_t)N * DEG);
    dg = calloc((size_t)N, sizeof(int));
    adj = calloc((size_t)N * N, 1);
    bufA = malloc(sizeof(uint64_t) * (size_t)N * W);
    bufB = malloc(sizeof(uint64_t) * (size_t)N * W);
    int *tu = malloc(sizeof(int) * (size_t)(m + 1));
    int *tv = malloc(sizeof(int) * (size_t)(m + 1));

    /* Read edges and build temporary adjacency for the bipartition check. */
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
        if (adj[(size_t)u * N + v] || dg[u] >= DEG || dg[v] >= DEG) { ok = 0; break; }
        adj[(size_t)u * N + v] = 1;
        adj[(size_t)v * N + u] = 1;
        nb_add(u, v);
        nb_add(v, u);
        tu[i] = u;
        tv[i] = v;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    /* BFS two-colouring. */
    int *queue = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) colr[v] = -1;
    for (int s = 0; s < N; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            for (int k = 0; k < dg[u]; k++) {
                int v = nb[(size_t)u * DEG + k];
                if (colr[v] < 0) {
                    colr[v] = 1 - colr[u];
                    queue[tail++] = v;
                } else if (colr[v] == colr[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    /* Reset and relink with orientation: eA is colour 0, eB is colour 1. */
    memset(adj, 0, (size_t)N * N);
    for (int v = 0; v < N; v++) dg[v] = 0;
    M = 0;
    for (int i = 0; i < m; i++) {
        int a = tu[i], b = tv[i];
        if (colr[a] != 0) { int t = a; a = b; b = t; }
        add_e(M, a, b);
        M++;
    }

    /* Greedy additions between deficient opposite-side vertices. */
    int *dA = malloc(sizeof(int) * (size_t)N);
    int *dB = malloc(sizeof(int) * (size_t)N);
    int nA = 0, nB = 0;
    for (int v = 0; v < N; v++) {
        if (dg[v] < DEG) {
            if (colr[v] == 0) dA[nA++] = v;
            else dB[nB++] = v;
        }
    }
    shuffle_int(dA, nA);
    shuffle_int(dB, nB);
    for (int p = 0; p < nA; p++) {
        int a = dA[p];
        for (int q = 0; q < nB && dg[a] < DEG; q++) {
            int b = dB[q];
            if (dg[b] < DEG && !adj[(size_t)a * N + b] && M < MCAP) {
                add_e(M, a, b);
                M++;
            }
        }
    }

    long cost = eval_bad();
    int *defs = malloc(sizeof(int) * (size_t)N);
    clock_t t0 = clock();
    const double T0 = 1.0, T1 = 0.03;
    double T = T0;
    long it = 0;

    while (cost > 0 && M >= 2) {
        if ((it & 7) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
            T = T0 * pow(T1 / T0, el / budget);
        }
        it++;
        if (rnd01() < 0.3) {
            /* Rewire: give a deficient vertex x one more neighbour, taking an edge from another vertex. */
            int nd = 0;
            for (int v = 0; v < N; v++)
                if (dg[v] < DEG) defs[nd++] = v;
            if (nd == 0) continue;
            int x = defs[rndint(nd)];
            int i = rndint(M);
            int a = eA[i], b = eB[i];
            if (colr[x] == 0) {
                if (adj[(size_t)x * N + b]) continue;
                unlink_e(i);
                add_e(i, x, b);
                long c2 = eval_bad();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    unlink_e(i);
                    add_e(i, a, b);
                }
            } else {
                if (adj[(size_t)a * N + x]) continue;
                unlink_e(i);
                add_e(i, a, x);
                long c2 = eval_bad();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    unlink_e(i);
                    add_e(i, a, b);
                }
            }
        } else {
            /* Switch: (a,b),(c,e) -> (a,e),(c,b). Degrees and bipartition are preserved. */
            int i = rndint(M), j = rndint(M);
            if (i == j) continue;
            int a = eA[i], b = eB[i], c = eA[j], e = eB[j];
            if (adj[(size_t)a * N + e] || adj[(size_t)c * N + b]) continue;
            unlink_e(i);
            unlink_e(j);
            add_e(i, a, e);
            add_e(j, c, b);
            long c2 = eval_bad();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                unlink_e(i);
                unlink_e(j);
                add_e(i, a, b);
                add_e(j, c, e);
            }
        }
    }

    if (cost == 0) {
        printf("%d %d\n", N, M);
        for (int i = 0; i < M; i++) printf("%d %d\n", eA[i], eB[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Classical constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): order 2(q+1)(q^2+1), diameter 4."""
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
    """W(q) for the largest prime power q <= min(d-1, 9) (larger q is too slow to build in Python)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """PG(2, q) incidence graph for the largest prime power q <= d-1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension and saturation (valid by construction).
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
    """Greedy set cover of `full` by at most d candidates; returns the chosen list or None."""
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
    """Add vertices whose neighbourhoods cover all vertices within distance D-1 of deficient vertices."""
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
    """Greedily join deficient opposite-side vertices in random order; returns the new edge list."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover extension and saturation until neither makes progress."""
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
# New idea: add a stub vertex with a partial neighbourhood, then let C repair.
# ----------------------------------------------------------------------------

def _stub_candidate(n, edges, d, D, rng):
    """Add one vertex joined to up to d deficient vertices, chosen to maximise coverage.

    The result may have bad pairs; the C annealer is responsible for repairing them.
    Returns (n+1, edges) or None if no deficient vertex exists.
    """
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    t = rng.randrange(2)
    cands = [s for s in range(n) if color[s] == t and deg[s] < d]
    rng.shuffle(cands)
    covered = 0
    chosen = []
    while len(chosen) < d and cands:
        gains = [(ball[s] & ~covered).bit_count() for s in cands]
        best = max(gains, default=0)
        if best <= 0:
            break
        thr = best - 1 if (best > 1 and rng.random() < 0.3) else best
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        s = cands.pop(rng.choice(opts))
        chosen.append(s)
        covered |= ball[s]
    if not chosen:
        return None
    v = n
    return n + 1, list(edges) + [(s, v) for s in chosen]


def _repair(graph, d, D, seed, budget):
    """Run the C annealer on graph (same vertex count). Returns a valid (n, edges) or None."""
    n, e = graph
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, e), timeout=budget + 5)
        rn, re = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if rn != n or not lib.is_valid(rn, re, d, D):
        return None
    return rn, re


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bases = []
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            bases.append(pg)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)
    for b in bases:
        consider(*b)
    cur = max(bases, key=lambda g: g[0]) if bases else best

    # Phase A: cover extension and saturation (cheap, always valid).
    span = deadline - start
    n2, e2 = _grow(cur[0], cur[1], d, D, start + 0.35 * span, rng)
    consider(n2, e2)
    if lib.is_valid(n2, e2, d, D):
        cur = (n2, e2)

    # Phase B: repeatedly add a stub vertex and let C repair the bad pairs.
    fails = 0
    k = 0
    while fails < 8:
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        cand = _stub_candidate(cur[0], cur[1], d, D, rng)
        if cand is None:
            fails += 1
            continue
        slice_t = min(remaining - 2.0, 8.0)
        res = _repair(cand, d, D, seed * 7919 + k, slice_t)
        k += 1
        if res is None:
            fails += 1
            continue
        rn, re = res
        re = _saturate_edges(rn, re, d, rng)
        if lib.is_valid(rn, re, d, D):
            cur = (rn, re)
            consider(rn, re)
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
