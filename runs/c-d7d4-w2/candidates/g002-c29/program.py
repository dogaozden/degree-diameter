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

/* Bi-Cayley graphs over groups Z_m x|_r Z_k.
   Vertices a_g (g < N) and b_x (x = N + x'), edges a_g ~ b_{g*s} for s in S (|S| = d).
   Left multiplication is an automorphism acting transitively on each side, so the
   diameter is certified by BFS from a_e and from b_e alone.
   Search: simulated annealing over S, for increasing N, with a time slice per N. */

typedef struct { int m, k, r; } GParam;
typedef struct { int N; int *tab; int *inv; } Grp;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int *g_dist = NULL;
static int *g_q = NULL;

static void grp_build(Grp *G, GParam p) {
    int m = p.m, k = p.k, r = p.r;
    int N = m * k;
    G->N = N;
    G->tab = (int *)malloc(sizeof(int) * (size_t)N * (size_t)N);
    G->inv = (int *)malloc(sizeof(int) * (size_t)N);
    int *pw = (int *)malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, d2 = y % k;
            int a = (int)(((long long)a1 + (long long)pw[b1] * c) % m);
            int b = (b1 + d2) % k;
            G->tab[(size_t)x * N + y] = a * k + b;
        }
    }
    for (int x = 0; x < N; x++) {
        G->inv[x] = 0;
        for (int y = 0; y < N; y++) {
            if (G->tab[(size_t)x * N + y] == 0) { G->inv[x] = y; break; }
        }
    }
    free(pw);
}

static int list_groups(int N, GParam *out, int cap) {
    int c = 0;
    for (int k = 1; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m == 1) {
            if (c < cap) { out[c].m = 1; out[c].k = k; out[c].r = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_ll(r, k, m) != 1 % m) continue;
            if (c < cap) { out[c].m = m; out[c].k = k; out[c].r = r; c++; }
        }
    }
    return c;
}

/* Number of (source, vertex) pairs at distance > D, sources a_e and b_e. 0 means valid. */
static int cost_eval(const Grp *G, const int *S, int d, int D) {
    int N = G->N, N2 = 2 * N, cost = 0;
    for (int side = 0; side < 2; side++) {
        int src = (side == 0) ? 0 : N;
        for (int i = 0; i < N2; i++) g_dist[i] = -1;
        g_dist[src] = 0;
        int head = 0, tail = 0;
        g_q[tail++] = src;
        while (head < tail) {
            int u = g_q[head++];
            int du = g_dist[u];
            if (du >= D) continue;
            if (u < N) {
                const int *row = G->tab + (size_t)u * N;
                for (int i = 0; i < d; i++) {
                    int v = N + row[S[i]];
                    if (g_dist[v] < 0) { g_dist[v] = du + 1; g_q[tail++] = v; }
                }
            } else {
                const int *row = G->tab + (size_t)(u - N) * N;
                for (int i = 0; i < d; i++) {
                    int v = row[G->inv[S[i]]];
                    if (g_dist[v] < 0) { g_dist[v] = du + 1; g_q[tail++] = v; }
                }
            }
        }
        cost += N2 - tail;
    }
    return cost;
}

static int pick_new(const int *S, int cnt, int N) {
    for (;;) {
        int c = rndint(N);
        int ok = 1;
        for (int j = 0; j < cnt; j++) if (S[j] == c) { ok = 0; break; }
        if (ok) return c;
    }
}

static int anneal(const Grp *G, int d, int D, int *S, long iters, double deadline) {
    int N = G->N;
    for (int i = 0; i < d; i++) S[i] = pick_new(S, i, N);
    int cur = cost_eval(G, S, d, D);
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 1023) == 0 && elapsed() > deadline) break;
        double frac = (double)it / (double)iters;
        double T = 1.5 * (1.0 - frac) + 0.05;
        int i = rndint(d);
        int c = pick_new(S, d, N);
        int old = S[i];
        S[i] = c;
        int nc = cost_eval(G, S, d, D);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            S[i] = old;
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    int ch;
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time nlo\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);
    while ((ch = getchar()) != EOF) {}
    if (d < 2 || D < 2) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    /* Moore bound for bipartite graphs is 2 * sum_{i<D} (d-1)^i; N = half of it. */
    long long sum = 0, p = 1;
    for (int i = 0; i < D; i++) {
        sum += p;
        p *= (d - 1);
        if (p > 1000000000LL) p = 1000000000LL;
    }
    long long hi = sum;
    if (hi > 1200) hi = 1200;

    int N0 = nlo;
    if (N0 < d + 1) N0 = d + 1;
    if (N0 > hi) { printf("0 0\n"); return 0; }

    g_dist = (int *)malloc(sizeof(int) * (size_t)(2 * hi + 4));
    g_q = (int *)malloc(sizeof(int) * (size_t)(2 * hi + 4));
    int *S = (int *)malloc(sizeof(int) * (size_t)d);
    int *bestS = (int *)malloc(sizeof(int) * (size_t)d);
    static GParam gl[4096];
    GParam bestP = {0, 0, 0};
    int best_N = 0;

    double deadline = budget;
    int N = N0;
    while (N <= hi) {
        double now = elapsed();
        double remain = deadline - now;
        if (remain <= 0.05) break;
        double slice_end = now + 0.6 * remain;
        int ng = list_groups(N, gl, 4096);
        if (ng == 0) break;
        int found = 0;
        while (!found && elapsed() < slice_end) {
            GParam gp = gl[rndint(ng)];
            Grp G;
            grp_build(&G, gp);
            int c = anneal(&G, d, D, S, 250000L, slice_end);
            if (c == 0) {
                found = 1;
                best_N = N;
                bestP = gp;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
            free(G.tab);
            free(G.inv);
        }
        if (!found) break;
        N++;
    }

    if (best_N == 0) { printf("0 0\n"); return 0; }
    Grp G;
    grp_build(&G, bestP);
    int NN = G.N;
    printf("%d %d\n", 2 * NN, NN * d);
    for (int g = 0; g < NN; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, NN + G.tab[g * NN + bestS[i]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python constructions).
# ----------------------------------------------------------------------------

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
# Shared graph helpers.
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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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
            for attempt in range(attempts):
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow), anchored to the best graph.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Bold change: the bi-Cayley search runs in C (simulated annealing over
# generating sets of groups Z_m x|_r Z_k), scanning orders N upward from the
# current best. Python only builds the start and checks the result.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, budget, nlo):
    """Run the C bi-Cayley annealer. Returns (n, edges), or (0, []) if nothing was found."""
    text = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget:.2f}", int(nlo)],
                     stdin_graph=None, timeout=budget + 20.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A (to 0.15 T): structured base, growth, and twin pipelines.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.1 * time_limit, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.15 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase C (0.15 T to 0.7 T): C annealer for bi-Cayley graphs with N above the best so far.
    if D >= 2 and d >= 2:
        c_end = start + 0.7 * time_limit
        budget = c_end - time.monotonic() - 1.5
        if budget > 2.0:
            nlo = best_n // 2 + 1
            try:
                n, e = _c_search(d, D, seed, budget, nlo)
                consider(n, e)
            except Exception:
                pass  # C failure must not break the fallback

    # Phase B (0.7 T to 0.9 T): kill-repair-regrow from the best valid graph.
    if D >= 2 and time.monotonic() < start + 0.9 * time_limit:
        _lns(best_n, best_e, d, D, start + 0.9 * time_limit, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
