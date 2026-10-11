import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cover-annealing vertex growth with saturation.
#
# A new vertex v on side c is joined to a set S of at most d deficient vertices on
# the other side. Distances between old vertices can only shrink, so the diameter
# stays <= D exactly when every vertex lies within distance D-1 of some s in S.
# Each candidate set S is searched by simulated annealing over swap moves,
# minimising the number of uncovered vertices. Balls of radius D-1 are kept as
# bitsets, so one evaluation costs about d * n/64 word operations. When no cover
# is found, random safe edges between deficient opposite-side vertices are added,
# which also only shrink distances.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define RESTARTS 6
#define ITERS 4000
#define T0 2.0

static int d, D, R;
static int n, CAP, WMAX, Wc;
static int *deg, *color, *adj;
static uint64_t *ball, *bufA, *bufB, *tmp;
static int *cand, *perm, *S, *inS;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) {
    return (int)(rnd64() % (uint64_t)m);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a * d + k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a * d + deg[a]++] = b;
    adj[b * d + deg[b]++] = a;
}

static void compute_balls(void) {
    Wc = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        uint64_t *row = bufA + (size_t)v * WMAX;
        for (int w = 0; w < Wc; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t *cur = bufA, *nxt = bufB;
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * WMAX;
            const uint64_t *src = cur + (size_t)v * WMAX;
            for (int w = 0; w < Wc; w++) dst[w] = src[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *u = cur + (size_t)adj[v * d + k] * WMAX;
                for (int w = 0; w < Wc; w++) dst[w] |= u[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < n; v++)
        for (int w = 0; w < Wc; w++)
            ball[(size_t)v * WMAX + w] = cur[(size_t)v * WMAX + w];
}

static int eval_cover(const int *Ss, int ns) {
    for (int w = 0; w < Wc; w++) tmp[w] = 0;
    for (int i = 0; i < ns; i++) {
        const uint64_t *b = ball + (size_t)Ss[i] * WMAX;
        for (int w = 0; w < Wc; w++) tmp[w] |= b[w];
    }
    int c = 0;
    for (int w = 0; w < Wc; w++) c += popc(tmp[w]);
    return n - c;
}

static int try_add(int c) {
    if (n >= CAP - 1) return 0;
    int P = 0;
    for (int v = 0; v < n; v++)
        if (color[v] == 1 - c && deg[v] < d) cand[P++] = v;
    if (P == 0) return 0;
    int ns = P < d ? P : d;
    for (int rep = 0; rep < RESTARTS; rep++) {
        if (now_sec() > t_end) return 0;
        for (int i = 0; i < P; i++) perm[i] = cand[i];
        for (int i = 0; i < ns; i++) {
            int j = i + rndint(P - i);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
            S[i] = perm[i];
            inS[S[i]] = 1;
        }
        int cost = eval_cover(S, ns);
        if (cost > 0 && P > ns) {
            for (int it = 0; it < ITERS && cost > 0; it++) {
                double T = T0 * (1.0 - (double)it / ITERS) + 1e-3;
                int i = rndint(ns);
                int t = cand[rndint(P)];
                if (inS[t]) continue;
                int old = S[i];
                S[i] = t;
                int nc = eval_cover(S, ns);
                int delta = nc - cost;
                if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                    inS[old] = 0;
                    inS[t] = 1;
                    cost = nc;
                } else {
                    S[i] = old;
                }
            }
        }
        if (cost == 0) {
            int v = n++;
            color[v] = 1 - c;
            deg[v] = 0;
            for (int i = 0; i < ns; i++) add_edge(v, S[i]);
            for (int i = 0; i < ns; i++) inS[S[i]] = 0;
            return 1;
        }
        for (int i = 0; i < ns; i++) inS[S[i]] = 0;
    }
    return 0;
}

static int saturate(void) {
    int *Lv = cand, *Rv = perm;
    int L = 0, Rn = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (color[v] == 0) Lv[L++] = v;
            else Rv[Rn++] = v;
        }
    }
    if (L == 0 || Rn == 0) return 0;
    long long trials = 20LL * (long long)L * (long long)Rn;
    if (trials > 3000000LL) trials = 3000000LL;
    int added = 0;
    for (long long t = 0; t < trials; t++) {
        int a = Lv[rndint(L)];
        int b = Rv[rndint(Rn)];
        if (deg[a] >= d || deg[b] >= d) continue;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
        added++;
    }
    return added;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    double t0 = now_sec();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    t_end = t0 + budget;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0 || d < 1) {
        printf("0 0\n");
        return 0;
    }
    CAP = 2 * n0 + 256;
    WMAX = (CAP + 63) / 64;
    deg = calloc(CAP, sizeof(int));
    color = calloc(CAP, sizeof(int));
    adj = calloc((size_t)CAP * d, sizeof(int));
    ball = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    bufA = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    bufB = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    tmp = calloc(WMAX, sizeof(uint64_t));
    cand = calloc(CAP, sizeof(int));
    perm = calloc(CAP, sizeof(int));
    S = calloc(d, sizeof(int));
    inS = calloc(CAP, sizeof(int));
    if (!deg || !color || !adj || !ball || !bufA || !bufB || !tmp ||
        !cand || !perm || !S || !inS) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (has_edge(u, v)) continue;
        if (deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }

    /* Bipartiteness check; the perm array serves as a BFS queue. */
    for (int v = 0; v < n; v++) color[v] = -1;
    int bad = 0;
    for (int s = 0; s < n && !bad; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int qh = 0, qt = 0;
        perm[qt++] = s;
        while (qh < qt && !bad) {
            int u = perm[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u * d + k];
                if (color[w] == -1) {
                    color[w] = 1 - color[u];
                    perm[qt++] = w;
                } else if (color[w] == color[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    R = D - 1;
    if (R < 0) R = 0;
    compute_balls();

    int fails = 0;
    while (now_sec() < t_end && fails < 3 && n < CAP - 1) {
        int added = 0;
        int c0 = rndint(2);
        for (int k = 0; k < 2 && !added; k++) {
            if (try_add((c0 + k) & 1)) added = 1;
            if (now_sec() >= t_end) break;
        }
        if (added) {
            compute_balls();
            fails = 0;
            continue;
        }
        if (now_sec() >= t_end) break;
        int e = saturate();
        if (e > 0) {
            compute_balls();
            fails = 0;
        } else {
            fails++;
        }
    }

    long long sumdeg = 0;
    for (int v = 0; v < n; v++) sumdeg += deg[v];
    printf("%d %lld\n", n, sumdeg / 2);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v * d + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Constructions and Python-side search helpers (inherited from the parent).
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


def _c_grow(d, D, n, edges, seed, budget):
    """Run the C cover-annealing grower on (n, edges) for about `budget` seconds."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 5.0)
    return lib.parse_graph_text(text)


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

    # Stage 1 (up to 40% of the budget): structured base graphs, grown by Python.
    base_end = start + 0.40 * time_limit

    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, base_end - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            cur = None
            while time.monotonic() < base_end:
                if cur is None or rng.random() < 0.2:
                    src_n, src_e = gq[0], gq[1]
                else:
                    src_n, src_e = _remove_twins(cur[0], cur[1], 0.15, rng)
                pn, pe = _pipeline(src_n, src_e, d, D, base_end, rng)
                consider(pn, pe)
                if cur is None or pn >= cur[0]:
                    cur = (pn, pe)

    # Calibration shortcut: a graph that already meets the Moore bound cannot grow.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Stage 2 (until 80% of the budget): C cover-annealing growth of the best base.
    c_end = start + 0.80 * time_limit
    c_budget = c_end - time.monotonic() - 1.0
    if D >= 3 and c_budget > 0.5:
        try:
            cn, ce = _c_grow(d, D, best[0], best[1], seed + 17, c_budget)
            consider(cn, ce)
        except RuntimeError:
            pass

    # Stage 3 (until 90% of the budget): non-cyclic group-lift and Haar search.
    deadline = start + 0.90 * time_limit
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
