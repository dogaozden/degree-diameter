import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealing with zero-cost plateau walks.
#
# State: a valid bipartite graph (bad pairs = 0). Each round:
#   1. Walk the plateau with degree-preserving bipartite double-edge switches,
#      accepting only moves that keep bad pairs at 0 (T = 0).
#   2. Add one vertex (cover-style neighbours, stealing an edge if a neighbour
#      is full), fill spare degree, then anneal with the same switches at low
#      temperature on the bad-pair count.
#   3. Keep the result if the bad-pair count reaches 0, else restore the snapshot.
# The bad-pair count is computed exactly with bitset ball expansion, so every
# accepted state is valid. The best graph seen is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXCAP 2048
#define ANNEAL 2500
#define TANN 0.5
#define PLATEAU 200

static int d, D, cap, W, n, bn;
static int *deg, *col, *adj, *bdeg, *bcol, *badj, *chosen, *L0, *L1;
static u64 *bA, *bB;
static int bestN, bestM;
static int *bestE;
static unsigned long long rs;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd() % (unsigned long long)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long moore_bound(int dd, int DD) {
    long long s = 0, p = 1;
    int i;
    if (DD == 0 || dd == 0) return 1;
    if (dd == 1) return DD >= 1 ? 2 : 1;
    if (dd == 2) return 2LL * DD;
    for (i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 1000000000LL) break;
    }
    return 2 * s;
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static long long cost(void) {
    int r, v, k, w;
    u64 *src = bA, *dst = bB, *tmp;
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) src[(size_t)v * W + w] = 0;
        src[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (r = 0; r < D; r++) {
        for (v = 0; v < n; v++) {
            u64 *o = dst + (size_t)v * W;
            u64 *s = src + (size_t)v * W;
            memcpy(o, s, sizeof(u64) * (size_t)W);
            for (k = 0; k < deg[v]; k++) {
                u64 *t = src + (size_t)adj[v * d + k] * W;
                for (w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = src; src = dst; dst = tmp;
    }
    {
        long long tot = 0;
        for (v = 0; v < n; v++)
            for (w = 0; w < W; w++)
                tot += popc(src[(size_t)v * W + w]);
        return ((long long)n * n - tot) / 2;
    }
}

static int has_edge(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++) if (adj[a * d + k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a * d + deg[a]++] = b;
    adj[b * d + deg[b]++] = a;
}

static void del_at(int a, int idx) {
    deg[a]--;
    adj[a * d + idx] = adj[a * d + deg[a]];
}

static void remove_edge(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++) if (adj[a * d + k] == b) { del_at(a, k); break; }
    for (k = 0; k < deg[b]; k++) if (adj[b * d + k] == a) { del_at(b, k); break; }
}

/* One degree-preserving switch a-b, x-e -> a-e, x-b (a, x on side 0).
   Accepted if the cost does not rise, or with Boltzmann probability when T > 0. */
static long long switch_step(long long c, double T) {
    int a, b, x, e, t;
    for (t = 0; ; t++) {
        a = rndint(n);
        if (col[a] == 0 && deg[a] > 0) break;
        if (t > 4000) return c;
    }
    b = adj[a * d + rndint(deg[a])];
    for (t = 0; ; t++) {
        x = rndint(n);
        if (x != a && col[x] == 0 && deg[x] > 0) break;
        if (t > 4000) return c;
    }
    e = adj[x * d + rndint(deg[x])];
    if (has_edge(a, e) || has_edge(x, b)) return c;
    remove_edge(a, b);
    remove_edge(x, e);
    add_edge(a, e);
    add_edge(x, b);
    {
        long long nc = cost();
        if (nc <= c || (T > 0 && rnd01() < exp(-(double)(nc - c) / T))) return nc;
    }
    remove_edge(a, e);
    remove_edge(x, b);
    add_edge(a, b);
    add_edge(x, e);
    return c;
}

/* Add one vertex on a random side, joined to d old vertices of the other side.
   A full neighbour gives up one random edge (its partner gets spare degree). */
static void add_random_vertex(void) {
    int s = rndint(2), w = n, k, t, x, f, nc = 0, tries, dup, j;
    n++;
    col[w] = 1 - s;
    deg[w] = 0;
    for (k = 0; k < d; k++) {
        f = -1;
        for (tries = 0; tries < 300; tries++) {
            x = rndint(w);
            if (col[x] != s) continue;
            dup = 0;
            for (j = 0; j < nc; j++) if (chosen[j] == x) { dup = 1; break; }
            if (dup) continue;
            if (deg[x] < d || rndint(3) == 0) { f = x; break; }
        }
        if (f < 0) break;
        if (deg[f] >= d) {
            t = adj[f * d + rndint(deg[f])];
            remove_edge(f, t);
        }
        add_edge(f, w);
        chosen[nc++] = f;
    }
}

/* Join deficient opposite-side vertices (only shortens distances). */
static void fill(void) {
    int n0 = 0, n1 = 0, v, i, tries, a, b;
    for (v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    tries = 4 * (n0 + n1) + 10;
    for (i = 0; i < tries && n0 > 0 && n1 > 0; i++) {
        a = L0[rndint(n0)];
        b = L1[rndint(n1)];
        if (deg[a] < d && deg[b] < d && !has_edge(a, b)) add_edge(a, b);
    }
}

static void save_state(void) {
    bn = n;
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(bcol, col, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(int) * (size_t)n * d);
}

static void restore_state(void) {
    n = bn;
    memcpy(deg, bdeg, sizeof(int) * (size_t)n);
    memcpy(col, bcol, sizeof(int) * (size_t)n);
    memcpy(adj, badj, sizeof(int) * (size_t)n * d);
}

static void record_best(void) {
    int v, k, m = 0;
    for (v = 0; v < n; v++) {
        for (k = 0; k < deg[v]; k++) {
            int u = adj[v * d + k];
            if (v < u) {
                bestE[2 * m] = v;
                bestE[2 * m + 1] = u;
                m++;
            }
        }
    }
    bestN = n;
    bestM = m;
}

int main(int argc, char **argv) {
    int nn = 0, mm = 0, m_read = 0, i, ok = 1;
    long long mo;
    double budget, endc;
    long long cur;
    int *eu;

    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);

    if (scanf("%d %d", &nn, &mm) != 2) { nn = 0; mm = 0; }
    if (mm < 0) mm = 0;
    eu = malloc(sizeof(int) * 2 * (size_t)(mm + 1));
    for (i = 0; i < mm; i++) {
        if (scanf("%d %d", &eu[2 * i], &eu[2 * i + 1]) != 2) break;
        m_read++;
    }
    mm = m_read;

    if (d < 1) { printf("0 0\n"); return 0; }
    mo = moore_bound(d, D);
    cap = mo > MAXCAP ? MAXCAP : (int)mo;
    if (cap < 2) cap = 2;
    W = (cap + 63) / 64;

    deg = calloc((size_t)cap, sizeof(int));
    col = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * d, sizeof(int));
    bdeg = calloc((size_t)cap, sizeof(int));
    bcol = calloc((size_t)cap, sizeof(int));
    badj = calloc((size_t)cap * d, sizeof(int));
    chosen = calloc((size_t)d + 2, sizeof(int));
    L0 = calloc((size_t)cap, sizeof(int));
    L1 = calloc((size_t)cap, sizeof(int));
    bA = calloc((size_t)cap * W, sizeof(u64));
    bB = calloc((size_t)cap * W, sizeof(u64));
    bestE = calloc((size_t)2 * cap * d + 4, sizeof(int));

    /* Load the start graph, checking simple-graph and degree rules. */
    n = 0;
    if (nn >= 1 && nn <= cap && D >= 2) {
        n = nn;
        for (i = 0; i < mm && ok; i++) {
            int a = eu[2 * i], b = eu[2 * i + 1];
            if (a < 0 || a >= n || b < 0 || b >= n || a == b ||
                deg[a] >= d || deg[b] >= d || has_edge(a, b)) ok = 0;
            else add_edge(a, b);
        }
    } else {
        ok = 0;
    }

    /* Bipartition by BFS; a conflict means the start is not bipartite. */
    if (ok) {
        int v, h, t, u, k;
        for (v = 0; v < n; v++) col[v] = -1;
        for (v = 0; v < n && ok; v++) {
            if (col[v] >= 0) continue;
            col[v] = 0;
            L0[0] = v;
            h = 0; t = 1;
            while (h < t && ok) {
                u = L0[h++];
                for (k = 0; k < deg[u]; k++) {
                    int w = adj[u * d + k];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        L0[t++] = w;
                    } else if (col[w] == col[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (ok && cost() != 0) ok = 0;

    /* Fallback: K_{d,d} (diameter 2, valid for D >= 2). */
    if (!ok) {
        int a, b;
        if (D < 2 || 2 * d > cap) { printf("0 0\n"); return 0; }
        memset(deg, 0, sizeof(int) * (size_t)cap);
        n = 2 * d;
        for (a = 0; a < d; a++) { col[a] = 0; col[d + a] = 1; }
        for (a = 0; a < d; a++)
            for (b = 0; b < d; b++)
                add_edge(a, d + b);
    }

    record_best();
    cur = 0;
    endc = (double)clock() + budget * CLOCKS_PER_SEC;

    while ((double)clock() < endc) {
        int i2, steps;
        for (i2 = 0; i2 < PLATEAU && (double)clock() < endc; i2++)
            cur = switch_step(cur, 0.0);
        if (n >= cap) continue;

        save_state();
        add_random_vertex();
        fill();
        cur = cost();
        for (steps = 0; cur > 0 && steps < ANNEAL && (double)clock() < endc; steps++)
            cur = switch_step(cur, TANN);
        if (cur == 0) {
            if (n > bestN) record_best();
        } else {
            restore_state();
            cur = 0;
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (i = 0; i < bestM; i++)
        printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    return 0;
}
'''


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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list.

    Adding cross-side edges keeps the graph bipartite and degrees <= d, and can only
    shorten distances, so a valid graph stays valid.
    """
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


# ----------------------------------------------------------------------------
# Twin duplication.
#
# A vertex v' with N(v') = N(v), v' not adjacent to v, is a "twin" of v. In any
# graph, non-adjacent twins are at the same distance from every other vertex,
# and at distance 2 from each other. So duplicating a vertex never breaks the
# diameter bound (for D >= 2), keeps the graph bipartite (v' is on v's side),
# and needs only spare degree on the neighbours of v.
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
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


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
        k = rng.choice((1, 1, 2, 2, 3, 4))
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
        if _cost(adj, D) > 40:
            continue
        if not _anneal(adj, color, d, D, rng, 60, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Redundant-edge pruning, then regrow.
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random redundant edges (keeping diameter <= D). Returns the pruned edge list."""
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    """Repeatedly prune redundant edges, regrow with cover vertices, keep the best."""
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Cross-matching doubling with annealed repair.
# ----------------------------------------------------------------------------

def _double_cross(n, edges, d, D, rng, deadline):
    """Try to build a valid 2n-vertex graph from two cross-matched copies of a base graph.

    Returns (N, edges) when the repaired graph has zero bad pairs, else None.
    """
    N = 2 * n
    if N > lib.moore_bound(d, D):
        return None
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    B = [set() for _ in range(N)]
    for u in range(n):
        for v in adj[u]:
            B[u].add(v)
            B[u + n].add(v + n)
    spare = [d - len(adj[v]) for v in range(n)]
    s0 = [v for v in range(n) if color[v] == 0 for _ in range(spare[v])]
    s1 = [v for v in range(n) if color[v] == 1 for _ in range(spare[v])]
    rng.shuffle(s0)
    rng.shuffle(s1)
    t0 = list(s0)
    t1 = list(s1)
    rng.shuffle(t0)
    rng.shuffle(t1)
    for x, w in zip(s0, s1):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    for x, w in zip(t1, t0):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    color2 = color + [1 - c for c in color]
    _fill(B, color2, d, rng)
    while time.monotonic() < deadline:
        if _anneal(B, color2, d, D, rng, 3000, deadline):
            return N, [(u, v) for u in range(N) for v in B[u] if u < v]
        return None
    return None


def _try_doubling(n, edges, d, D, deadline, rng, consider):
    """Repeatedly attempt cross-matching doubling of the base until the deadline."""
    while time.monotonic() < deadline:
        res = _double_cross(n, edges, d, D, rng, deadline)
        if res is not None:
            N, e = res
            consider(N, e)
            return True
    return False


# ----------------------------------------------------------------------------
# Vertex splitting with neighbour partition, then annealed repair.
# ----------------------------------------------------------------------------

def _split_repair(n, edges, d, D, deadline, rng, consider):
    """Repeatedly split a random vertex of the current valid graph and repair it."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        cur_n = len(adj)
        cands = [v for v in range(cur_n) if len(adj[v]) >= 2]
        if not cands:
            break
        v = rng.choice(cands)
        nb = list(adj[v])
        rng.shuffle(nb)
        k = rng.randint(1, len(nb) - 1)
        S1, S2 = nb[:k], nb[k:]
        w = cur_n
        adj.append(set(S2))
        color.append(color[v])
        adj[v] = set(S1)
        for u in S2:
            adj[u].discard(v)
            adj[u].add(w)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 400, deadline):
            m = len(adj)
            e = [(a, b) for a in range(m) for b in adj[a] if a < b]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _prune_then_split(n, edges, d, D, deadline, rng, consider):
    """Prune redundant edges first (frees degree), then run split-repair from the result."""
    if time.monotonic() >= deadline:
        return
    pe = _prune_redundant(n, edges, D, rng, deadline, 160)
    n2, e2 = _grow(n, pe, d, D, deadline, rng)
    consider(n2, e2)
    _split_repair(n2, e2, d, D, deadline, rng, consider)


# ----------------------------------------------------------------------------
# Repair with an added vertex.
# ----------------------------------------------------------------------------

def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 400, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Build: Python constructions and search first (about 30% of the budget), then the
# C engine (plateau walk plus vertex insertion with annealed repair) takes the
# start graph and searches for a larger valid one until the budget is spent.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total_end = start + 0.85 * time_limit
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

    # Python share of the budget; every stage fraction below is of T.
    T = 0.30 * time_limit
    deadline = start + 0.92 * T

    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * T, rng)
            consider(n1, e1)

    if D >= 2 and 2 * base_n <= lib.moore_bound(d, D):
        _try_doubling(base_n, base_e, d, D, start + 0.20 * T, rng, consider)

    if D >= 2:
        trial_end = start + 0.10 * T
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        _lns(best_n, best_e, d, D, start + 0.60 * T, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _prune_regrow(best_n, best_e, d, D, start + 0.72 * T, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _prune_then_split(best_n, best_e, d, D, start + 0.84 * T, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    # C stage: plateau walk and vertex insertion from the best valid graph so far.
    if d >= 3 and D >= 2:
        rem = total_end - time.monotonic() - 2.0
        if rem > 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(rem - 1.0, 2)],
                                stdin_graph=(best_n, best_e), timeout=rem + 2.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
