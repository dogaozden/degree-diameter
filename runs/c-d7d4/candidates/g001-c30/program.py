import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated-annealing vertex growth.
#
# Input: a valid bipartite graph (max degree d, diameter <= D) on stdin.
# Loop: add one vertex on a chosen side, join it greedily to opposite-side
# vertices that cover the most vertices within distance D-1, then repair with
# annealing over degree-preserving 2-switches and deficient-vertex edge moves
# until the diameter is <= D again. On success, fill spare degree and snapshot.
# On repeated failure, restore the last valid graph. Prints the largest valid
# graph found, or "0 0" if the input is not usable.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define WN 16
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2)
#define SA_IT 20000
#define MAX_FAILS 60

typedef uint64_t Row[WN];

static int N, NW, Dg, DIAM;
static int nadj[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char am[MAXN][MAXN];
static int col[MAXN];
static Row X1[MAXN], X2[MAXN];

static int bkN;
static int bkNadj[MAXN];
static int bkAdj[MAXN][MAXDEG];
static unsigned char bkAm[MAXN][MAXN];

static int snapN, snapM;
static int SE[MAXE + 8][2];

static int defl[MAXN];
static clock_t dl;
static uint64_t rs;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int timeup(void) { return clock() >= dl; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void set_N(int x) {
    N = x;
    NW = (N + 63) / 64;
}

/* Bitset balls of radius R over the current graph (vertices 0..N-1). */
static Row *balls(int R) {
    Row *cur = X1, *nx = X2;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < R; s++) {
        for (int v = 0; v < N; v++) {
            memcpy(nx[v], cur[v], sizeof(Row));
            for (int k = 0; k < nadj[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int w = 0; w < NW; w++) nx[v][w] |= src[w];
            }
        }
        Row *t = cur;
        cur = nx;
        nx = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long long badpairs(void) {
    Row *b = balls(DIAM);
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < NW; w++) pc += pc64(b[v][w]);
        tot += N - pc;
    }
    return tot / 2;
}

static void rm_half(int u, int v) {
    for (int k = 0; k < nadj[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--nadj[u]];
            return;
        }
    }
}

static void add_edge(int u, int v) {
    am[u][v] = am[v][u] = 1;
    adj[u][nadj[u]++] = v;
    adj[v][nadj[v]++] = u;
}

static void del_edge(int u, int v) {
    am[u][v] = am[v][u] = 0;
    rm_half(u, v);
    rm_half(v, u);
}

static void snapshot(void) {
    snapN = N;
    snapM = 0;
    for (int u = 0; u < N; u++)
        for (int k = 0; k < nadj[u]; k++) {
            int v = adj[u][k];
            if (v > u && snapM < MAXE) {
                SE[snapM][0] = u;
                SE[snapM][1] = v;
                snapM++;
            }
        }
}

static void fill_graph(void) {
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++)
            if (col[u] != col[v] && nadj[u] < Dg && nadj[v] < Dg && !am[u][v])
                add_edge(u, v);
}

static void save_state(void) {
    bkN = N;
    memcpy(bkNadj, nadj, sizeof nadj);
    memcpy(bkAdj, adj, sizeof adj);
    memcpy(bkAm, am, sizeof am);
}

static void restore_state(void) {
    set_N(bkN);
    memcpy(nadj, bkNadj, sizeof nadj);
    memcpy(adj, bkAdj, sizeof adj);
    memcpy(am, bkAm, sizeof am);
}

/* Add a new vertex of colour c, joined greedily to opposite-colour vertices
   that maximise newly covered vertices within distance DIAM-1. */
static void attach_vertex(int c) {
    int old = N;
    int nwo = (old + 63) / 64;
    Row *R1 = balls(DIAM - 1);
    uint64_t covered[WN];
    memset(covered, 0, sizeof covered);
    set_N(old + 1);
    int v = old;
    nadj[v] = 0;
    col[v] = c;
    int cnt = 0;
    while (cnt < Dg) {
        int best = -1, bestg = 0, ties = 0;
        for (int u = 0; u < old; u++) {
            if (col[u] == c || nadj[u] >= Dg || am[v][u]) continue;
            int g = 0;
            for (int w = 0; w < nwo; w++) g += pc64(R1[u][w] & ~covered[w]);
            if (g > bestg) {
                bestg = g;
                best = u;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndint(ties) == 0) best = u;
            }
        }
        if (best < 0) break;
        add_edge(v, best);
        for (int w = 0; w < nwo; w++) covered[w] |= R1[best][w];
        cnt++;
    }
}

/* Simulated annealing on bad-pair count. Moves preserve bipartiteness and
   degree bounds. Returns the final bad-pair count (0 means valid). */
static long long sa_repair(long long maxit, double T0) {
    long long cur = badpairs();
    for (long long it = 0; it < maxit && cur > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        double T = T0 * (1.0 - (double)it / (double)maxit) + 0.05;
        int nd = 0;
        for (int v = 0; v < N; v++)
            if (nadj[v] < Dg) defl[nd++] = v;

        if (nd > 0 && rnd01() < 0.5) {
            /* Add an edge from a deficient vertex; if the partner is full,
               drop one of its edges. */
            int p = defl[rndint(nd)];
            int q = -1;
            for (int t = 0; t < 8 && q < 0; t++) {
                int x = rndint(N);
                if (col[x] != col[p] && !am[p][x]) q = x;
            }
            if (q < 0) continue;
            int r = -1;
            if (nadj[q] >= Dg) r = adj[q][rndint(nadj[q])];
            if (r >= 0) del_edge(q, r);
            add_edge(p, q);
            long long nb = badpairs();
            long long delta = nb - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nb;
            } else {
                del_edge(p, q);
                if (r >= 0) add_edge(q, r);
            }
        } else {
            /* Degree-preserving 2-switch on two random edges. */
            int a = rndint(N), c2 = rndint(N);
            if (nadj[a] == 0 || nadj[c2] == 0) continue;
            int b = adj[a][rndint(nadj[a])];
            int e = adj[c2][rndint(nadj[c2])];
            int p = (col[a] == 0) ? a : b;
            int q = (col[a] == 0) ? b : a;
            int p2 = (col[c2] == 0) ? c2 : e;
            int q2 = (col[c2] == 0) ? e : c2;
            if (p == p2 || q == q2 || am[p][q2] || am[p2][q]) continue;
            del_edge(p, q);
            del_edge(p2, q2);
            add_edge(p, q2);
            add_edge(p2, q);
            long long nb = badpairs();
            long long delta = nb - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nb;
            } else {
                del_edge(p, q2);
                del_edge(p2, q);
                add_edge(p, q);
                add_edge(p2, q2);
            }
        }
    }
    return cur;
}

static void grow(void) {
    int fails = 0;
    while (!timeup() && fails < MAX_FAILS && N < MAXN - 2) {
        save_state();
        attach_vertex(rndint(2));
        long long r = sa_repair(SA_IT, 0.8);
        if (r == 0) {
            fill_graph();
            snapshot();
            fails = 0;
        } else {
            restore_state();
            fails++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = (uint64_t)seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    dl = clock() + (clock_t)(tl * CLOCKS_PER_SEC);
    Dg = d;
    DIAM = D;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 64 || m < 0 || m > MAXE ||
        d < 1 || d > MAXDEG - 2 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    set_N(n);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || am[u][v] ||
            nadj[u] >= Dg || nadj[v] >= Dg) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    static int qu[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0;
        qu[t++] = s;
        while (h < t) {
            int u = qu[h++];
            for (int k = 0; k < nadj[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    qu[t++] = w;
                }
            }
        }
    }
    for (int u = 0; u < N; u++)
        for (int k = 0; k < nadj[u]; k++)
            if (col[adj[u][k]] == col[u]) {
                printf("0 0\n");
                return 0;
            }

    if (badpairs() != 0) {
        printf("0 0\n");
        return 0;
    }

    snapshot();
    grow();
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", SE[i][0], SE[i][1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions.
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
    # Python constructions get the first ~30% of the budget; the C annealing
    # growth gets the rest, up to ~90% of time_limit in total.
    end = start + 0.9 * time_limit
    py_deadline = start + 0.3 * time_limit
    ext_deadline = start + 0.15 * time_limit
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < py_deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, py_deadline)
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
            S = _search_haar(d, D, haar_m, rng, py_deadline, 120)
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
            res = _search_lift(d, D, k, m, rng, 250, py_deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        best_n = best[0]

    # Already at the Moore bound: nothing to search for.
    if best_n >= lib.moore_bound(d, D):
        return best

    # C phase: anneal-grow the best valid graph found so far.
    budget = end - time.monotonic() - 1.5
    if budget >= 1.0 and D >= 3 and 2 <= d <= 40:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
