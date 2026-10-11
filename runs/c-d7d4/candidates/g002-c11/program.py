import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1200
#define WMAX 20
#define DMAX 32
#define STAG 40000L

static int d, D, n;
static int nb[NMAX][DMAX];
static int deg[NMAX];
static int side[NMAX];
static uint64_t ball[NMAX][WMAX];
static uint64_t tmpb[NMAX][WMAX];
static int bestN = -1;
static int bestnb[NMAX][DMAX];
static int bestdeg[NMAX];
static int bestside[NMAX];
static long B = 0;
static long moves_since = 0;
static uint64_t rs = 1;
static double budget_s = 1.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ball[v] = bitset of vertices within distance r of v. */
static void compute_ball(int r) {
    int w = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) ball[v][k] = 0;
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < w; k++) tmpb[v][k] = ball[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int k = 0; k < w; k++) tmpb[v][k] |= ball[u][k];
            }
        }
        for (int v = 0; v < n; v++)
            for (int k = 0; k < w; k++) ball[v][k] = tmpb[v][k];
    }
}

/* Number of unordered pairs at distance > D. Zero means a valid graph. */
static long eval_bad(void) {
    compute_ball(D);
    int w = (n + 63) >> 6;
    long cnt = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(ball[v][k]);
        cnt += n - c;
    }
    return cnt / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (nb[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void rem_nb(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) {
            nb[a][i] = nb[a][--deg[a]];
            return;
        }
    }
}

static void rem_edge(int a, int b) {
    rem_nb(a, b);
    rem_nb(b, a);
}

static int pick_side0(void) {
    for (int t = 0; t < 400; t++) {
        int v = rndi(n);
        if (side[v] == 0 && deg[v] > 0) return v;
    }
    return -1;
}

static int count_side(int s) {
    int c = 0;
    for (int v = 0; v < n; v++)
        if (side[v] == s) c++;
    return c;
}

static void save_best(void) {
    bestN = n;
    for (int v = 0; v < n; v++) {
        bestdeg[v] = deg[v];
        bestside[v] = side[v];
        memcpy(bestnb[v], nb[v], sizeof(int) * DMAX);
    }
}

static void restore_best(void) {
    n = bestN;
    for (int v = 0; v < n; v++) {
        deg[v] = bestdeg[v];
        side[v] = bestside[v];
        memcpy(nb[v], bestnb[v], sizeof(int) * DMAX);
    }
}

/* Degree-preserving cross 2-switch: (a,b),(c,e) -> (a,e),(c,b), a,c on side 0. */
static void move_switch(double T) {
    int a = pick_side0();
    int c = pick_side0();
    if (a < 0 || c < 0 || a == c) return;
    int b = nb[a][rndi(deg[a])];
    int e = nb[c][rndi(deg[c])];
    if (b == e) return;
    if (has_edge(a, e) || has_edge(c, b)) return;
    rem_edge(a, b);
    rem_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    long Bn = eval_bad();
    if (Bn <= B || rndu() < exp(-(double)(Bn - B) / T)) {
        B = Bn;
    } else {
        rem_edge(a, e);
        rem_edge(c, b);
        add_edge(a, b);
        add_edge(c, e);
    }
}

/* Delete a random edge (accepted by Metropolis). */
static void move_del(double T) {
    int a = pick_side0();
    if (a < 0) return;
    int b = nb[a][rndi(deg[a])];
    rem_edge(a, b);
    long Bn = eval_bad();
    if (Bn <= B || rndu() < exp(-(double)(Bn - B) / T)) {
        B = Bn;
    } else {
        add_edge(a, b);
    }
}

/* Move one spare slot from a deficient vertex w to a neighbour y of a random x. */
static void move_shift(double T) {
    static int wl[NMAX];
    int mw = 0;
    for (int v = 0; v < n; v++)
        if (deg[v] < d) wl[mw++] = v;
    if (mw == 0) return;
    int w = wl[rndi(mw)];
    int x = -1;
    for (int t = 0; t < 60; t++) {
        int c = rndi(n);
        if (side[c] != side[w] && deg[c] > 0 && !has_edge(w, c)) {
            x = c;
            break;
        }
    }
    if (x < 0) return;
    int y = nb[x][rndi(deg[x])];
    rem_edge(x, y);
    add_edge(w, x);
    long Bn = eval_bad();
    if (Bn <= B || rndu() < exp(-(double)(Bn - B) / T)) {
        B = Bn;
    } else {
        rem_edge(w, x);
        add_edge(x, y);
    }
}

/* Join two deficient opposite-side vertices if possible (never raises B), else shift. */
static void move_addshift(double T) {
    static int L0[NMAX], L1[NMAX];
    int m0 = 0, m1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) L0[m0++] = v;
            else L1[m1++] = v;
        }
    }
    if (m0 > 0 && m1 > 0) {
        int a = L0[rndi(m0)];
        int b = L1[rndi(m1)];
        if (!has_edge(a, b)) {
            add_edge(a, b);
            B = eval_bad();
            return;
        }
    }
    if (m0 + m1 > 0) move_shift(T);
}

static void perturb(int k) {
    for (int i = 0; i < k; i++) move_switch(1e9);
}

/*
 * Insert a new vertex whose neighbourhood is a greedy cover of radius D-1.
 * Neighbours that are already full give up one random edge (which may break
 * some pairs; the annealer repairs them).
 */
static void grow_cover(void) {
    if (n + 1 >= NMAX) return;
    int c = rndi(2);
    if (count_side(1 - c) < d) {
        c = 1 - c;
        if (count_side(1 - c) < d) return;
    }
    compute_ball(D - 1);
    int w = (n + 63) >> 6;
    uint64_t cov[WMAX];
    for (int k = 0; k < w; k++) cov[k] = 0;
    static char used[NMAX];
    memset(used, 0, sizeof(char) * (size_t)n);
    int chosen[DMAX];
    int nch = 0;
    for (int t = 0; t < d; t++) {
        int bestu = -1, bestg = -1;
        int start = rndi(n);
        for (int j = 0; j < n; j++) {
            int u = (start + j) % n;
            if (side[u] != 1 - c || used[u]) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += popc(ball[u][k] & ~cov[k]);
            if (g > bestg) {
                bestg = g;
                bestu = u;
            }
        }
        if (bestu < 0) break;
        used[bestu] = 1;
        chosen[nch++] = bestu;
        for (int k = 0; k < w; k++) cov[k] |= ball[bestu][k];
    }
    while (nch < d) {
        int u = rndi(n);
        if (side[u] != 1 - c || used[u]) continue;
        used[u] = 1;
        chosen[nch++] = u;
    }
    int v = n++;
    side[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int u = chosen[i];
        if (deg[u] >= d) {
            int wv = nb[u][rndi(deg[u])];
            rem_edge(u, wv);
        }
        add_edge(u, v);
    }
}

static void on_valid(void) {
    if (n > bestN) {
        save_best();
        moves_since = 0;
    }
    if (n + 1 < NMAX) {
        grow_cover();
        B = eval_bad();
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    if (d < 2 || d > DMAX || D < 2) {
        printf("0 0\n");
        return 0;
    }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > NMAX - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) {
            ok = 0;
            break;
        }
        if (deg[a] >= d || deg[b] >= d || has_edge(a, b)) {
            ok = 0;
            break;
        }
        add_edge(a, b);
    }
    if (ok) {
        int *q = malloc(sizeof(int) * (size_t)n);
        for (int v = 0; v < n; v++) side[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt) {
                int x = q[qh++];
                for (int i = 0; i < deg[x]; i++) {
                    int y = nb[x][i];
                    if (side[y] < 0) {
                        side[y] = 1 - side[x];
                        q[qt++] = y;
                    } else if (side[y] == side[x]) {
                        ok = 0;
                        break;
                    }
                }
                if (!ok) break;
            }
        }
        free(q);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    B = eval_bad();
    if (B == 0) on_valid();

    long it = 0;
    while (elapsed() < budget_s) {
        for (int k = 0; k < 200; k++) {
            double f = (double)(it % 5000) / 5000.0;
            double T = 0.7 * (1.0 - f) + 0.03;
            int r = rndi(100);
            if (r < 80) move_switch(T);
            else if (r < 92) move_addshift(T);
            else move_del(T);
            it++;
            moves_since++;
            if (B == 0) on_valid();
        }
        if (bestN >= 0 && moves_since > STAG) {
            restore_best();
            B = eval_bad();
            perturb(30);
            moves_since = 0;
            if (B == 0) on_valid();
        }
    }

    if (bestN < 0) {
        printf("0 0\n");
        return 0;
    }
    long m = 0;
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestdeg[v]; i++)
            if (bestnb[v][i] > v) m++;
    printf("%d %ld\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestdeg[v]; i++)
            if (bestnb[v][i] > v) printf("%d %d\n", v, bestnb[v][i]);
    free(eu);
    free(ev);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane and generalized-quadrangle starts.
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
# Shared helpers.
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
# Haar and cyclic-lift families, kept as a secondary family.
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = float(time_limit)
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

    ext_deadline = t0 + 0.10 * T
    main_deadline = t0 + 0.16 * T

    # D >= 3: projective plane, grown by cover extension then saturation.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown likewise.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, ext_deadline, rng)
            consider(n2, e2)

    # Short Python family search.
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < main_deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, main_deadline)
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
            S = _search_haar(d, D, haar_m, rng, main_deadline, 120)
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
            res = _search_lift(d, D, k, m, rng, 250, main_deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    # Main engine: C simulated annealing with cover-based vertex growth,
    # started from the best valid graph. Skipped when the Moore bound is met.
    if D >= 2 and 2 <= d <= 32 and best_n < lib.moore_bound(d, D):
        remaining = t0 + T - time.monotonic()
        budget = max(0.5, 0.80 * remaining - 0.5)
        if budget > 0.5:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                                stdin_graph=best, timeout=max(1.0, 0.92 * remaining))
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
