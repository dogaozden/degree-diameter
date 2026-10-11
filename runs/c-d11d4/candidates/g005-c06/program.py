import itertools
import math
import random
import time

import lib


# C repair engine. It reads a valid bipartite graph (max degree d, diameter <= D) and
# repeatedly adds one vertex. The new vertex is attached greedily to the opposite side,
# choosing neighbours that maximise newly covered vertices within distance D-1. Any
# remaining bad pairs are removed by simulated annealing over degree-preserving 2-switches
# and endpoint rewires, with bad pairs as the cost. Each successful repair is saved, and
# the search keeps growing from the best saved graph. Output is always a valid graph.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 3072
#define WMAX 48
#define MAXD 32
#define MAXR 8

typedef uint64_t u64;

static int n, d, D;
static int col[NMAX];
static int deg[NMAX];
static int nbr[NMAX][MAXD];
static unsigned char A[NMAX][NMAX];
static u64 ball[MAXR][NMAX][WMAX];
static u64 rs = 88172645463325252ULL;
static int logA[NMAX * MAXD], logB[NMAX * MAXD];
static int nlog = 0;
static int bestN = 0, bestM = 0;
static int bestCol[NMAX];
static int bestEa[NMAX * MAXD], bestEb[NMAX * MAXD];
static int ia[NMAX * MAXD], ib[NMAX * MAXD];
static clock_t t_start;
static double budget_s;

typedef struct { int type, a, b, c, e; } Move;

static u64 rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (u64)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int timeup(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC >= budget_s;
}

static void add_e(int a, int b) {
    A[a][b] = 1; A[b][a] = 1;
    nbr[a][deg[a]++] = b;
    nbr[b][deg[b]++] = a;
}

static void rm_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nbr[a][i] == b) { nbr[a][i] = nbr[a][--deg[a]]; return; }
    }
}

static void del_e(int a, int b) {
    A[a][b] = 0; A[b][a] = 0;
    rm_from(a, b); rm_from(b, a);
}

static void compute_balls(void) {
    int w = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) ball[0][v][k] = 0;
        ball[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 1; r <= D; r++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = ball[r][v];
            const u64 *src = ball[r - 1][v];
            for (int k = 0; k < w; k++) dst[k] = src[k];
            for (int i = 0; i < deg[v]; i++) {
                const u64 *s = ball[r - 1][nbr[v][i]];
                for (int k = 0; k < w; k++) dst[k] |= s[k];
            }
        }
    }
}

static long cost(void) {
    compute_balls();
    int w = (n + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += pc(ball[D][v][k]);
        bad += n - c;
    }
    return bad / 2;
}

/* Greedy cover: choose up to d opposite-side vertices with spare degree whose
   radius-(D-1) balls cover as much of the old graph as possible. */
static int greedy_attach(int c, int *out) {
    static u64 cov[WMAX];
    static unsigned char used[NMAX];
    int w = (n + 63) >> 6;
    for (int k = 0; k < w; k++) cov[k] = 0;
    memset(used, 0, (size_t)n);
    int chosen = 0;
    while (chosen < d) {
        int best = -1, bg = 0, ties = 0;
        for (int u = 0; u < n; u++) {
            if (col[u] == c || deg[u] >= d || used[u]) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += pc(ball[D - 1][u][k] & ~cov[k]);
            if (g > bg) { bg = g; best = u; ties = 1; }
            else if (g == bg && g > 0) { ties++; if (rndi(ties) == 0) best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        out[chosen++] = best;
        for (int k = 0; k < w; k++) cov[k] |= ball[D - 1][best][k];
    }
    return chosen;
}

static void saturate_all(void) {
    static int L0[NMAX], L1[NMAX];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L0[n0++] = v; else L1[n1++] = v;
        }
    }
    for (int i = n0 - 1; i > 0; i--) { int j = rndi(i + 1); int t = L0[i]; L0[i] = L0[j]; L0[j] = t; }
    for (int i = n1 - 1; i > 0; i--) { int j = rndi(i + 1); int t = L1[i]; L1[i] = L1[j]; L1[j] = t; }
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && deg[a] < d; j++) {
            int b = L1[j];
            if (deg[b] >= d || A[a][b]) continue;
            add_e(a, b);
        }
    }
}

/* Add one vertex with greedy cover neighbours. Returns 1 on success. */
static int grow(void) {
    compute_balls();
    int c0 = rndi(2);
    for (int t = 0; t < 2; t++) {
        int c = (t == 0) ? c0 : 1 - c0;
        int out[MAXD];
        int k = greedy_attach(c, out);
        if (k == 0) continue;
        int v = n;
        n++;
        for (int u = 0; u < v; u++) A[u][v] = 0;
        memset(A[v], 0, (size_t)n);
        col[v] = c;
        deg[v] = 0;
        for (int i = 0; i < k; i++) add_e(v, out[i]);
        saturate_all();
        return 1;
    }
    return 0;
}

static int pick_deg_vertex(void) {
    for (int t = 0; t < 100; t++) {
        int v = rndi(n);
        if (deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving 2-switch or endpoint rewire. Returns 1 if a move was applied. */
static int do_move(Move *m) {
    int a = pick_deg_vertex();
    if (a < 0) return 0;
    int b = nbr[a][rndi(deg[a])];
    if (rnd() & 1) {
        int c = -1;
        for (int t = 0; t < 100; t++) {
            int x = rndi(n);
            if (x != a && col[x] == col[a] && deg[x] > 0) { c = x; break; }
        }
        if (c < 0) return 0;
        int e = nbr[c][rndi(deg[c])];
        if (e == b || A[a][e] || A[c][b]) return 0;
        del_e(a, b); del_e(c, e); add_e(a, e); add_e(c, b);
        m->type = 1; m->a = a; m->b = b; m->c = c; m->e = e;
        return 1;
    } else {
        int e = -1;
        for (int t = 0; t < 100; t++) {
            int x = rndi(n);
            if (x != b && col[x] == col[b] && deg[x] < d && !A[a][x]) { e = x; break; }
        }
        if (e < 0) return 0;
        del_e(a, b); add_e(a, e);
        m->type = 2; m->a = a; m->b = b; m->e = e;
        return 1;
    }
}

static void undo_move(const Move *m) {
    if (m->type == 1) {
        del_e(m->a, m->e); del_e(m->c, m->b);
        add_e(m->a, m->b); add_e(m->c, m->e);
    } else {
        del_e(m->a, m->e); add_e(m->a, m->b);
    }
}

static int cand[NMAX];

/* Logged greedy fill of spare degree at x (only adds edges, never raises cost). */
static void fill_logged(int x) {
    if (deg[x] >= d) return;
    int nc = 0;
    for (int y = 0; y < n; y++) {
        if (y != x && col[y] != col[x] && deg[y] < d && !A[x][y]) cand[nc++] = y;
    }
    while (nc > 0 && deg[x] < d) {
        int i = rndi(nc);
        int y = cand[i];
        cand[i] = cand[--nc];
        add_e(x, y);
        logA[nlog] = x; logB[nlog] = y; nlog++;
    }
}

static void undo_logged(void) {
    for (int i = nlog - 1; i >= 0; i--) del_e(logA[i], logB[i]);
    nlog = 0;
}

/* Simulated annealing on bad-pair cost. Returns 1 if cost reaches 0. */
static int sa(long iters) {
    long cur = cost();
    if (cur == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if (timeup()) break;
        double T = 1.0 * (1.0 - (double)it / (double)iters) + 0.05;
        Move mv;
        if (!do_move(&mv)) continue;
        nlog = 0;
        if (mv.type == 2) fill_logged(mv.b);
        long nc = cost();
        long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_logged();
            undo_move(&mv);
        }
    }
    return cur == 0;
}

static void save_best(void) {
    bestN = n;
    bestM = 0;
    for (int v = 0; v < n; v++) {
        bestCol[v] = col[v];
        for (int i = 0; i < deg[v]; i++) {
            int u = nbr[v][i];
            if (u > v) { bestEa[bestM] = v; bestEb[bestM] = u; bestM++; }
        }
    }
}

static void load_best(void) {
    n = bestN;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = bestCol[v];
        memset(A[v], 0, (size_t)n);
    }
    for (int i = 0; i < bestM; i++) add_e(bestEa[i], bestEb[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    t_start = clock();

    long nn = 0, mm = 0;
    if (scanf("%ld %ld", &nn, &mm) != 2 || nn < 1 || mm < 0 || nn > NMAX - 256 ||
        mm > NMAX * MAXD) {
        printf("0 0\n");
        return 0;
    }
    for (long i = 0; i < mm; i++) {
        if (scanf("%d %d", &ia[i], &ib[i]) != 2) { printf("0 0\n"); return 0; }
        if (ia[i] < 0 || ib[i] < 0 || ia[i] >= nn || ib[i] >= nn) { printf("0 0\n"); return 0; }
    }
    if (d < 1 || d > MAXD || D < 2 || D > MAXR - 1) { printf("0 0\n"); return 0; }

    n = (int)nn;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (long i = 0; i < mm; i++) {
        int a = ia[i], b = ib[i];
        if (a == b || A[a][b] || deg[a] >= d || deg[b] >= d) continue;
        add_e(a, b);
    }

    /* Two-colour the input; bail out if it is not bipartite. */
    static int q[NMAX];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int x = nbr[u][i];
                if (col[x] < 0) { col[x] = 1 - col[u]; q[tail++] = x; }
                else if (col[x] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    long c0 = cost();
    if (c0 == 0) save_best();
    else if (sa(3000)) save_best();
    else { printf("0 0\n"); return 0; }

    int fails = 0;
    while (!timeup() && fails < 40) {
        load_best();
        if (!grow()) { fails++; continue; }
        if (sa(1200)) { save_best(); fails = 0; }
        else fails++;
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEa[i], bestEb[i]);
    return 0;
}
"""


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


def _local_cover(cands, ball, full, d, rng, iters, deadline):
    """Plateau-walking swap search for a cover of `full` by at most d candidates.

    Starts from a random d-subset and repeatedly swaps one member for a random
    candidate, keeping swaps that do not lower the number of covered vertices.
    """
    pool = list(cands)
    if not pool:
        return None
    k = min(d, len(pool))
    chosen = rng.sample(pool, k)
    union = 0
    for s in chosen:
        union |= ball[s]
    if union == full:
        return chosen
    score = union.bit_count()
    for _ in range(iters):
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        s = rng.choice(pool)
        if s in chosen:
            continue
        trial = chosen[:]
        trial[i] = s
        u = 0
        for t in trial:
            u |= ball[t]
        sc = u.bit_count()
        if sc >= score:
            chosen, score = trial, sc
            if u == full:
                return chosen
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
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _local_cover(cands, ball, full, d, rng, 400, deadline)
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

    # D = 3: projective planes for the few largest prime powers q with q + 1 <= d,
    # each grown by the twin + cover pipeline within its time slice.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, start + 0.35 * time_limit - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), with randomized restarts of the
    # twin + cover pipeline. The PG path is skipped here, since W(q) is larger.
    pipe_end = start + 0.4 * time_limit
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            while time.monotonic() < pipe_end:
                pn, pe = _pipeline(gq[0], gq[1], d, D, pipe_end, rng)
                consider(pn, pe)

    # Main constructive search (group lifts, Haar, cyclic lifts), time-boxed.
    loop_end = start + (0.5 if D >= 4 else 0.6) * time_limit
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < loop_end:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, loop_end)
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
            S = _search_haar(d, D, haar_m, rng, loop_end, 120)
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
            res = _search_lift(d, D, k, m, rng, 250, loop_end)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    # C repair stage: grow the best graph by one vertex at a time, using greedy cover
    # attachment and simulated annealing on bad pairs. Failures fall back to `best`.
    budget = start + 0.88 * time_limit - time.monotonic() - 3.0
    if D >= 3 and budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 2.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
