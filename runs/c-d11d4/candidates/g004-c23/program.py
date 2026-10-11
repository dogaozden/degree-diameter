import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: annealing with vertex growth and bad-pair-focused rewiring.
#
# Each state is a bipartite graph with max degree DEG and a diameter cost
# (number of unordered vertex pairs at distance > DIAM). Moves:
#   * swap: take edges a-b and c-e (a, c on side 0), replace them by a-e and c-b.
#     Degrees and bipartiteness are preserved.
#   * focused (new): pick a bad pair (u, w) reported by the last evaluation.
#     Pick x in N(w), a in N(x), so dist(a, w) = 2. Then join a to u using
#     spare degree, or by a 2-switch that frees one slot on each side.
#     This shortens the bad pair directly instead of hoping a random swap does.
#   * grow: add a vertex on a random side, joined to up to DEG opposite-side
#     vertices. Growth is accepted unconditionally, then moves repair the cost.
# Each move is logged as a removal list and an addition list, so undo is exact.
# Whenever the cost reaches 0 the state is saved as the best valid graph.
# If repair stalls, the search restarts from the best saved graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define STALL 1500

static int DEG, DIAM;
static double PFOC = 0.5;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestNv;
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static uint64_t rs = 1;
static int badc[MAXN], badlist[MAXN];
static int last_bu = -1, last_bw = -1;
static int cur_bu = -1, cur_bw = -1;
static int defi[MAXN], fulli[MAXN], stk[MAXN];
static int nrem, nadd;
static int remA[4], remB[4], addA[4], addB[4];

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Returns the number of bad unordered pairs. Also sets last_bu/last_bw to a
   random bad pair (u, w), or -1 when the graph is valid. */
static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    int nb = 0;
    for (int v = 0; v < nv; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        badc[v] = nv - cnt;
        bad += badc[v];
        if (badc[v] > 0) badlist[nb++] = v;
    }
    last_bu = -1;
    last_bw = -1;
    if (nb > 0) {
        int v = badlist[rnd(nb)];
        uint64_t *s = cur + (size_t)v * W;
        int start = rnd(nv), found = -1;
        for (int k = 0; k < nv; k++) {
            int w = start + k;
            if (w >= nv) w -= nv;
            if (!((s[w >> 6] >> (w & 63)) & 1ULL)) {
                found = w;
                break;
            }
        }
        last_bu = v;
        last_bw = found;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static void add_edge(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void log_reset(void) {
    nrem = 0;
    nadd = 0;
}

static void plan_rem(int a, int b) {
    remA[nrem] = a;
    remB[nrem] = b;
    nrem++;
}

static void plan_add(int a, int b) {
    addA[nadd] = a;
    addB[nadd] = b;
    nadd++;
}

static void apply_plan(void) {
    for (int i = 0; i < nrem; i++) remove_edge(remA[i], remB[i]);
    for (int i = 0; i < nadd; i++) add_edge(addA[i], addB[i]);
}

static void undo_plan(void) {
    for (int i = 0; i < nadd; i++) remove_edge(addA[i], addB[i]);
    for (int i = 0; i < nrem; i++) add_edge(remA[i], remB[i]);
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static int swap_move(void) {
    int tries = 0;
    int a = 0, c = 0;
    do {
        a = rnd(nv);
        c = rnd(nv);
        tries++;
    } while ((col[a] != 0 || deg[a] == 0 || col[c] != 0 || deg[c] == 0) && tries < 1000);
    if (tries >= 1000) return 0;
    int b = adjv[a][rnd(deg[a])];
    int e = adjv[c][rnd(deg[c])];
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    log_reset();
    plan_rem(a, b);
    plan_rem(c, e);
    plan_add(a, e);
    plan_add(c, b);
    apply_plan();
    return 1;
}

/* Focused move on the current bad pair (u, w). */
static int focused_move(void) {
    int u = cur_bu, w = cur_bw;
    if (u < 0 || w < 0 || u >= nv || w >= nv) return 0;
    if (deg[w] == 0) return 0;
    int x = adjv[w][rnd(deg[w])];
    if (deg[x] < 2) return 0;
    int a = adjv[x][rnd(deg[x])];
    if (a == w || a == u) return 0;          /* dist(a, w) = 2 */
    if (col[a] == col[u]) return 0;
    if (has_edge(a, u)) return 0;
    int cu = deg[u] < DEG;
    int ca = deg[a] < DEG;
    log_reset();
    if (cu && ca) {
        plan_add(a, u);
    } else if (ca) {
        /* u full: drop u-c, c regains a slot */
        int c = adjv[u][rnd(deg[u])];
        plan_rem(u, c);
        plan_add(a, u);
    } else if (cu) {
        /* a full: drop a-b, b regains a slot */
        int b = adjv[a][rnd(deg[a])];
        plan_rem(a, b);
        plan_add(a, u);
    } else {
        /* both full: 2-switch a-b, u-c -> a-u, b-c (b and c on opposite sides) */
        int b = adjv[a][rnd(deg[a])];
        int c = adjv[u][rnd(deg[u])];
        if (b == c || has_edge(b, c)) return 0;
        plan_rem(a, b);
        plan_rem(u, c);
        plan_add(a, u);
        plan_add(b, c);
    }
    apply_plan();
    return 1;
}

static void grow(void) {
    int c = rnd(2);
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    int nd = 0, nf = 0;
    for (int w = 0; w < v; w++) {
        if (col[w] != 1 - c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        add_edge(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        remove_edge(w, x);
        add_edge(v, w);
        k++;
    }
}

static void save_best(void) {
    memcpy(bestAdj, adjv, sizeof adjv);
    memcpy(bestDeg, deg, sizeof deg);
    memcpy(bestCol, col, sizeof col);
    bestNv = nv;
}

static void restore_best(void) {
    memcpy(adjv, bestAdj, sizeof adjv);
    memcpy(deg, bestDeg, sizeof deg);
    memcpy(col, bestCol, sizeof col);
    nv = bestNv;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) { deg[i] = 0; col[i] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    if (nv == 0) {
        printf("0 0\n");
        return 0;
    }

    /* two-colour the start graph by DFS */
    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    long long cur_cost = eval_cost();
    cur_bu = last_bu;
    cur_bw = last_bw;
    save_best();
    int have_valid = (cur_cost == 0);
    double T = 0.4;
    long stall = 0;
    double tstart = (double)clock() / CLOCKS_PER_SEC;

    while (1) {
        double el = (double)clock() / CLOCKS_PER_SEC - tstart;
        if (el >= tl) break;

        if (cur_cost == 0) {
            if (nv > bestNv || !have_valid) {
                save_best();
                have_valid = 1;
            }
            if (nv + 1 >= MAXN) break;
            grow();
            cur_cost = eval_cost();
            cur_bu = last_bu;
            cur_bw = last_bw;
            stall = 0;
            continue;
        }

        int ok = (rnd01() < PFOC) ? focused_move() : swap_move();
        if (!ok) continue;
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur_cost);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur_cost = c2;
            cur_bu = last_bu;
            cur_bw = last_bw;
        } else {
            undo_plan();
        }
        if (++stall > STALL) {
            restore_best();
            cur_cost = eval_cost();
            cur_bu = last_bu;
            cur_bw = last_bw;
            stall = 0;
            T = 0.3 + 0.4 * rnd01();
        }
    }

    long long em = 0;
    for (int v = 0; v < bestNv; v++) em += bestDeg[v];
    printf("%d %lld\n", bestNv, em / 2);
    for (int v = 0; v < bestNv; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
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
    # Targets (D >= 4, d >= 5) hand the best graph to the C annealer for most of the budget.
    use_c = D >= 4 and d >= 5
    frac = 0.25 if use_c else 0.85
    deadline = start + frac * time_limit
    ext_deadline = start + 0.5 * frac * time_limit
    pipe_end = start + 0.7 * frac * time_limit
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

    # D >= 3: projective planes for the few largest prime powers q with q + 1 <= d,
    # each grown by the twin + cover pipeline within its time slice.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q). Repeated randomized restarts of the
    # twin + cover pipeline; the best valid result is kept.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            while time.monotonic() < pipe_end:
                pn, pe = _pipeline(gq[0], gq[1], d, D, pipe_end, rng)
                consider(pn, pe)

    # Main search. For D >= 4 the non-cyclic group-lift family dominates.
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

    # Annealing with vertex growth and focused rewiring in C, started from the best valid graph.
    # Any failure (compile, timeout, bad output) keeps the Python result.
    if use_c:
        budget = start + 0.88 * time_limit - time.monotonic() - 1.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=budget + 15.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
