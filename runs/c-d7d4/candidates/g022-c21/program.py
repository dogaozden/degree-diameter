import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
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
# Bipartite voltage lifts over small groups (cyclic or semidirect).
# ----------------------------------------------------------------------------

def _pick_group(order, rng):
    """Return (order, mul) for a cyclic or a semidirect group of the given order."""
    if order >= 4 and rng.random() < 0.5:
        ks = [k for k in range(2, 13) if order % k == 0 and order // k >= 2]
        rng.shuffle(ks)
        for k in ks:
            m = order // k
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                r = rng.choice(rs)
                try:
                    o, mul, _ = lib.semidirect_group(m, k, r)
                    return o, mul
                except ValueError:
                    continue
    o, mul, _ = lib.cyclic_group(order)
    return o, mul


def _init_darts(s, d, order, rng):
    """Darts (u, v, g): A vertex u, B vertex v (local indices), voltage g. Each A and B vertex gets d darts."""
    slots = [v for v in range(s) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    seen = set()
    for u in range(s):
        for j in range(d):
            v = slots[u * d + j]
            for _ in range(60):
                g = rng.randrange(order)
                if (u, v, g) not in seen:
                    break
            else:
                return None
            seen.add((u, v, g))
            darts.append((u, v, g))
    return darts


def _lift(s, darts, order, mul):
    """Lift the base graph: A side is 0..s-1, B side is s..2s-1 in the base."""
    return lib.group_lift(2 * s, [(u, s + v, g) for u, v, g in darts], order, mul)


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Hill-climb voltages of random bipartite base lifts until a diameter-D lift appears."""
    base_pick = (1, 1, 2, 2, 3)
    while time.monotonic() < deadline:
        s = rng.choice(base_pick)
        base_n = 2 * s
        lo = best_n // base_n
        order = lo + 1 + rng.randrange(0, max(2, lo // 8 + 1))
        order, mul = _pick_group(order, rng)
        darts = _init_darts(s, d, order, rng)
        if darts is None:
            continue
        n, e = _lift(s, darts, order, mul)
        cost = lib.bad_pairs(n, e, D)
        steps = 0
        while cost > 0 and steps < 250 and time.monotonic() < deadline:
            steps += 1
            i = rng.randrange(len(darts))
            u, v, old = darts[i]
            g2 = rng.randrange(order)
            if g2 == old or (u, v, g2) in set(darts):
                continue
            darts[i] = (u, v, g2)
            n2, e2 = _lift(s, darts, order, mul)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cost or rng.random() < 0.02:
                cost, n, e = c2, n2, e2
            else:
                darts[i] = (u, v, old)
        if cost == 0 and time.monotonic() < deadline:
            if n > best_n and lib.is_valid(n, e, d, D):
                consider(n, e)
                best_n = max(best_n, n)
            n3, e3 = _grow(n, e, d, D, deadline, rng)
            consider(n3, e3)
            best_n = max(best_n, n3)


# ----------------------------------------------------------------------------
# C engine: cover-guided growth plus simulated annealing over bipartite moves.
#
# State: a bipartite graph with max degree d. Cost = number of vertex pairs at
# distance > D. Moves: add an edge between deficient vertices, degree-preserving
# double-edge switch, shift an endpoint to a deficient vertex, remove an edge.
# When cost reaches 0 the graph is saved and grown by one vertex whose
# neighbourhood is a greedy cover (radius D-1 balls). If annealing stalls, the
# best saved graph is restored and grown again with different tie-breaks.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1100
#define WMAX ((MAXN + 63) / 64)
#define MAXD 40
#define MAXE (MAXN * MAXD)
#define STALL 30000

static int d, D, n;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static uint64_t wa[MAXN][WMAX], wb[MAXN][WMAX], ballr[MAXN][WMAX];
static int Lv[MAXN], Rv[MAXN], nL, nR;
static int bsn, bside[MAXN], beu[MAXE], bev[MAXE], bsm;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int irand(int k) { return (int)(rnd() % (uint64_t)k); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rm_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; return; }
}

static void add_edge(int u, int v) {
    A[u][v] = 1; A[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    A[u][v] = 0; A[v][u] = 0;
    rm_nb(u, v); rm_nb(v, u);
}

static void build_lists(void) {
    nL = 0; nR = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) Lv[nL++] = v; else Rv[nR++] = v;
    }
}

/* out[v] = bitset of vertices within distance r of v. */
static void ball_compute(int r, uint64_t out[][WMAX]) {
    int w = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = wa;
    uint64_t (*nxt)[WMAX] = wb;
    uint64_t (*tmp)[WMAX];
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) cur[v][k] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < r; t++) {
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < w; k++) nxt[v][k] = cur[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int k = 0; k < w; k++) nxt[v][k] |= cur[u][k];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    for (int v = 0; v < n; v++)
        for (int k = 0; k < w; k++) out[v][k] = cur[v][k];
}

static int bad_pairs(void) {
    int w = (n + 63) >> 6;
    ball_compute(D, ballr);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int p = 0;
        for (int k = 0; k < w; k++) p += pc64(ballr[v][k]);
        bad += n - p;
    }
    return (int)(bad / 2);
}

/* Add one vertex on the side whose greedy cover of the other side's balls is best. */
static int grow(void) {
    if (n + 2 >= MAXN) return 0;
    int w = (n + 63) >> 6;
    ball_compute(D - 1, ballr);
    int bestSide = -1, bestUnc = 1 << 30, bestCh[MAXD], bestNch = 0;
    for (int s = 0; s < 2; s++) {
        uint64_t U[WMAX];
        for (int k = 0; k < w; k++) U[k] = 0;
        for (int v = 0; v < n; v++) U[v >> 6] |= 1ULL << (v & 63);
        int cand[MAXN], nc = 0;
        for (int v = 0; v < n; v++)
            if (side[v] == 1 - s && deg[v] < d) cand[nc++] = v;
        int ch[MAXD], nch = 0;
        while (nch < d && nc > 0) {
            int bg = 0, bi = -1, ties = 0;
            for (int i = 0; i < nc; i++) {
                int v = cand[i], g = 0;
                for (int k = 0; k < w; k++) g += pc64(ballr[v][k] & U[k]);
                if (g > bg) { bg = g; bi = i; ties = 1; }
                else if (g == bg && g > 0) {
                    ties++;
                    if (irand(ties) == 0) bi = i;
                }
            }
            if (bi < 0) break;
            int v = cand[bi];
            ch[nch++] = v;
            for (int k = 0; k < w; k++) U[k] &= ~ballr[v][k];
            cand[bi] = cand[--nc];
        }
        int unc = 0;
        for (int k = 0; k < w; k++) unc += pc64(U[k]);
        if (unc < bestUnc || (unc == bestUnc && irand(2) == 0)) {
            bestUnc = unc; bestSide = s; bestNch = nch;
            for (int i = 0; i < nch; i++) bestCh[i] = ch[i];
        }
    }
    if (bestSide < 0) return 0;
    int v = n;
    memset(A[v], 0, MAXN);
    for (int x = 0; x < n; x++) A[x][v] = 0;
    side[v] = bestSide;
    deg[v] = 0;
    n++;
    for (int i = 0; i < bestNch; i++) add_edge(v, bestCh[i]);
    return 1;
}

static void save_best(void) {
    bsn = n; bsm = 0;
    for (int v = 0; v < n; v++) bside[v] = side[v];
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (u > v) { beu[bsm] = v; bev[bsm] = u; bsm++; }
        }
}

static void restore_best(void) {
    for (int v = 0; v < n; v++) { deg[v] = 0; memset(A[v], 0, n); }
    n = bsn;
    for (int v = 0; v < n; v++) side[v] = bside[v];
    for (int i = 0; i < bsm; i++) add_edge(beu[i], bev[i]);
    build_lists();
}

static void apply_move(int kind, int a, int b, int c, int e) {
    switch (kind) {
    case 0: add_edge(a, b); break;
    case 1: del_edge(a, b); del_edge(c, e); add_edge(a, e); add_edge(c, b); break;
    case 2: del_edge(a, b); add_edge(a, c); break;
    default: del_edge(a, b); break;
    }
}

static void undo_move(int kind, int a, int b, int c, int e) {
    switch (kind) {
    case 0: del_edge(a, b); break;
    case 1: del_edge(a, e); del_edge(c, b); add_edge(a, b); add_edge(c, e); break;
    case 2: del_edge(a, c); add_edge(a, b); break;
    default: add_edge(a, b); break;
    }
}

static int colour_graph(void) {
    static int q[MAXN];
    int head = 0, tail = 0;
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++];
            for (int i = 0; i < deg[x]; i++) {
                int y = nb[x][i];
                if (side[y] < 0) { side[y] = 1 - side[x]; q[tail++] = y; }
                else if (side[y] == side[x]) return 0;
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double limit = atof(argv[4]);
    if (d < 1 || d >= MAXD || D < 2) { printf("0 0\n"); return 0; }

    int rn = 0, rm = 0;
    if (scanf("%d %d", &rn, &rm) != 2) { rn = 0; rm = 0; }
    if (rn >= MAXN - 2 || rm < 0 || rm > MAXE) { printf("0 0\n"); return 0; }
    static int eu[MAXE], ev[MAXE];
    n = 0;
    if (rn == 0) {
        n = 2; side[0] = 0; side[1] = 1;
        add_edge(0, 1);
    } else {
        n = rn;
        int ok = 1;
        for (int i = 0; i < rm; i++)
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
        for (int i = 0; ok && i < rm; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                deg[u] >= d || deg[v] >= d || A[u][v]) { ok = 0; break; }
            add_edge(u, v);
        }
        if (ok) ok = colour_graph();
        if (!ok) { printf("0 0\n"); return 0; }
    }

    build_lists();
    save_best();
    int cur = bad_pairs();
    double deadline = cpu_now() + limit * 0.85;
    double T = 0.3;
    long stall = 0;

    while (cpu_now() < deadline) {
        if (cur == 0) {
            save_best();
            if (!grow()) break;
            build_lists();
            cur = bad_pairs();
            stall = 0;
            continue;
        }
        if (++stall > STALL) {
            restore_best();
            cur = 0;
            stall = 0;
            T = 0.2 + 0.4 * urand();
            continue;
        }
        if (nL == 0 || nR == 0) break;

        double r = urand();
        int kind = r < 0.12 ? 0 : (r < 0.55 ? 1 : (r < 0.97 ? 2 : 3));
        int a = -1, b = -1, c = -1, e = -1, ok = 0;
        for (int tries = 0; tries < 20 && !ok; tries++) {
            if (kind == 0) {
                a = Lv[irand(nL)];
                b = Rv[irand(nR)];
                ok = deg[a] < d && deg[b] < d && !A[a][b];
            } else if (kind == 1) {
                a = Lv[irand(nL)];
                c = Lv[irand(nL)];
                if (!deg[a] || !deg[c]) continue;
                b = nb[a][irand(deg[a])];
                e = nb[c][irand(deg[c])];
                ok = a != c && b != e && !A[a][e] && !A[c][b];
            } else {
                a = Lv[irand(nL)];
                if (!deg[a]) continue;
                b = nb[a][irand(deg[a])];
                if (kind == 2) {
                    c = Rv[irand(nR)];
                    ok = deg[c] < d && c != b && !A[a][c];
                } else {
                    ok = 1;
                }
            }
        }
        if (!ok) continue;

        apply_move(kind, a, b, c, e);
        int nc = bad_pairs();
        int delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) cur = nc;
        else undo_move(kind, a, b, c, e);
    }

    if (cur == 0) save_best();
    printf("%d %d\n", bsn, bsm);
    for (int i = 0; i < bsm; i++) printf("%d %d\n", beu[i], bev[i]);
    return 0;
}
"""


def _engine(d, D, seed, n, edges, budget):
    """Run the C annealing engine from a valid start graph; return (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=(n, edges), timeout=budget + 5.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Driver. Phases (fractions of the usable budget T = 0.85 * time_limit):
#   A  structured base (W(q) or PG(2,q)) grown, twin trials
#   L  bipartite voltage lifts over cyclic / semidirect groups
#   C  C annealing engine with cover-guided growth, from the best valid graph
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), which is valid for every d >= 1 and D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured small base, grown, then twin/cover trials.
    if D >= 2:
        base_n, base_e = best_n, list(best_e)
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                consider(n0, e0)
                base_n, base_e = n0, list(e0)
                n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
                consider(n1, e1)
        trial_end = at(0.20)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.35):
        _lift_search(d, D, best_n, rng, at(0.35), consider)

    # Phase C: C annealing with cover-guided growth from the best valid graph.
    if D >= 2 and d <= 30 and best_n < 1000:
        budget = (start + T - time.monotonic()) * 0.9
        if budget > 2.0:
            try:
                n, e = _engine(d, D, seed, best_n, best_e, budget)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
