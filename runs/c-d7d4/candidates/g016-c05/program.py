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

#define MAXN 2048
#define WMAX 32
#define MAXD 64

static int N, Dd, DIAM;
static int nside[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static uint64_t RA[MAXN][WMAX], RB[MAXN][WMAX];
static int S0[MAXN];
static int n0cnt;

static int bsN = 0;
static int bsDeg[MAXN];
static int bsAdj[MAXN][MAXD];
static int bsSide[MAXN];
static int have_best = 0;

static int ua, ui, ub, uib, uc, uj, ue, uie;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double runif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t T0;
static double TLIM;
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static int idx_of(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return k;
    return -1;
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void remove_edge(int a, int b) {
    int i = idx_of(a, b);
    adj[a][i] = adj[a][deg[a] - 1];
    deg[a]--;
    int j = idx_of(b, a);
    adj[b][j] = adj[b][deg[b] - 1];
    deg[b]--;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static int cost(void) {
    int nw = (N + 63) >> 6;
    uint64_t (*cur)[WMAX] = RA;
    uint64_t (*nxt)[WMAX] = RB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DIAM; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(cur[v][w]);
        bad += N - c;
    }
    return (int)(bad / 2);
}

static int color_graph(void) {
    static int stk[MAXN];
    for (int v = 0; v < N; v++) nside[v] = -1;
    for (int s = 0; s < N; s++) {
        if (nside[s] >= 0) continue;
        nside[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (nside[v] < 0) {
                    nside[v] = 1 - nside[u];
                    stk[sp++] = v;
                } else if (nside[v] == nside[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Greedily join deficient opposite-side pairs (only lowers the cost). */
static void fill_all(void) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int a = 0; a < N; a++) {
            if (nside[a] != 0 || deg[a] >= Dd) continue;
            for (int b = 0; b < N; b++) {
                if (deg[a] >= Dd) break;
                if (nside[b] != 1 || deg[b] >= Dd) continue;
                if (!has_edge(a, b)) {
                    add_edge(a, b);
                    changed = 1;
                }
            }
        }
    }
}

static int try_add_edge(void) {
    int ds0[MAXN], ds1[MAXN], c0 = 0, c1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < Dd) {
            if (nside[v] == 0) ds0[c0++] = v;
            else ds1[c1++] = v;
        }
    }
    if (c0 == 0 || c1 == 0) return 0;
    for (int t = 0; t < 30; t++) {
        int a = ds0[rint_(c0)], b = ds1[rint_(c1)];
        if (!has_edge(a, b)) {
            add_edge(a, b);
            return 1;
        }
    }
    return 0;
}

/* Degree-preserving bipartite double-edge switch: (a,b),(c,e) -> (a,e),(c,b). */
static int do_switch(void) {
    if (n0cnt < 2) return 0;
    int a = S0[rint_(n0cnt)];
    if (deg[a] == 0) return 0;
    int c = S0[rint_(n0cnt)];
    if (c == a || deg[c] == 0) return 0;
    int i = rint_(deg[a]), b = adj[a][i];
    int j = rint_(deg[c]), e = adj[c][j];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    int ib = idx_of(b, a), ie = idx_of(e, c);
    adj[a][i] = e;
    adj[c][j] = b;
    adj[b][ib] = c;
    adj[e][ie] = a;
    ua = a; ui = i; ub = b; uib = ib;
    uc = c; uj = j; ue = e; uie = ie;
    return 1;
}

static void undo_switch(void) {
    adj[ua][ui] = ub;
    adj[uc][uj] = ue;
    adj[ub][uib] = ua;
    adj[ue][uie] = uc;
}

static int anneal(long iters, double ta, double tb) {
    int cur = cost();
    if (cur == 0) return 1;
    n0cnt = 0;
    for (int v = 0; v < N; v++) if (nside[v] == 0) S0[n0cnt++] = v;
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() > TLIM) break;
        double T = ta + (tb - ta) * (double)it / (double)iters;
        if (runif() < 0.05) {
            if (try_add_edge()) {
                cur = cost();
                if (cur == 0) return 1;
            }
            continue;
        }
        if (!do_switch()) continue;
        int nc = cost();
        int delta = nc - cur;
        if (delta <= 0 || runif() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_switch();
        }
    }
    return cur == 0;
}

static void shuffle_ints(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Attach new vertex nv to d old vertices on side opp; steal an edge from full ones. */
static void attach(int nv, int opp, int N0) {
    int cand[MAXN], nc = 0, pick[MAXD], np = 0;
    for (int v = 0; v < N0; v++) if (nside[v] == opp) cand[nc++] = v;
    shuffle_ints(cand, nc);
    for (int i = 0; i < nc && np < Dd; i++) if (deg[cand[i]] < Dd) pick[np++] = cand[i];
    for (int i = 0; i < nc && np < Dd; i++) if (deg[cand[i]] >= Dd) pick[np++] = cand[i];
    for (int p = 0; p < np; p++) {
        int y = pick[p];
        if (deg[y] >= Dd) {
            int k = rint_(deg[y]);
            int z = adj[y][k];
            remove_edge(y, z);
        }
        add_edge(nv, y);
    }
}

static void grow_pair(void) {
    int N0 = N, a = N0, b = N0 + 1;
    N = N0 + 2;
    nside[a] = 0;
    nside[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    attach(a, 1, N0);
    attach(b, 0, N0);
    fill_all();
}

static void save_best(void) {
    if (cost() != 0) return;
    bsN = N;
    for (int v = 0; v < N; v++) {
        bsDeg[v] = deg[v];
        bsSide[v] = nside[v];
        memcpy(bsAdj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
    have_best = 1;
}

static void restore_best(void) {
    N = bsN;
    for (int v = 0; v < N; v++) {
        deg[v] = bsDeg[v];
        nside[v] = bsSide[v];
        memcpy(adj[v], bsAdj[v], sizeof(int) * (size_t)deg[v]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    TLIM = atof(argv[4]);
    T0 = clock();

    if (Dd < 1 || Dd > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int ok = 1;
    if (n == 0 && m == 0) {
        N = 2;
        add_edge(0, 1);
        nside[0] = 0;
        nside[1] = 1;
    } else {
        if (n < 1 || n > MAXN - 2 || m < 0) ok = 0;
        else {
            N = n;
            for (int i = 0; i < m && ok; i++) {
                int u, v;
                if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
                if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
                if (deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) { ok = 0; break; }
                add_edge(u, v);
            }
        }
        if (ok && !color_graph()) ok = 0;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    fill_all();
    int ok2 = (cost() == 0);
    if (!ok2) ok2 = anneal(20000, 0.6, 0.05);
    int fails = 0;

    while (elapsed() < TLIM) {
        if (ok2) {
            save_best();
            fails = 0;
        } else if (have_best) {
            restore_best();
            fails++;
        } else {
            ok2 = anneal(30000, 0.6, 0.05);
            continue;
        }
        if (N + 2 > MAXN - 2) break;
        grow_pair();
        int extra = fails < 10 ? fails : 10;
        long iters = 15000 + 4000L * extra;
        ok2 = anneal(iters, 0.6, 0.05);
    }
    if (ok2) save_best();

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    int mm = 0;
    for (int v = 0; v < bsN; v++) mm += bsDeg[v];
    mm /= 2;
    printf("%d %d\n", bsN, mm);
    for (int v = 0; v < bsN; v++)
        for (int k = 0; k < bsDeg[v]; k++) {
            int u = bsAdj[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
'''


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
# Bipartite voltage lifts over small groups (Python phase).
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
# C engine: bitset-based simulated annealing with vertex-pair growth.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, n, e, budget):
    """Run the C annealer from (n, e) for about `budget` seconds. Returns (n, e) or raises."""
    out = lib.run_c(C_SOURCE, [d, D, int(seed) & 0xFFFFFFFF, round(budget, 2)],
                    stdin_graph=(n, e), timeout=budget + 5.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Driver. Fractions of the usable budget T = 0.85 * time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, twin trials
#   L  bipartite voltage lifts over cyclic / semidirect groups
#   C  C annealer: grows the best valid graph by bipartite vertex pairs
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

    # Phase A: structured small base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.22):
        _lift_search(d, D, best_n, rng, at(0.22), consider)

    # Phase C: bitset annealing in C from the best valid graph found so far.
    if D >= 2 and 2 <= d <= 64 and best_n < lib.moore_bound(d, D):
        budget = at(1.0) - time.monotonic()
        if budget > 2.0:
            try:
                n, e = _c_search(d, D, seed, best_n, best_e, 0.93 * budget)
                consider(n, e)
            except (RuntimeError, ValueError, OSError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
