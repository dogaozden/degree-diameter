import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bit-parallel bad-pair annealing with degree-preserving bipartite
# switches, plus vertex insertion that is kept only when repair reaches zero.
# Input: "n m" and edges (valid, bipartite, max degree d), or "0 0" for K_{d,d}.
# Output: the largest valid graph found, in the same format ("0 0" if none).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 16
#define WMAX 18

static int d, D, n;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t BA[MAXN][WMAX], BB[MAXN][WMAX];
static int W;
static int s0[MAXN];

static int sN;
static int sAdj[MAXN][MAXD];
static int sDeg[MAXN];
static int sCol[MAXN];

static int bN = 0;
static int bAdj[MAXN][MAXD];
static int bDeg[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int has(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void addE(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void delE(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) { adj[u][i] = adj[u][deg[u] - 1]; deg[u]--; break; }
    for (int i = 0; i < deg[v]; i++)
        if (adj[v][i] == u) { adj[v][i] = adj[v][deg[v] - 1]; deg[v]--; break; }
}

/* Number of unordered vertex pairs at distance > D. */
static long long cost(void) {
    W = (n + 63) / 64;
    uint64_t (*cur)[WMAX] = BA;
    uint64_t (*nxt)[WMAX] = BB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[adj[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        miss += n - c;
    }
    return miss / 2;
}

static int colour_graph(void) {
    static int stk[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void snap_save(void) {
    sN = n;
    memcpy(sAdj, adj, sizeof adj);
    memcpy(sDeg, deg, sizeof deg);
    memcpy(sCol, col, sizeof col);
}

static void snap_restore(void) {
    n = sN;
    memcpy(adj, sAdj, sizeof adj);
    memcpy(deg, sDeg, sizeof deg);
    memcpy(col, sCol, sizeof col);
}

static void save_best(void) {
    bN = n;
    memcpy(bAdj, adj, sizeof adj);
    memcpy(bDeg, deg, sizeof deg);
}

/* Add edges between deficient opposite-side vertices; only lowers the cost. */
static void fill_edges(void) {
    for (int a = 0; a < n; a++) {
        if (col[a] != 0 || deg[a] >= d) continue;
        for (int b = 0; b < n && deg[a] < d; b++) {
            if (col[b] != 1 || deg[b] >= d || has(a, b)) continue;
            addE(a, b);
        }
    }
}

/* Degree-preserving bipartite switches minimising the cost. Returns final cost. */
static long long anneal(long long cur, long long iters, double deadline) {
    int m0 = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == 0) s0[m0++] = v;
    if (m0 < 2) return cur;
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && cpu_now() > deadline) break;
        double frac = (double)it / (double)iters;
        double T = 0.7 * (1.0 - frac) + 0.05;
        int a = s0[rndint(m0)];
        int c = s0[rndint(m0)];
        if (a == c || deg[a] == 0 || deg[c] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has(a, e) || has(c, b)) continue;
        delE(a, b);
        delE(c, e);
        addE(a, e);
        addE(c, b);
        long long nw = cost();
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nw;
        } else {
            delE(a, e);
            delE(c, b);
            addE(a, b);
            addE(c, e);
        }
    }
    return cur;
}

/* Add one vertex on a random side, joined to d opposite-side vertices (stealing
   edges from full vertices when needed). Caller restores the snapshot on failure. */
static int grow_once(void) {
    int s = rndint(2);
    int v = n++;
    col[v] = s;
    deg[v] = 0;
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (col[u] == 1 - s && deg[u] < d) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int k = 0;
    for (int i = 0; i < nc && k < d; i++) {
        addE(v, cand[i]);
        k++;
    }
    int tries = 0;
    while (k < d && tries < 5000) {
        tries++;
        int u = rndint(v);
        if (col[u] != 1 - s || has(v, u)) continue;
        if (deg[u] >= d) {
            if (deg[u] == 0) continue;
            int w = adj[u][rndint(deg[u])];
            delE(u, w);
        }
        addE(v, u);
        k++;
    }
    return k == d;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x2545F4914F6CDD1DULL + 1ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    double deadline = cpu_now() + budget;
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 == 0) {
        n = 2 * d;
        for (int i = 0; i < n; i++) { deg[i] = 0; col[i] = (i < d) ? 0 : 1; }
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) addE(i, d + j);
    } else {
        if (n0 >= MAXN - 2) { printf("0 0\n"); return 0; }
        n = n0;
        for (int i = 0; i < n; i++) deg[i] = 0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
            if (deg[u] >= d || deg[v] >= d || has(u, v)) continue;
            addE(u, v);
        }
        if (!colour_graph()) {
            printf("0 0\n");
            return 0;
        }
    }

    bN = 0;
    fill_edges();
    long long cur = cost();
    if (cur == 0) save_best();

    while (cpu_now() < deadline) {
        if (n + 2 >= MAXN) break;
        if (cur != 0) {
            cur = anneal(cur, 4000, deadline);
            if (cur == 0) save_best();
            continue;
        }
        snap_save();
        if (!grow_once()) {
            snap_restore();
            continue;
        }
        fill_edges();
        cur = cost();
        cur = anneal(cur, 3000, deadline);
        if (cur == 0) {
            save_best();
        } else {
            snap_restore();
            cur = 0;
        }
    }

    if (bN == 0) {
        printf("0 0\n");
        return 0;
    }
    long long m = 0;
    for (int u = 0; u < bN; u++)
        for (int i = 0; i < bDeg[u]; i++)
            if (bAdj[u][i] > u) m++;
    printf("%d %lld\n", bN, m);
    for (int u = 0; u < bN; u++)
        for (int i = 0; i < bDeg[u]; i++)
            if (bAdj[u][i] > u) printf("%d %d\n", u, bAdj[u][i]);
    return 0;
}
"""


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
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
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
    """Greedy set cover of `full` by at most d candidates. Returns list or None."""
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
    """Greedily add vertices whose neighbourhoods cover the vertices at distance D-1."""
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
    """Greedily join deficient opposite-side vertices in random order. Only shortens distances."""
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
# Twin duplication: a non-adjacent twin w of v (N(w) = N(v)) keeps all distances
# to other vertices and only needs spare degree on the neighbours of v.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
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
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
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
# Voltage lifts over non-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
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
    if order < 2:
        return None
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
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


def _group_phase(d, D, best, rng, deadline, consider):
    """Adaptive group-lift search; `best` is a dict holding the current best 'n'."""
    group_sizes = [1, 2, 3, 4]
    state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    while time.monotonic() < deadline:
        k = rng.choice(group_sizes)
        st = state[k]
        floor = best["n"] // (2 * k) + 1
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


# ----------------------------------------------------------------------------
# Main build: short Python start-up, then the C annealing/growth engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = {"n": fb_n, "e": list(fb_e)}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = list(e)

    # Python start-up: structured base, then short group and twin pipelines.
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
        else:
            base_n, base_e = best["n"], list(best["e"])
    else:
        base_n, base_e = best["n"], list(best["e"])

    if D >= 4:
        _group_phase(d, D, best, rng, start + 0.2 * time_limit, consider)

    if D >= 2:
        trial_end = start + 0.3 * time_limit
        while time.monotonic() < trial_end:
            if rng.random() < 0.5:
                src_n, src_e = base_n, base_e
            else:
                src_n, src_e = best["n"], best["e"]
            n, e = _trial(src_n, src_e, d, D, rng, trial_end)
            consider(n, e)

    # C stage: anneal and grow from the best graph found so far.
    end = start + 0.9 * time_limit - 2.0
    remaining = end - time.monotonic()
    if D >= 2 and remaining > 4.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 2.0, 2)],
                            stdin_graph=(best["n"], best["e"]),
                            timeout=remaining)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    n_out, e_out = best["n"], best["e"]
    if not lib.is_valid(n_out, e_out, d, D):
        return fb_n, list(fb_e)
    return n_out, list(e_out)
