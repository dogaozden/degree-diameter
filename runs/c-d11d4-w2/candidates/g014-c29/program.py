import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: hill-climbing search for voltage lifts over semidirect groups
# Z_m x| Z_k. The base graph is K + K vertices, each left vertex has DEG darts
# to right vertices (a union of DEG random perfect matchings between the sides).
# A dart (u, v, g) joins (u, x) to (v, x*g) for every group element x.
# Cost = number of unordered vertex pairs at distance > DIAM, computed with
# bitset BFS. Random restarts plus single-voltage hill climbing; prints the
# first zero-cost lift and exits, otherwise prints "0 0".
# ----------------------------------------------------------------------------

C_GROUP = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define WMAX ((MAXN + 63) / 64)
#define MAXD 16
#define MAXK 4
#define MAXDART (MAXK * MAXD)
#define ITER 1500

static int DEGR, DIAM, KB, GM, GK, GR, ORD, NV, ND;
static int pw[64];
static int dU[MAXDART], dV[MAXDART], dG[MAXDART];
static int adj[MAXN][MAXD], dg[MAXN];
static uint64_t RA[MAXN * WMAX], RB[MAXN * WMAX];
static uint64_t rs = 88172645463325252ULL;

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

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return ((a + pw[b] * c) % GM) * GK + (b + e) % GK;
}

static int has_nb(int a, int b) {
    for (int i = 0; i < dg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void build_graph(void) {
    NV = 2 * KB * ORD;
    for (int v = 0; v < NV; v++) dg[v] = 0;
    for (int i = 0; i < ND; i++) {
        for (int x = 0; x < ORD; x++) {
            int a = dU[i] * ORD + x;
            int b = dV[i] * ORD + gmul(x, dG[i]);
            if (dg[a] >= DEGR || dg[b] >= DEGR || has_nb(a, b)) continue;
            adj[a][dg[a]++] = b;
            adj[b][dg[b]++] = a;
        }
    }
}

static long long eval_cost(void) {
    int W = (NV + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(cur, 0, sizeof(uint64_t) * (size_t)NV * (size_t)W);
    for (int v = 0; v < NV; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                uint64_t *t = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += NV - cnt;
    }
    return bad / 2;
}

static void randomize_all(void) {
    for (int s = 0; s < DEGR; s++) {
        int p[MAXK];
        for (int i = 0; i < KB; i++) p[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < KB; i++) {
            int j = s * KB + i;
            dU[j] = i;
            dV[j] = KB + p[i];
        }
    }
    for (int j = 0; j < ND; j++) dG[j] = rnd(ORD);
}

static void output_graph(void) {
    long long em = 0;
    for (int v = 0; v < NV; v++) em += dg[v];
    printf("%d %lld\n", NV, em / 2);
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < dg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    DEGR = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    KB = atoi(argv[4]);
    GM = atoi(argv[5]);
    GK = atoi(argv[6]);
    GR = atoi(argv[7]);
    double tl = atof(argv[8]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEGR < 1 || DEGR > MAXD || DIAM < 1 || KB < 1 || KB > MAXK ||
        GM < 2 || GK < 1 || GK > 63 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    ORD = GM * GK;
    if (2 * KB * ORD > MAXN) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % GM;
    for (int b = 1; b < GK; b++) pw[b] = (int)((long long)pw[b - 1] * GR % GM);
    ND = KB * DEGR;

    clock_t t0 = clock();
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < tl) {
        randomize_all();
        build_graph();
        long long cost = eval_cost();
        for (int it = 0; it < ITER && cost > 0; it++) {
            if ((it & 63) == 0 &&
                (double)(clock() - t0) / CLOCKS_PER_SEC >= tl) break;
            int j = rnd(ND);
            int old = dG[j];
            dG[j] = rnd(ORD);
            build_graph();
            long long c2 = eval_cost();
            if (c2 <= cost || rnd01() < 0.01) cost = c2;
            else dG[j] = old;
        }
        if (cost == 0) {
            build_graph();
            output_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _adj_of(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colour(n, adj):
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


def _balls(n, adj, r):
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


def _greedy_cover(cands, ball, full, d, rng, noisy):
    """Greedy cover of `full` by at most d candidates; noisy picks randomly among near-best."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        mx = max(gains, default=0)
        if mx <= 0:
            return None
        if noisy:
            idx = [i for i, g in enumerate(gains) if g >= mx - 1 and g > 0]
            i = rng.choice(idx)
        else:
            i = gains.index(mx)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _cover_grow(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within distance D-1 (keeps diameter <= D)."""
    edges = list(edges)
    adj = _adj_of(n, edges)
    color = _colour(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        grew = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            if not cands:
                continue
            ch = None
            for att in range(3):
                ch = _greedy_cover(cands, ball, full, d, rng, att > 0)
                if ch or time.monotonic() >= deadline:
                    break
            if ch:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                for s in ch:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                grew = True
                break
        if not grew:
            break
    return n, edges


def _twin_grow(n, edges, d, rng, deadline):
    """Add twins (same neighbourhood) while all neighbours have spare degree."""
    edges = list(edges)
    adj = _adj_of(n, edges)
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(len(adj[y]) >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            for y in nb:
                adj[y].append(v)
                edges.append((y, v))
            changed = True
    return n, edges


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertex pairs in random order (only shortens distances)."""
    edges = list(edges)
    adj = _adj_of(n, edges)
    color = _colour(n, adj)
    existing = set((min(u, v), max(u, v)) for u, v in edges)
    deg = [len(a) for a in adj]
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


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth, cover growth and saturation until nothing is added."""
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_e = _saturate(cur_n, cur_e, d, rng)
        cur_n, cur_e = _cover_grow(cur_n, cur_e, d, D, deadline, rng)
        cur_e = _saturate(cur_n, cur_e, d, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


def _group_opts(G, rng):
    """All (m, k, r) with G = m*k and Z_m x| Z_k given by r (r^k = 1 mod m, gcd(r, m) = 1)."""
    out = []
    for k2 in range(1, 13):
        if G % k2 or G // k2 < 2:
            continue
        m = G // k2
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        out += [(m, k2, r) for r in range(1, m)
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    return out


def _run_group(d, D, seed, K, m, k, r, budget):
    out = lib.run_c(C_GROUP, [d, D, seed, K, m, k, r, f"{budget:.2f}"],
                    timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def _group_phase(d, D, cur, rng, deadline, consider):
    """Search group lifts with K + K base vertices, for orders above the current best."""
    for K in (1, 2, 3):
        G = cur() // (2 * K) + 1
        fails = 0
        while fails < 2:
            if deadline - time.monotonic() < 2.0:
                return
            G = max(G, cur() // (2 * K) + 1)
            opts = _group_opts(G, rng)
            ok = False
            for _ in range(2):
                left = deadline - time.monotonic()
                if left < 2.0 or not opts:
                    break
                m, k, r = rng.choice(opts)
                try:
                    n, e = _run_group(d, D, rng.randrange(1 << 30), K, m, k, r,
                                      min(5.0, left - 1.0))
                except Exception:
                    continue
                if n > 0 and consider(n, e):
                    ok = True
                    break
            if ok:
                G += 1
                fails = 0
            else:
                fails += 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3, d - 1 a prime power -> Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    state = {"n": best[0]}

    def consider(n, e):
        nonlocal best
        if n > state["n"] and lib.is_valid(n, e, d, D):
            best = (n, e)
            state["n"] = n
            return True
        return False

    def cur():
        return state["n"]

    end = start + 0.80 * tl - 1.0

    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            n2, e2 = _pipeline(pn, pe, d, D, start + 0.5 * tl, rng)
            consider(n2, e2)
        return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            pn, pe = _pipeline(gq[0], gq[1], d, D, start + 0.3 * tl, rng)
            consider(pn, pe)
            # Bold change: non-cyclic group lifts searched in C, aimed above the best order.
            if d >= 5 and end - time.monotonic() > 3.0:
                _group_phase(d, D, cur, rng, end, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
