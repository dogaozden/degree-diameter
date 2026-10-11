import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealing over semidirect groups Z_M x| Z_K2.
#
# The base is a d-regular bipartite multigraph on KB + KB vertices, given by d
# random perfect matchings (dart (i, t) goes from left i to right tgt[i*d+t]).
# Each dart carries a voltage in the group G = M*K2. The lift has 2*KB*G
# vertices. Its cost is the number of vertex pairs at distance > DIAM, computed
# with bitset ball propagation. Moves change one voltage or swap two darts'
# targets (both keep the base d-regular). The annealer stops at cost 0 and
# prints that lift. Otherwise it prints "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 8192
#define WMAX (MAXN / 64)
#define DEGMAX 40
#define MAXDART 512

static int D_DEG, DIAM, MOD, K2, RR, KB, GG, NV;
static int pw[64];
static int tgt[MAXDART];
static int volt[MAXDART];
static int adj[MAXN][DEGMAX];
static int dg[MAXN];
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static uint64_t rs = 1;

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

/* Semidirect product Z_MOD x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + R^b c, b + e). */
static int mulG(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)pw[b] * (long long)c) % MOD;
    return (int)(t * K2 + (b + e) % K2);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void build_graph(void) {
    for (int v = 0; v < NV; v++) dg[v] = 0;
    for (int i = 0; i < KB; i++) {
        for (int t = 0; t < D_DEG; t++) {
            int j = i * D_DEG + t;
            int rt = KB + tgt[j];
            for (int x = 0; x < GG; x++) {
                int a = i * GG + x;
                int b = rt * GG + mulG(x, volt[j]);
                if (dg[a] >= D_DEG || dg[b] >= D_DEG || has_edge(a, b)) continue;
                adj[a][dg[a]++] = b;
                adj[b][dg[b]++] = a;
            }
        }
    }
}

static long long eval_cost(void) {
    build_graph();
    int n = NV;
    int W = (n + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
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
    for (int v = 0; v < n; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += n - cnt;
    }
    return bad / 2;
}

static void print_graph(void) {
    long long em = 0;
    for (int v = 0; v < NV; v++) em += dg[v];
    printf("%d %lld\n", NV, em / 2);
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < dg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    D_DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    MOD = atoi(argv[5]);
    K2 = atoi(argv[6]);
    RR = atoi(argv[7]);
    KB = atoi(argv[8]);
    if (D_DEG < 1 || D_DEG > 32 || DIAM < 1 || tl <= 0 || MOD < 1 || K2 < 1 || K2 > 60 ||
        KB < 1 || KB > 8) {
        printf("0 0\n");
        return 0;
    }
    GG = MOD * K2;
    if (GG < 2) {
        printf("0 0\n");
        return 0;
    }
    NV = 2 * KB * GG;
    if (NV > MAXN) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % MOD;
    for (int b = 1; b < K2; b++) pw[b] = (int)(((long long)pw[b - 1] * RR) % MOD);

    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    int perm[8];
    for (int t = 0; t < D_DEG; t++) {
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmpv = perm[i];
            perm[i] = perm[j];
            perm[j] = tmpv;
        }
        for (int i = 0; i < KB; i++) tgt[i * D_DEG + t] = perm[i];
    }
    int ND = KB * D_DEG;
    for (int j = 0; j < ND; j++) volt[j] = rnd(GG);

    long long cur = eval_cost();
    if (cur == 0) {
        print_graph();
        return 0;
    }
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    while (1) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
        if (frac >= 1.0) break;
        double T = 3.0 * pow(0.05, frac) + 0.05;

        int type;
        int j1 = rnd(ND), j2 = 0, oldv = 0;
        if (ND < 2 || rnd01() < 0.5) {
            type = 0;
            oldv = volt[j1];
            int nvv = rnd(GG);
            while (nvv == oldv) nvv = rnd(GG);
            volt[j1] = nvv;
        } else {
            type = 1;
            j2 = rnd(ND);
            if (j2 == j1) continue;
            int tmpt = tgt[j1];
            tgt[j1] = tgt[j2];
            tgt[j2] = tmpt;
        }

        long long c2 = eval_cost();
        if (c2 == 0) {
            print_graph();
            return 0;
        }
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            if (type == 0) {
                volt[j1] = oldv;
            } else {
                int tmpt = tgt[j1];
                tgt[j1] = tgt[j2];
                tgt[j2] = tmpt;
            }
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
    """W(q) incidence graph for the largest prime power q <= min(d - 1, 9) (kept small for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (adds edges only)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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


def _group_params(G, rng):
    """Return (M, K2, R) with G = M*K2 describing Z_M x| Z_K2 (cyclic if no valid R is found)."""
    divs = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        for _ in range(40):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return G, 1, 1


def _run_lift(d, D, seed, budget, M, K2, R, kb):
    """Run the C lift annealer for `budget` seconds; return (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", M, K2, R, kb],
                    stdin_graph=None, timeout=budget + 6.0)
    n, edges = lib.parse_graph_text(out)
    if n == 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3 (non-calibration): incidence graph of PG(2, q), q the largest prime power <= d - 1.
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            pn, pe = lib.projective_plane_incidence(qs[0])
            consider(pn, pe)

    # D >= 4: generalized quadrangle incidence graph, saturated with spare degree.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Main phase: voltage lifts over semidirect groups, searched by the C annealer.
    # Each attempt targets a lift just larger than the current best.
    end = start + 0.88 * tl - 1.0
    state, miss = {}, {}
    while True:
        remaining = end - time.monotonic()
        if remaining < 2.5:
            break
        budget = min(max(2.0, remaining / 6.0), 8.0, remaining - 1.5)
        if budget < 1.0:
            break
        kb = rng.choice([1, 2, 3, 4, 5])
        floor = best_n // (2 * kb) + 1
        G = max(state.get(kb, 0), floor, 2)
        if 2 * kb * G > 8000:
            continue
        M, K2, R = _group_params(G, rng)
        try:
            res = _run_lift(d, D, rng.randrange(1, 1 << 30), budget, M, K2, R, kb)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])
            state[kb] = G + 1
            miss[kb] = 0
        else:
            miss[kb] = miss.get(kb, 0) + 1
            state[kb] = G
            if miss[kb] >= 3:
                state[kb] = floor
                miss[kb] = 0

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
