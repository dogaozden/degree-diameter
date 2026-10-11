import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of small bipartite base
# graphs with a semidirect-product group Z_M x| Z_K2.
#
# Lifted graph: vertices A(i,x) and B(j,y), i,j in [0,K), x,y in the group of
# order N = M*K2. The base graph is d-regular bipartite, given by d perfect
# matchings ta[t][i] (B index) with voltages vg[t][i]. The lift joins
# A(i,x) to B(ta[t][i], x*vg[t][i]).
#
# The group acts on each side by left multiplication, so the lift has diameter
# <= D iff every representative A(i,1) and B(j,1) reaches all vertices within D
# steps. The cost is the number of unreached (representative, vertex) pairs,
# plus a penalty for parallel lifted edges. Moves: change one voltage, or swap
# two targets inside one matching (both keep the graph simple and d-regular).
# Cost 0 gives a valid graph, which is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 16
#define MAXD 16
#define MAXV 4400
#define STALL 4000

static int d, D, K, M, K2, R, N, V;
static int *mulT;
static int ta[MAXD][MAXK];
static int vg[MAXD][MAXK];
static int adj[MAXV * MAXD];
static int dist_[MAXV], stampA[MAXV], qb[MAXV];
static int curStamp = 0;
static uint64_t rs = 1;
static int mvType, mvJ, mvI, mvA, mvB, mvOld;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nxt() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0);
}

static int mul(int x, int y) { return mulT[(size_t)x * N + y]; }

static void build_group(void) {
    N = M * K2;
    mulT = (int *)malloc(sizeof(int) * (size_t)N * (size_t)N);
    int *pw = (int *)malloc(sizeof(int) * (size_t)K2);
    long long p = 1 % M;
    for (int b = 0; b < K2; b++) {
        pw[b] = (int)p;
        p = (p * R) % M;
    }
    for (int x = 0; x < N; x++) {
        int a = x / K2, b = x % K2;
        for (int y = 0; y < N; y++) {
            int c = y / K2, e = y % K2;
            int ra = (int)(((long long)a + (long long)pw[b] * c) % M);
            int rb = (b + e) % K2;
            mulT[(size_t)x * N + y] = ra * K2 + rb;
        }
    }
    free(pw);
}

static void random_init(void) {
    for (int j = 0; j < d; j++) {
        for (int i = 0; i < K; i++) ta[j][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int k = rnd(i + 1);
            int t = ta[j][i];
            ta[j][i] = ta[j][k];
            ta[j][k] = t;
        }
        for (int i = 0; i < K; i++) vg[j][i] = rnd(N);
    }
}

static long long eval_cost(void) {
    long long pen = 0;
    for (int i = 0; i < K; i++) {
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            for (int j = 0; j < d; j++) {
                int b = ta[j][i];
                int v = K * N + b * N + mul(x, vg[j][i]);
                adj[u * d + j] = v;
                adj[v * d + j] = u;
            }
        }
    }
    for (int i = 0; i < K; i++)
        for (int j1 = 0; j1 < d; j1++)
            for (int j2 = j1 + 1; j2 < d; j2++)
                if (ta[j1][i] == ta[j2][i] && vg[j1][i] == vg[j2][i]) pen += 1000;

    long long cost = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = (r < K) ? r * N : K * N + (r - K) * N;
        curStamp++;
        int h = 0, t = 0;
        qb[t++] = src;
        stampA[src] = curStamp;
        dist_[src] = 0;
        while (h < t) {
            int u = qb[h++];
            if (dist_[u] >= D) continue;
            for (int s = 0; s < d; s++) {
                int w = adj[u * d + s];
                if (stampA[w] != curStamp) {
                    stampA[w] = curStamp;
                    dist_[w] = dist_[u] + 1;
                    qb[t++] = w;
                }
            }
        }
        cost += V - t;
    }
    return cost + pen;
}

static void apply_move(void) {
    mvJ = rnd(d);
    if (K > 1 && rnd(2) == 1) {
        mvType = 1;
        mvA = rnd(K);
        mvB = rnd(K - 1);
        if (mvB >= mvA) mvB++;
        int t = ta[mvJ][mvA];
        ta[mvJ][mvA] = ta[mvJ][mvB];
        ta[mvJ][mvB] = t;
    } else {
        mvType = 0;
        mvI = rnd(K);
        mvOld = vg[mvJ][mvI];
        vg[mvJ][mvI] = rnd(N);
    }
}

static void undo_move(void) {
    if (mvType == 1) {
        int t = ta[mvJ][mvA];
        ta[mvJ][mvA] = ta[mvJ][mvB];
        ta[mvJ][mvB] = t;
    } else {
        vg[mvJ][mvI] = mvOld;
    }
}

static void print_graph(void) {
    long long E = (long long)K * N * d;
    printf("%d %lld\n", V, E);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < N; x++) {
            int u = i * N + x;
            for (int j = 0; j < d; j++) printf("%d %d\n", u, adj[u * d + j]);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double tl = atof(argv[8]);
    if (d < 1 || d > MAXD || K < 1 || K > MAXK || M < 1 || K2 < 1 || R < 0 || D < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    if ((long long)2 * K * M * K2 > MAXV) {
        printf("0 0\n");
        return 0;
    }
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nxt();
    build_group();
    V = 2 * K * N;

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    int done = 0;
    long long cur = 0;
    while (!done) {
        random_init();
        cur = eval_cost();
        long long runBest = cur;
        long stall = 0;
        while (1) {
            if (cur == 0) {
                done = 1;
                break;
            }
            double el = (double)clock() / CLOCKS_PER_SEC - t0;
            if (el >= tl) {
                done = 1;
                break;
            }
            double T = 1.5 * (1.0 - el / tl) + 0.15;
            apply_move();
            long long c2 = eval_cost();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else undo_move();
            if (cur < runBest) {
                runBest = cur;
                stall = 0;
            } else if (++stall > STALL) {
                break;
            }
        }
    }

    if (cur == 0) {
        eval_cost();
        print_graph();
    } else {
        printf("0 0\n");
    }
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _saturate(n, edges, d, rng):
    """Return an edge list with extra opposite-side edges added between deficient vertices.

    Adding edges keeps bipartiteness, degree <= d and diameter <= D.
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


def _group_options(N, rng, cap):
    """Random semidirect-product parameters (M, K2, R) with M * K2 = N and small K2."""
    opts = []
    for k2 in range(1, min(N, 16) + 1):
        if N % k2:
            continue
        m = N // k2
        if m == 1:
            opts.append((1, k2, 0))
            continue
        cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1]
        for r in rng.sample(cands, min(2, len(cands))):
            opts.append((m, k2, r))
    rng.shuffle(opts)
    return opts[:cap]


def _try_lift(d, D, K, m, k2, r, seed, budget):
    """Run the C lift annealer once; return (n, edges) if a valid lift was found, else None."""
    out = lib.run_c(C_SOURCE, [d, D, K, m, k2, r, seed, f"{budget:.2f}"],
                    stdin_graph=None, timeout=budget + 5.0)
    n, e = lib.parse_graph_text(out)
    if n <= 0 or not e:
        return None
    return n, e


def _lift_search(d, D, start_n, deadline, rng, consider):
    """Try lift sizes V = 2 K N in ascending order, a few group/base configurations each."""
    moore = lib.moore_bound(d, D)
    V = start_n + (start_n % 2)
    while V <= moore and time.monotonic() < deadline - 0.5:
        half = V // 2
        combos = []
        for k in range(1, 9):
            if half % k == 0 and half // k >= 2:
                N = half // k
                for (m, k2, r) in _group_options(N, rng, 2):
                    combos.append((k, m, k2, r))
        rng.shuffle(combos)
        for (k, m, k2, r) in combos[:2]:
            budget = min(1.2, deadline - time.monotonic())
            if budget < 0.3:
                break
            res = _try_lift(d, D, k, m, k2, r, rng.randrange(1 << 30), budget)
            if res is not None:
                consider(res[0], res[1])
                break
        V += 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3 (non-calibration): projective plane for the largest prime power q < d - 1, saturated.
    if D == 3 and d >= 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            n1, e1 = lib.projective_plane_incidence(qs[0])
            consider(n1, e1)
            consider(n1, _saturate(n1, e1, d, rng))

    # D >= 4: generalized quadrangle W(q), saturated with spare degree (safe baseline).
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate(gq[0], gq[1], d, rng))

    # Main search for D >= 4: C annealing over voltage lifts with non-cyclic groups.
    if D >= 4 and d >= 4:
        deadline = start + 0.85 * tl - 2.0
        moore = lib.moore_bound(d, D)
        start_n = max(best_n + 2, int(0.77 * moore))
        try:
            _lift_search(d, D, start_n, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
