import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: voltage lifts over semidirect products Z_M x| Z_K2.
#
# A base bipartite graph has K vertices per side and is d-regular: d perfect
# matchings perm[j] between the sides, each dart (j, i) carrying a voltage g in
# G = M*K2. The lift has 2*K*G vertices: A(i,x) ~ B(perm[j][i], x*g). Left
# multiplication by a group element is an automorphism, so the diameter test
# needs only BFS from the 2K orbit representatives. The C annealer changes
# voltages to reach diameter <= D, then verifies the full graph before printing.
# Python keeps the verified Generalized Quadrangle W(q) start as a fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXK 8
#define MAXD 32

static int DEGD, DIAM, K, M, K2, R, G, NV;
static int perm[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int adj[MAXN][MAXD];
static int deg[MAXN];
static long long pw[64];
static int stampA[MAXN], distA[MAXN], qb[MAXN];
static int stampc = 0;
static uint64_t rs = 1;

static uint64_t nxr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(nxr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nxr() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* Semidirect product Z_M x| Z_K2: (a,b)*(c,e) = (a + R^b c, b + e). */
static int mulg(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long t = (pw[b] * (long long)c) % M;
    int aa = (int)((a + t) % M);
    return aa * K2 + (b + e) % K2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void build_graph(void) {
    NV = 2 * K * G;
    for (int v = 0; v < NV; v++) deg[v] = 0;
    for (int j = 0; j < DEGD; j++)
        for (int i = 0; i < K; i++) {
            int p = perm[j][i];
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                int b = (K + p) * G + mulg(x, volt[j][i]);
                if (has_edge(a, b)) continue;
                adj[a][deg[a]++] = b;
                adj[b][deg[b]++] = a;
            }
        }
}

/* Number of vertices not within DIAM of s. */
static int bfs_bad(int s) {
    stampc++;
    int qh = 0, qt = 0;
    qb[qt++] = s;
    stampA[s] = stampc;
    distA[s] = 0;
    while (qh < qt) {
        int u = qb[qh++];
        if (distA[u] >= DIAM) continue;
        for (int i = 0; i < deg[u]; i++) {
            int w = adj[u][i];
            if (stampA[w] != stampc) {
                stampA[w] = stampc;
                distA[w] = distA[u] + 1;
                qb[qt++] = w;
            }
        }
    }
    return NV - qt;
}

static long long cost_reps(void) {
    long long s = 0;
    for (int i = 0; i < K; i++) s += bfs_bad(i * G);
    for (int p = 0; p < K; p++) s += bfs_bad((K + p) * G);
    return s;
}

static int full_ok(void) {
    for (int v = 0; v < NV; v++)
        if (bfs_bad(v) != 0) return 0;
    return 1;
}

static void init_random(void) {
    for (int j = 0; j < DEGD; j++) {
        for (int i = 0; i < K; i++) perm[j][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int t = rndi(i + 1);
            int tmp = perm[j][i];
            perm[j][i] = perm[j][t];
            perm[j][t] = tmp;
        }
        for (int i = 0; i < K; i++) volt[j][i] = rndi(G);
    }
}

static void output_graph(void) {
    long long em = 0;
    for (int v = 0; v < NV; v++) em += deg[v];
    printf("%d %lld\n", NV, em / 2);
    for (int v = 0; v < NV; v++)
        for (int i = 0; i < deg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEGD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (DEGD < 1 || DEGD > MAXD || DIAM < 1 || K < 1 || K > MAXK ||
        M < 2 || K2 < 1 || K2 > 64 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (2 * K * G > MAXN) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * (long long)(R % M)) % M;

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nxr();

    double t0 = now_s();
    long stallLim = 4000;
    long stall = 0;
    init_random();
    build_graph();
    long long cur = cost_reps();
    long long bestc = cur;

    while (1) {
        double frac = (now_s() - t0) / tl;
        if (frac >= 1.0) break;

        if (cur == 0) {
            if (full_ok()) {
                output_graph();
                return 0;
            }
        }

        if (stall > stallLim) {
            init_random();
            build_graph();
            cur = cost_reps();
            bestc = cur;
            stall = 0;
            continue;
        }

        int j = rndi(DEGD);
        int i = rndi(K);
        int old = volt[j][i];
        int nvl = rndi(G);
        if (nvl == old) continue;

        volt[j][i] = nvl;
        build_graph();
        long long c2 = cost_reps();
        double T = (double)G * (0.02 + 0.15 * (1.0 - frac));
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                stall = 0;
            } else {
                stall++;
            }
        } else {
            volt[j][i] = old;
            build_graph();
            stall++;
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (keeps diameter)."""
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


def _groups_of_order(G, rng):
    """List of (M, K2, R) with M * K2 = G giving Z_M x| Z_K2 (R^K2 = 1 mod M)."""
    out = []
    for K2 in range(1, 13):
        if G % K2:
            continue
        M = G // K2
        if M < 2:
            continue
        if K2 == 1:
            out.append((M, 1, 1))
            continue
        rs = [r for r in range(1, M)
              if math.gcd(r, M) == 1 and pow(r, K2, M) == 1 % M]
        if rs:
            out.append((M, K2, rng.choice(rs)))
    return out


def _lift_c(d, D, seed, k, M, K2, R, budget):
    """Run the C voltage annealer for `budget` seconds; return parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", k, M, K2, R],
                    timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    end = start + 0.9 * tl - 1.0
    rng = random.Random(seed)

    if d >= 1 and D == 1:
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

    # Generalized quadrangle start (diameter 4), saturated with spare degree.
    if D >= 4 and d >= 3:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Lift search: each success raises the target order for the next attempt.
    if d <= 30:
        ks = [1, 2, 3, 4, 5, 6]
        while True:
            remaining = end - time.monotonic()
            if remaining < 2.0:
                break
            cand_k = [k for k in ks
                      if 2 * k * max(2, best_n // (2 * k) + 1) <= 4000]
            if not cand_k:
                break
            k = rng.choice(cand_k)
            G = max(2, best_n // (2 * k) + 1)
            groups = _groups_of_order(G, rng)
            if not groups:
                continue
            M, K2, R = rng.choice(groups)
            slice_t = min(remaining, max(2.5, min(10.0, 0.25 * remaining)))
            try:
                n2, e2 = _lift_c(d, D, rng.randrange(1 << 30), k, M, K2, R, slice_t)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
