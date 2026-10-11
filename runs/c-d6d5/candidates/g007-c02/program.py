"""Bi-Cayley (Haar-type) search for bipartite graphs of max degree d and diameter D.

Bold change: the voltage-lift annealer and the grow phase are replaced by a different
construction. The graph is the bi-Cayley graph over Z_m with connection set S of size d:
vertices a_i = i and b_j = m + j, with edge a_i ~ b_{i+s} for s in S. Every vertex has
degree exactly d, and the graph is bipartite by construction.

Why only two BFS runs decide the diameter: the translation x -> x + c maps a_i to a_{i+c}
and b_j to b_{j+c}, so it is an automorphism that is transitive on each side. Hence
  dist(a_i, a_k) = dist(a_0, a_{k-i}), dist(a_i, b_j) = dist(a_0, b_{j-i}),
  dist(b_i, b_k) = dist(b_0, b_{k-i}).
So the graph has diameter <= D exactly when BFS from a_0 and from b_0 reach all 2m
vertices within D steps. The C engine anneals S for a target m just above the current
best, using the count of unreached vertices as the cost.

Pipeline:
  1. Python: K_{d,d} fallback (valid for D >= 2), projective-plane / Araujo-Pardo-Lopez
     constructions for D = 3, and the W(q) generalized quadrangle for D >= 4.
  2. C: upward search over m. For each m, simulated annealing over S with restarts.
     Every accepted graph is re-emitted and printed as the best so far.
  3. Python re-validates the C output with lib.is_valid and keeps the larger valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define ITERS 30000
#define RESTARTS 3
#define MCAP_MAX 400000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int M;               /* cyclic group order; graph has 2M vertices */
static int S[MAXD];        /* connection set, DEG distinct residues */
static int bestS[MAXD];
static int bestM;
static int *stamp, *bufA, *bufB;
static int cur;
static int Mcap;

static long long moore_bound(void) {
    if (DIAM <= 0 || DEG <= 0) return 1;
    if (DEG == 1) return 2;
    if (DEG == 2) return 2LL * DIAM;
    long long s = 0, p = 1;
    for (int i = 0; i < DIAM; i++) {
        s += p;
        p *= (DEG - 1);
        if (s > 1000000000LL) break;
    }
    return 2 * s;
}

static int in_set(int v) {
    for (int e = 0; e < DEG; e++)
        if (S[e] == v) return 1;
    return 0;
}

static int in_prefix(int v, int upto) {
    for (int e = 0; e < upto; e++)
        if (S[e] == v) return 1;
    return 0;
}

/* Number of vertices within DIAM steps of the source (side 0 = a, side 1 = b). */
static int bfs_cover(int side, int src) {
    if (cur >= 2000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)(2 * Mcap + 2));
        cur = 0;
    }
    cur++;
    int *f = bufA, *h = bufB;
    int fsz = 0, cnt = 1;
    int sid = side ? M + src : src;
    stamp[sid] = cur;
    f[fsz++] = sid;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            int v = f[q];
            if (v < M) {
                for (int e = 0; e < DEG; e++) {
                    int id = M + (v + S[e]) % M;
                    if (stamp[id] != cur) {
                        stamp[id] = cur;
                        h[nsz++] = id;
                    }
                }
            } else {
                int j = v - M;
                for (int e = 0; e < DEG; e++) {
                    int id = (j - S[e] + M) % M;
                    if (stamp[id] != cur) {
                        stamp[id] = cur;
                        h[nsz++] = id;
                    }
                }
            }
        }
        cnt += nsz;
        int *t = f;
        f = h;
        h = t;
        fsz = nsz;
    }
    return cnt;
}

/* Zero iff the bi-Cayley graph for the current M, S has diameter <= DIAM. */
static long eval_cost(void) {
    long N2 = 2L * M;
    return (N2 - bfs_cover(0, 0)) + (N2 - bfs_cover(1, 0));
}

static int sa_run(int iters) {
    for (int e = 0; e < DEG; e++) {
        int v;
        do {
            v = rnd_int(M);
        } while (in_prefix(v, e));
        S[e] = v;
    }
    long c = eval_cost();
    for (int it = 0; it < iters && c > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double temp = 1.2 * (1.0 - (double)it / iters) + 0.02;
        int p = rnd_int(DEG);
        int nv = rnd_int(M);
        if (in_set(nv)) continue;
        int old = S[p];
        S[p] = nv;
        long c2 = eval_cost();
        if (c2 <= c || rnd_unit() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
        } else {
            S[p] = old;
        }
    }
    return c == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 2;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    long long mb = moore_bound();
    long long mc = mb / 2;
    if (mc > MCAP_MAX) mc = MCAP_MAX;
    if (mc < DEG) mc = DEG;
    Mcap = (int)mc;
    stamp = calloc((size_t)(2 * Mcap + 2), sizeof(int));
    bufA = malloc(sizeof(int) * (size_t)(2 * Mcap + 2));
    bufB = malloc(sizeof(int) * (size_t)(2 * Mcap + 2));
    cur = 0;

    /* K_{d,d} is the starting point: bi-Cayley with M = d and S = all residues. */
    bestM = DEG;
    for (int e = 0; e < DEG; e++) bestS[e] = e;

    while (elapsed() < DEADLINE && bestM + 1 <= Mcap) {
        int m = bestM + 1 + rnd_int(4);
        if (m > Mcap) m = Mcap;
        M = m;
        int ok = 0;
        for (int r = 0; r < RESTARTS && !ok && elapsed() < DEADLINE; r++)
            ok = sa_run(ITERS);
        if (ok) {
            bestM = m;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
        }
    }

    int m = bestM;
    printf("%d %d\n", 2 * m, m * DEG);
    for (int i = 0; i < m; i++)
        for (int e = 0; e < DEG; e++)
            printf("%d %d\n", i, m + (i + bestS[e]) % m);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: known constructions and fallbacks.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _known_start(d, D):
    """Best construction Python builds directly for D = 3, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (bi-Cayley with all residues), valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    # Known D = 3 constructions.
    known = _known_start(d, D)
    if known is not None and lib.is_valid(known[0], known[1], d, D) and known[0] > best[0]:
        best = known

    # D >= 4: generalized quadrangle baseline (cheap, guarded by time).
    if D >= 4 and time.monotonic() - t0 < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if best[0] >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=None, timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass   # keep the valid fallback

    return best
