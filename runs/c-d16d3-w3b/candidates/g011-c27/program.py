import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int N, M, W, DEGMAX, DIST;
static int *off, *nb;
static u64 *rA, *rB;
static unsigned char *kept, *bestkept;
static int K, bestK;
static int *badv, *excv;
static u64 st;
static time_t t0;
static double budget;

static u64 rnd64(void) {
    st ^= st << 13;
    st ^= st >> 7;
    st ^= st << 17;
    return st;
}

static int rndint(int k) { return (int)(rnd64() % (u64)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return difftime(time(NULL), t0); }

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Cost of the kept induced subgraph: degree excess plus ordered pairs at distance > DIST.
   Zero means the kept set is a valid graph (degree <= DEGMAX, diameter <= DIST). */
static long long evaluate(void) {
    long long cost = 0;
    int v, i, s, w;
    for (v = 0; v < N; v++) {
        if (!kept[v]) { excv[v] = 0; badv[v] = 0; continue; }
        int dg = 0;
        for (i = off[v]; i < off[v + 1]; i++) if (kept[nb[i]]) dg++;
        excv[v] = dg > DEGMAX ? dg - DEGMAX : 0;
        cost += excv[v];
    }
    memset(rA, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (v = 0; v < N; v++)
        if (kept[v]) rA[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    u64 *cur = rA, *nxt = rB;
    for (s = 0; s < DIST; s++) {
        for (v = 0; v < N; v++) {
            if (!kept[v]) continue;
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src0 = cur + (size_t)v * W;
            memcpy(dst, src0, sizeof(u64) * (size_t)W);
            for (i = off[v]; i < off[v + 1]; i++) {
                int u = nb[i];
                if (!kept[u]) continue;
                const u64 *src = cur + (size_t)u * W;
                for (w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    for (v = 0; v < N; v++) {
        if (!kept[v]) continue;
        const u64 *row = cur + (size_t)v * W;
        int cnt = 0;
        for (w = 0; w < W; w++) cnt += popc64(row[w]);
        badv[v] = K - cnt;
        cost += badv[v];
    }
    return cost;
}

static int pick_removal(void) {
    int tries, v;
    if (rnd01() < 0.5) {
        for (tries = 0; tries < 60; tries++) {
            v = rndint(N);
            if (kept[v] && (badv[v] > 0 || excv[v] > 0)) return v;
        }
    }
    do { v = rndint(N); } while (!kept[v]);
    return v;
}

static int pick_addition(void) {
    int v;
    do { v = rndint(N); } while (kept[v]);
    return v;
}

static void reduce_to_valid(void) {
    long long c = evaluate();
    while (c > 0 && K > 0) {
        long long bs = -1;
        int bv = -1, v;
        for (v = 0; v < N; v++) {
            if (!kept[v]) continue;
            long long sc = (long long)badv[v] + 2LL * (long long)excv[v];
            sc = sc * 4096 + (long long)(rnd64() % 4096);
            if (sc > bs) { bs = sc; bv = v; }
        }
        kept[bv] = 0;
        K--;
        c = evaluate();
    }
}

int main(int argc, char **argv) {
    int i, v;
    if (argc < 5) return 1;
    DEGMAX = atoi(argv[1]);
    DIST = atoi(argv[2]);
    st = (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x12345678ULL;
    if (st == 0) st = 1;
    budget = atof(argv[4]);
    if (scanf("%d %d", &N, &M) != 2) { N = 0; M = 0; }
    if (N <= 0 || DIST < 1 || DEGMAX < 1) { printf("0 0\n"); return 0; }

    int *eu = malloc(sizeof(int) * (size_t)(M + 1));
    int *ev = malloc(sizeof(int) * (size_t)(M + 1));
    int ne = 0;
    for (i = 0; i < M; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= N || b >= N || a == b) continue;
        eu[ne] = a;
        ev[ne] = b;
        ne++;
    }
    off = calloc((size_t)N + 1, sizeof(int));
    for (i = 0; i < ne; i++) { off[eu[i] + 1]++; off[ev[i] + 1]++; }
    for (v = 0; v < N; v++) off[v + 1] += off[v];
    nb = malloc(sizeof(int) * (size_t)(2 * ne + 1));
    int *fp = malloc(sizeof(int) * (size_t)(N + 1));
    memcpy(fp, off, sizeof(int) * (size_t)(N + 1));
    for (i = 0; i < ne; i++) {
        nb[fp[eu[i]]++] = ev[i];
        nb[fp[ev[i]]++] = eu[i];
    }
    free(fp);

    W = (N + 63) / 64;
    rA = calloc((size_t)N * (size_t)W, sizeof(u64));
    rB = calloc((size_t)N * (size_t)W, sizeof(u64));
    kept = malloc((size_t)N);
    bestkept = malloc((size_t)N);
    badv = calloc((size_t)N, sizeof(int));
    excv = calloc((size_t)N, sizeof(int));
    memset(kept, 1, (size_t)N);
    K = N;
    t0 = time(NULL);

    reduce_to_valid();
    memcpy(bestkept, kept, (size_t)N);
    bestK = K;

    /* Grow the valid kept set one vertex at a time by annealing swaps. */
    while (bestK < N && elapsed() < budget) {
        memcpy(kept, bestkept, (size_t)N);
        K = bestK;

        int bestA = -1;
        long long bestc = 0;
        for (i = 0; i < 24; i++) {
            int a = pick_addition();
            kept[a] = 1;
            K++;
            long long c = evaluate();
            kept[a] = 0;
            K--;
            if (bestA < 0 || c < bestc) { bestc = c; bestA = a; }
        }
        kept[bestA] = 1;
        K++;
        long long cost = evaluate();
        int ok = (cost == 0);

        int iters = 3000;
        for (i = 0; i < iters && !ok && K < N; i++) {
            if ((i & 31) == 0 && elapsed() >= budget) break;
            double T = 3.0 * (1.0 - (double)i / iters) + 0.3;
            int r = pick_removal();
            int a = pick_addition();
            kept[r] = 0;
            kept[a] = 1;
            long long c2 = evaluate();
            long long delta = c2 - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = c2;
                if (cost == 0) ok = 1;
            } else {
                kept[a] = 0;
                kept[r] = 1;
            }
        }
        if (ok) {
            bestK = K;
            memcpy(bestkept, kept, (size_t)N);
        }
    }

    int *map = malloc(sizeof(int) * (size_t)(N + 1));
    int cnt = 0;
    for (v = 0; v < N; v++) map[v] = bestkept[v] ? cnt++ : -1;
    long long E = 0;
    for (v = 0; v < N; v++) {
        if (!bestkept[v]) continue;
        for (i = off[v]; i < off[v + 1]; i++) {
            int u = nb[i];
            if (bestkept[u] && u > v) E++;
        }
    }
    printf("%d %lld\n", cnt, E);
    for (v = 0; v < N; v++) {
        if (!bestkept[v]) continue;
        for (i = off[v]; i < off[v + 1]; i++) {
            int u = nb[i];
            if (bestkept[u] && u > v) printf("%d %d\n", map[v], map[u]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3). Safe baseline.
#
# Start from PG(2, q) incidence. Each old vertex has spare capacity s = d - q - 1.
# Pick an arc S with every line holding <= s points of S; add an A-vertex on the
# lines through each P in S and a B-vertex on the points of each line in S.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Build.
#
# Bold change: instead of voltage lifts and greedy fills, take the incidence
# graph of PG(2, q) with q the smallest prime power >= d (degree q+1 > d, so the
# vertices are over-full) and let the C engine search for the largest induced
# subgraph with max degree <= d and diameter <= D. Every induced subgraph of a
# bipartite graph is bipartite, so validity reduces to degree and distances.
# The arc-extended graph and K_{d,d} remain as fallbacks, and every candidate
# passes lib.is_valid before it can be returned.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Moore-optimal incidence graph when d - 1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Baseline: arc-extended projective plane graphs.
    deadline = t0 + 0.2 * time_limit
    for n_c, e_c in _arc_extensions(d, deadline, random.Random(seed * 7919 + d)):
        consider(n_c, e_c)

    # Bold search: induced subgraphs of PG(2, q), q = smallest prime power >= d.
    q = d
    while not lib.is_prime_power(q):
        q += 1
    if q <= 40:
        left = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
        if left >= 2.0:
            n0, e0 = lib.projective_plane_incidence(q)
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{left:.2f}"],
                                 stdin_graph=(n0, e0), timeout=left + 2.5)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
