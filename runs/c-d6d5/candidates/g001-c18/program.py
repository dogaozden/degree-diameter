import itertools
import time

import lib


# Engine: C annealer over bi-Cayley lifts. The graph is 2k base vertices lifted
# over a semidirect product Z_m x| Z_k2 of order G. Each base vertex A_i has d darts,
# one per layer. Moves: change a voltage, or swap two targets within one layer
# (a joint rewiring move, which the parent lacks). Targets come from a per-k
# ratchet: the best G found so far for each k, plus a random step that grows with G.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 3
#define K2MAX 64

static uint64_t rs0 = 0x2545F4914F6CDD1DULL, rs1 = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) {
    uint64_t s1 = rs0;
    const uint64_t s0 = rs1;
    rs0 = s0;
    s1 ^= s1 << 23;
    rs1 = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs1 + s0;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, G_, M_, K2_;
static long PW_[K2MAX];
static int *dI, *dJ, *dS;          /* darts, length d*K_ */
static int *adj, *cnt, *vis, *que; /* adjacency (N*d), counts, BFS */
static int capN = 0;
static int vstamp = 0;
static int *bE = NULL;
static long bEc = 0;
static int bNv = 0;
static int bestFound = 0;
static long bestN_ = 0;
static int curG[KMAX + 1];

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* Semidirect product Z_M x| Z_K2 with action r: (a,b)*(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    const int a = x / K2_, b = x % K2_, c = y / K2_, e = y % K2_;
    const long t = ((long)a + PW_[b] * (long)c) % M_;
    return (int)(t * K2_ + (b + e) % K2_);
}

static void ensure_capacity(int N) {
    if (N <= capN) return;
    free(adj); free(cnt); free(vis); free(que);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * d_);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
}

/* Penalty: unreached (representative, vertex) pairs within distance D, plus
   a heavy penalty per duplicate dart (same i, j and voltage). Zero means valid. */
static long eval_cost(void) {
    const int k = K_, G = G_, d = d_, D = D_;
    const int N = 2 * k * G;
    const int nd = d * k;
    long dup = 0;
    for (int t = 0; t < nd; t++)
        for (int u = 0; u < t; u++)
            if (dI[u] == dI[t] && dJ[u] == dJ[t] && dS[u] == dS[t]) dup++;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < nd; t++) {
        const int i = dI[t], j = dJ[t], s = dS[t];
        for (int g = 0; g < G; g++) {
            const int a = i * G + g;
            const int b = (k + j) * G + gmul(g, s);
            adj[a * d + cnt[a]++] = b;
            adj[b * d + cnt[b]++] = a;
        }
    }
    /* Vertex-transitive within each class, so one BFS per class representative suffices. */
    long total = 0;
    for (int r = 0; r < 2 * k; r++) {
        const int src = r * G;
        vstamp++;
        int head = 0, tail = 0;
        que[tail++] = src;
        vis[src] = vstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            const int end = tail;
            while (head < end) {
                const int u = que[head++];
                for (int e = 0; e < d; e++) {
                    const int v = adj[u * d + e];
                    if (vis[v] != vstamp) { vis[v] = vstamp; que[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total + dup * (long)N;
}

static int setup_group(int G) {
    int divs[K2MAX + 1], nd = 0;
    for (int x = 1; x <= K2MAX && x <= G / 2; x++)
        if (G % x == 0) divs[nd++] = x;
    if (nd == 0) return 0;
    for (int tries = 0; tries < 200; tries++) {
        int k2 = 1;
        if (nd > 1 && rndint(10) < 7) k2 = divs[1 + rndint(nd - 1)];
        const int m = G / k2;
        if (k2 == 1) { M_ = G; K2_ = 1; PW_[0] = 1; return 1; }
        for (int a = 0; a < 100; a++) {
            const int r = 1 + rndint(m - 1);
            if (gcd_i(r, m) != 1) continue;
            long p = 1 % m, q = 1 % m;
            for (int b = 0; b < k2; b++) p = p * r % m;
            if (p != 1 % m) continue;
            M_ = m; K2_ = k2;
            for (int b = 0; b < k2; b++) { PW_[b] = q; q = q * r % m; }
            return 1;
        }
    }
    M_ = G; K2_ = 1; PW_[0] = 1;
    return 1;
}

static void random_darts(void) {
    const int k = K_, d = d_;
    int perm[KMAX];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            const int r = rndint(i + 1);
            const int tmp = perm[i]; perm[i] = perm[r]; perm[r] = tmp;
        }
        for (int i = 0; i < k; i++) {
            const int t = l * k + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(G_);
        }
    }
}

static long anneal(int iters, double T0, clock_t dl) {
    const int k = K_, d = d_, nd = d_ * K_;
    long cost = eval_cost();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 63) == 0 && clock() > dl) break;
        const double T = T0 * (1.0 - (double)it / iters) + 0.02;
        if (k >= 2 && rnd01() < 0.25) {
            const int l = rndint(d);
            const int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            const int t1 = l * k + i1, t2 = l * k + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            const long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            const int t = rndint(nd);
            const int old = dS[t];
            dS[t] = rndint(G_);
            const long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
            else dS[t] = old;
        }
    }
    return cost;
}

static void record(void) {
    const int k = K_, G = G_, d = d_;
    const long m = (long)d * k * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)m);
    long c = 0;
    for (int t = 0; t < d * k; t++) {
        const int i = dI[t], j = dJ[t], s = dS[t];
        for (int g = 0; g < G; g++) {
            E[2 * c] = i * G + g;
            E[2 * c + 1] = (k + j) * G + gmul(g, s);
            c++;
        }
    }
    free(bE);
    bE = E;
    bEc = m;
    bNv = 2 * k * G;
    bestFound = 1;
    bestN_ = bNv;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed seconds [start_n]\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    const uint64_t seed = strtoull(argv[3], NULL, 10);
    const double budget = atof(argv[4]);
    const long start_n = argc > 5 ? atol(argv[5]) : 0;
    if (d_ < 3 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    rs0 ^= seed * 0x9E3779B97F4A7C15ULL + 1;
    rs1 ^= (seed + 7) * 0xBF58476D1CE4E5B9ULL;
    for (int i = 0; i < 20; i++) rnd64();

    bestN_ = start_n;
    dI = malloc(sizeof(int) * (size_t)d_ * KMAX);
    dJ = malloc(sizeof(int) * (size_t)d_ * KMAX);
    dS = malloc(sizeof(int) * (size_t)d_ * KMAX);
    for (int k = 1; k <= KMAX; k++) {
        long c = start_n / (2L * k);
        if (c < 1) c = 1;
        curG[k] = (int)c;
    }

    const clock_t t0 = clock();
    const clock_t deadline = t0 + (clock_t)(budget * (double)CLOCKS_PER_SEC);
    const int ITERS = 4000;
    while (clock() < deadline) {
        const int k = 1 + rndint(KMAX);
        int G = curG[k] + 1 + rndint(1 + curG[k] / 32);
        if (G < 2) G = 2;
        K_ = k;
        G_ = G;
        if (!setup_group(G)) continue;
        ensure_capacity(2 * k * G);
        random_darts();
        const long c = anneal(ITERS, 2.5, deadline);
        if (c == 0) {
            if (2L * k * G > bestN_) record();
            if (G > curG[k]) curG[k] = G;
        }
    }

    if (!bestFound) {
        printf("0 0\n");
    } else {
        printf("%d %ld\n", bNv, bEc);
        for (long e = 0; e < bEc; e++) printf("%d %d\n", bE[2 * e], bE[2 * e + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Main driver: baselines first, then the C ratchet search starting above them.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and best_n == lib.moore_bound(d, 3):
                return best  # projective plane meets the Moore bound: optimal

    if D >= 4 and left() > 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and best_n == lib.moore_bound(d, 4):
                return best

    if d >= 3 and left() > 5.0:
        budget = max(1.0, 0.8 * left() - 1.0)
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, int(seed) & 0xFFFFFFFF, f"{budget:.2f}", best_n],
                            timeout=left() * 0.92)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
