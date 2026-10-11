import itertools
import math
import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline families (safe fallback, unchanged from the parent).
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
# NEW construction: multi-orbit voltage lifts over groups Z_m x| Z_k2 with a
# free d-regular bipartite base multigraph on K+K vertices (K <= 3).
#
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h.
# Darts x = 0..K*d-1: dart x leaves A-orbit ai[x] = x/d, enters B-orbit bi[x],
# with voltage vv[x]. Edges: A_{i,g} ~ B_{j, g*s}. B-degrees are kept exactly d
# by only swapping B-endpoints between darts.
#
# Left multiplication by any group element is an automorphism, and it is
# transitive on each orbit. So validity needs only 2K BFS runs, from the orbit
# representatives A_{i,0} and B_{j,0}.
#
# Cost = total unreached (representative, vertex) pairs + duplicate penalty.
# Search ramps the order upward from the start graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 16
#define MAXKK 3
#define MAXDARTS 64
#define PEN 1000LL
#define ITERS 30000

static int d_ = 1, D_ = 1, ND = 1, K_ = 1;
static double BUDGET = 10.0;
static clock_t T0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

/* group Z_m x| Z_k2, element (a,b) coded as a*GK+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM = 1, GK = 1, GG = 1;
static int pw[64];

static int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (int)((a + ((long long)pw[b] * c) % GM) % GM);
    int nb2 = (b + e) % GK;
    return na * GK + nb2;
}

static void set_group(int m, int k2, int r) {
    GM = m; GK = k2; GG = m * k2;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
}

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int pick_r(int m, int k2) {
    if (k2 == 1 || m <= 2 || rndint(2) == 0) return 1;
    for (int t = 0; t < 200; t++) {
        int r = 2 + rndint(m - 2);
        if (gcdi(r, m) == 1 && pmod(r, k2, m) == 1 % m) return r;
    }
    return 1;
}

static int ai[MAXDARTS], bi[MAXDARTS], vv[MAXDARTS];
static int sbi[MAXDARTS], svv[MAXDARTS];
static int capN = 0, stamp = 0;
static int *nb = NULL, *cnt = NULL, *vis = NULL, *queue = NULL;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(nb); free(cnt); free(vis); free(queue);
    capN = N + 64;
    nb = malloc(sizeof(int) * (size_t)capN * MAXDEG);
    cnt = calloc((size_t)capN, sizeof(int));
    vis = calloc((size_t)capN, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)capN);
    stamp = 0;
}

static void build_nb(void) {
    int K = K_, d = d_, G = GG, N = 2 * K * G;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int x = 0; x < ND; x++) {
        int i = ai[x], j = bi[x], s = vv[x];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gmul(g, s);
            nb[a * d + cnt[a]++] = b;
            nb[b * d + cnt[b]++] = a;
        }
    }
}

/* BFS to depth D_ from src; returns number of reached vertices (including src). */
static int bfs_from(int src) {
    int d = d_;
    if (stamp >= 2000000000) {
        memset(vis, 0, sizeof(int) * (size_t)capN);
        stamp = 0;
    }
    stamp++;
    int head = 0, tail = 0;
    queue[tail++] = src;
    vis[src] = stamp;
    for (int lev = 0; lev < D_ && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = queue[head++];
            for (int t = 0; t < d; t++) {
                int v = nb[u * d + t];
                if (vis[v] != stamp) {
                    vis[v] = stamp;
                    queue[tail++] = v;
                }
            }
        }
    }
    return tail;
}

static long long evalcost(void) {
    int K = K_, G = GG, N = 2 * K * G;
    long long dup = 0;
    for (int x = 0; x < ND; x++)
        for (int y = x + 1; y < ND; y++)
            if (ai[x] == ai[y] && bi[x] == bi[y] && vv[x] == vv[y]) dup++;
    build_nb();
    long long total = 0;
    for (int i = 0; i < K; i++) total += N - bfs_from(i * G);
    for (int j = 0; j < K; j++) total += N - bfs_from((K + j) * G);
    return total + PEN * dup;
}

static void init_state(void) {
    int d = d_, K = K_;
    ND = K * d;
    int bl[MAXDARTS];
    for (int x = 0; x < ND; x++) bl[x] = x % K;
    for (int x = ND - 1; x > 0; x--) {
        int j = rndint(x + 1);
        int t = bl[x]; bl[x] = bl[j]; bl[j] = t;
    }
    for (int x = 0; x < ND; x++) {
        ai[x] = x / d;
        bi[x] = bl[x];
        vv[x] = rndint(GG);
    }
}

static void mutate(void) {
    if (rnd01() < 0.5) {
        int x = rndint(ND);
        vv[x] = rndint(GG);
    } else {
        int x = rndint(ND), y = rndint(ND);
        int t = bi[x]; bi[x] = bi[y]; bi[y] = t;
    }
}

static int anneal(int iters) {
    init_state();
    long long cost = evalcost();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && elapsed() > BUDGET) return 0;
        memcpy(sbi, bi, sizeof bi);
        memcpy(svv, vv, sizeof vv);
        mutate();
        long long c2 = evalcost();
        double temp = 3.0 * (1.0 - (double)it / iters) + 0.1;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            memcpy(bi, sbi, sizeof bi);
            memcpy(vv, svv, sizeof vv);
        }
    }
    return cost == 0;
}

static int *bestE = NULL;
static int bestM = 0, bestNv = 0;

static void record(void) {
    int K = K_, G = GG, N = 2 * K * G;
    int m = ND * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)m);
    int c = 0;
    for (int x = 0; x < ND; x++) {
        for (int g = 0; g < G; g++) {
            E[2 * c] = ai[x] * G + g;
            E[2 * c + 1] = (K + bi[x]) * G + gmul(g, vv[x]);
            c++;
        }
    }
    free(bestE);
    bestE = E;
    bestM = m;
    bestNv = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    BUDGET = atof(argv[4]);
    int minN = (argc > 5) ? atoi(argv[5]) : 0;
    if (d_ < 1 || d_ > MAXDEG || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    T0 = clock();

    int bestN = minN;
    ensure_cap(64);

    while (elapsed() < BUDGET) {
        int K = 1 + rndint(MAXKK);
        int Gmin = bestN / (2 * K) + 1;
        int spread = Gmin / 25 + 2;
        int G = Gmin + rndint(spread);
        int cands[64], nc = 0;
        for (int k = 1; k <= 40 && k <= G; k++) {
            if (G % k == 0) cands[nc++] = k;
        }
        int k2 = cands[rndint(nc)];
        int m = G / k2;
        int r = pick_r(m, k2);
        set_group(m, k2, r);
        K_ = K;
        ND = K * d_;
        int N = 2 * K * G;
        ensure_cap(N);
        if (anneal(ITERS) && N > bestN) {
            bestN = N;
            record();
        }
    }

    if (bestE == NULL) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestNv, bestM);
    for (int c = 0; c < bestM; c++) {
        printf("%d %d\n", bestE[2 * c], bestE[2 * c + 1]);
    }
    return 0;
}
'''


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions first.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: multi-orbit voltage lifts over Z_m x| Z_k2, ramping upward
    # from the best exact order found so far.
    if D >= 3 and 3 <= d <= 12 and time_limit > 10:
        budget = max(1.0, min(0.8 * time_limit, time_limit - 9.0))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                            timeout=budget + 8.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
