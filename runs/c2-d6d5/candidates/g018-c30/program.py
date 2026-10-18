import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXH 1200
#define MAXN (2 * MAXH)
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXH * MAXD)
#define TEMP 0.4

/* Unstructured bipartite search. The graph is d-regular with sides A (indices 0..H-1)
   and B (indices 0..H-1, labels H..2H-1). Moves are double-edge switches, which keep
   the graph d-regular and bipartite. Cost = number of unordered pairs at distance > D.
   Once cost is 0, the graph grows by one A vertex and one B vertex, using edge splits. */

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, H_, E_;
static int ea[MAXE], eb[MAXE];
static unsigned char M[MAXH * MAXH];
static int nbv[MAXN * MAXD];
static int degc[MAXN];
static u64 RA[MAXN * MAXW], RB[MAXN * MAXW];
static u64 *RC = RA, *RN = RB;
static int missv[MAXN];
static int bestH = 0, bestE = 0;
static int bA[MAXE], bB[MAXE];

static long long evalcost(void) {
    int h = H_, d = d_, D = D_, N = 2 * h, W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) degc[v] = 0;
    for (int e = 0; e < E_; e++) {
        int a = ea[e], b = h + eb[e];
        if (degc[a] < d) nbv[a * d + degc[a]++] = b;
        if (degc[b] < d) nbv[b * d + degc[b]++] = a;
    }
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) RC[v * W + w] = 0;
        RC[v * W + (v >> 6)] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = RN + v * W;
            memcpy(dst, RC + v * W, sizeof(u64) * (size_t)W);
            for (int k = 0; k < d; k++) {
                int u = nbv[v * d + k];
                const u64 *src = RC + u * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        u64 *sw = RC; RC = RN; RN = sw;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(RC[v * W + w]);
        missv[v] = N - c;
        total += N - c;
    }
    return total / 2;
}

/* Double-edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Applying it again to the same
   pair of edge ids undoes it. Returns 0 (no change) if it would create a loop or duplicate. */
static int do_switch(int e1, int e2) {
    if (e1 == e2) return 0;
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (M[a1 * MAXH + b2] || M[a2 * MAXH + b1]) return 0;
    M[a1 * MAXH + b1] = 0; M[a2 * MAXH + b2] = 0;
    M[a1 * MAXH + b2] = 1; M[a2 * MAXH + b1] = 1;
    eb[e1] = b2; eb[e2] = b1;
    return 1;
}

static int incident(int v, int *out) {
    int h = H_, n = 0;
    for (int e = 0; e < E_ && n < MAXD; e++) {
        if (v < h) { if (ea[e] == v) out[n++] = e; }
        else if (eb[e] == v - h) out[n++] = e;
    }
    return n;
}

static int anneal(double dl) {
    long long cost = evalcost();
    long long it = 0;
    int inc1[MAXD], inc2[MAXD];
    while (cost > 0) {
        if ((it & 15) == 0 && now() > dl) break;
        it++;
        int N = 2 * H_, W = (N + 63) >> 6;
        int e1 = -1, e2 = -1;
        if (rndu() < 0.5) {
            /* Targeted move: bring an unreached vertex w closer to a deficient vertex v. */
            int v = -1, off = rndi(N);
            for (int q = 0; q < N; q++) {
                int x = (off + q) % N;
                if (missv[x] > 0) { v = x; break; }
            }
            int w = -1;
            if (v >= 0) {
                int off2 = rndi(N);
                for (int q = 0; q < N; q++) {
                    int x = (off2 + q) % N;
                    if (x != v && !((RC[v * W + (x >> 6)] >> (x & 63)) & 1ULL)) { w = x; break; }
                }
            }
            if (v >= 0 && w >= 0) {
                int n1 = incident(v, inc1), n2 = incident(w, inc2);
                if (n1 > 0 && n2 > 0) { e1 = inc1[rndi(n1)]; e2 = inc2[rndi(n2)]; }
            }
        }
        if (e1 < 0) { e1 = rndi(E_); e2 = rndi(E_); }
        if (!do_switch(e1, e2)) continue;
        long long c2 = evalcost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / TEMP)) {
            cost = c2;
        } else {
            do_switch(e1, e2);
        }
    }
    return cost == 0;
}

/* Add one A vertex and one B vertex, each with degree d, by splitting d random old edges.
   Edge (x,y) becomes (x,b) and gains (a,y), so x and y keep their degrees. */
static int grow(void) {
    int a = H_, b = H_;
    if (a + 1 >= MAXH) return 0;
    H_ = a + 1;
    for (int s = 0; s < d_; s++) {
        int done = 0;
        for (int tries = 0; tries < 200000 && !done; tries++) {
            int e = rndi(E_);
            int x = ea[e], y = eb[e];
            if (x == a || y == b) continue;
            if (M[a * MAXH + y] || M[x * MAXH + b]) continue;
            M[x * MAXH + y] = 0;
            M[x * MAXH + b] = 1; eb[e] = b;
            M[a * MAXH + y] = 1;
            ea[E_] = a; eb[E_] = y; E_++;
            done = 1;
        }
        if (!done) return 0;
    }
    return 1;
}

static void save_best(void) {
    bestH = H_;
    bestE = E_;
    memcpy(bA, ea, sizeof(int) * (size_t)E_);
    memcpy(bB, eb, sizeof(int) * (size_t)E_);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int h0 = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 2 || h0 < d_ || h0 + 2 >= MAXH) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    H_ = h0; E_ = 0;
    for (int i = 0; i < h0; i++)
        for (int s = 0; s < d_; s++) {
            int j = (i + s) % h0;
            M[i * MAXH + j] = 1;
            ea[E_] = i; eb[E_] = j; E_++;
        }
    for (int t = 0; t < 20 * E_; t++) do_switch(rndi(E_), rndi(E_));

    while (now() < tend) {
        double rem = tend - now();
        double dl = now() + fmax(1.0, 0.25 * rem);
        if (dl > tend) dl = tend;
        if (!anneal(dl)) break;
        if (H_ > bestH) save_best();
        if (!grow()) break;
    }

    if (bestH == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestH, bestE);
    for (int e = 0; e < bestE; e++) printf("%d %d\n", bA[e], bestH + bB[e]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    # Unstructured search: start from a smaller random-like regular bipartite graph,
    # then alternate annealing (bad-pair cost) and vertex growth.
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    elapsed = time.monotonic() - start
    budget = max(0.5, min(budget, time_limit - elapsed - 4.0))

    moore = lib.moore_bound(d, D)
    h0 = max(d + 1, min(200, moore // 8))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), h0],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
