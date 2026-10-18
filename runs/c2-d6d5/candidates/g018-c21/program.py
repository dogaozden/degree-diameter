"""Bold variant: unstructured simulated annealing over d-regular bipartite graphs.

Instead of searching over voltage lifts of groups, this keeps a simple d-regular
bipartite graph on 2h vertices and anneals it with degree-preserving edge switches,
using the number of vertex pairs at distance > D as the cost. Whenever the cost
reaches 0, the side size h grows by one (two new vertices, each with degree d), and
the search continues. Every accepted state is simple, bipartite, and d-regular, so
the output is valid whenever cost 0 was reached. The fallback K_{d,d} and the
projective-plane incidence graph are kept, so every case still returns a valid graph.

Risk: this does not use the lift structure behind the 684 record for d=6, D=5, so it
may return fewer vertices than the parent did on that target.
"""
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

#define MAXD 64

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

static int d_, D_, h_;          /* degree, diameter, side size */
static int *adj = NULL;         /* 2h*d: A ids 0..h-1 hold B ids h..2h-1, and vice versa */
static u64 *cur = NULL, *nxt = NULL;
static size_t capW = 0;
static int *bestE = NULL;
static int bestH = 0;
static long long evals = 0;

static int findrow(int v, int u) {
    const int *r = adj + (size_t)v * d_;
    for (int k = 0; k < d_; k++) if (r[k] == u) return k;
    return -1;
}

/* Edge (a1,b1) at slot i of a1 and (a2,b2) at slot j of a2 become (a1,b2) and (a2,b1).
   Applying the same call twice restores the original graph. */
static void do_switch(int a1, int i, int a2, int j) {
    int d = d_;
    int b1 = adj[a1 * d + i], b2 = adj[a2 * d + j];
    adj[a1 * d + i] = b2;
    adj[a2 * d + j] = b1;
    int p = findrow(b1, a1); adj[b1 * d + p] = a2;
    int q = findrow(b2, a2); adj[b2 * d + q] = a1;
}

static void ensure_buffers(void) {
    int N = 2 * h_;
    size_t W = (size_t)(N + 63) / 64;
    size_t need = (size_t)N * W;
    if (need > capW) {
        free(cur); free(nxt);
        cur = malloc(sizeof(u64) * need);
        nxt = malloc(sizeof(u64) * need);
        capW = need;
    }
}

/* Cost = number of unordered vertex pairs at distance > D_. */
static long long eval_cost(void) {
    int d = d_, N = 2 * h_;
    int W = (N + 63) / 64;
    evals++;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            const int *r = adj + (size_t)v * d;
            for (int k = 0; k < d; k++) {
                const u64 *s2 = cur + (size_t)r[k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const u64 *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += popc(s[w]);
        unr += N - pc;
    }
    return unr / 2;
}

/* Build adj from h_-side edge pairs (pa[p] in A, pb[p] in B), each vertex having exactly d_ edges. */
static void build_from_pairs(int h, const int *pa, const int *pb, int m) {
    int d = d_, N = 2 * h;
    free(adj);
    adj = malloc(sizeof(int) * (size_t)N * d);
    int *cnt = calloc((size_t)N, sizeof(int));
    for (int p = 0; p < m; p++) {
        int a = pa[p], b = h + pb[p];
        adj[a * d + cnt[a]++] = b;
        adj[b * d + cnt[b]++] = a;
    }
    free(cnt);
}

static void record(void) {
    int h = h_, d = d_;
    int *ne = malloc(sizeof(int) * 2 * (size_t)h * d);
    int p = 0;
    for (int a = 0; a < h; a++)
        for (int k = 0; k < d; k++) {
            ne[2 * p] = a;
            ne[2 * p + 1] = adj[a * d + k];
            p++;
        }
    free(bestE);
    bestE = ne;
    bestH = h;
}

/* Add two vertices (one per side): remove d edges (a_i,b_i) with distinct a_i and b_i,
   then add (new_A, b_i) and (a_i, new_B). Degrees stay d. Returns 0 if no such choice was found. */
static int grow(void) {
    int h = h_, d = d_, m = d * h;
    int *pa = malloc(sizeof(int) * m), *pb = malloc(sizeof(int) * m);
    int p = 0;
    for (int a = 0; a < h; a++)
        for (int k = 0; k < d; k++) {
            pa[p] = a;
            pb[p] = adj[a * d + k] - h;
            p++;
        }
    char *usedA = calloc((size_t)h, 1), *usedB = calloc((size_t)h, 1), *mark = calloc((size_t)m, 1);
    int rem[MAXD];
    int chosen = 0;
    for (int tries = 0; chosen < d && tries < 5000; tries++) {
        int e = rndi(m);
        int a = pa[e], b = pb[e];
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = usedB[b] = 1;
        mark[e] = 1;
        rem[chosen++] = e;
    }
    int ok = (chosen == d);
    if (ok) {
        int tot = m + d;
        int *na = malloc(sizeof(int) * tot), *nb = malloc(sizeof(int) * tot);
        int n = 0;
        for (int e = 0; e < m; e++)
            if (!mark[e]) { na[n] = pa[e]; nb[n] = pb[e]; n++; }
        for (int c = 0; c < d; c++) {
            int e = rem[c];
            na[n] = h; nb[n] = pb[e]; n++;
            na[n] = pa[e]; nb[n] = h; n++;
        }
        h_ = h + 1;
        build_from_pairs(h_, na, nb, n);
        ensure_buffers();
        free(na); free(nb);
    }
    free(pa); free(pb); free(usedA); free(usedB); free(mark);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;

    /* Start from K_{d,d}, which has diameter 2 <= D. */
    h_ = d_;
    {
        int m = d_ * d_;
        int *pa = malloc(sizeof(int) * m), *pb = malloc(sizeof(int) * m);
        int p = 0;
        for (int a = 0; a < d_; a++)
            for (int b = 0; b < d_; b++) { pa[p] = a; pb[p] = b; p++; }
        build_from_pairs(h_, pa, pb, m);
        free(pa); free(pb);
    }
    ensure_buffers();
    long long cost = eval_cost();

    const long long EPOCH = 30000;
    const double T0 = 2.0, T1 = 0.15;

    while (1) {
        if (now() > tend) break;
        if (cost == 0) {
            if (h_ > bestH) record();
            if (grow()) { cost = eval_cost(); continue; }
        }
        int h = h_, d = d_;
        int a1 = rndi(h), a2 = rndi(h);
        if (a1 == a2) continue;
        int i = rndi(d), j = rndi(d);
        int b1 = adj[a1 * d + i], b2 = adj[a2 * d + j];
        if (findrow(a1, b2) >= 0 || findrow(a2, b1) >= 0) continue;
        do_switch(a1, i, a2, j);
        long long c2 = eval_cost();
        double phase = (double)(evals % EPOCH) / (double)EPOCH;
        double T = T0 * pow(T1 / T0, phase);
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            do_switch(a1, i, a2, j);
        }
    }
    if (cost == 0 && h_ > bestH) record();

    if (bestH == 0) { printf("0 0\n"); return 0; }
    int E = bestH * d_;
    printf("%d %d\n", 2 * bestH, E);
    for (int p = 0; p < E; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    _ = time.monotonic() - start
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
