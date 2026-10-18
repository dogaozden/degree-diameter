import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of bi-Cayley lifts over Z_m x| Z_k, this engine works on
# arbitrary d-regular bipartite graphs. It draws a random d-regular bipartite
# graph on 2h vertices (union of d random perfect matchings between two sides),
# removes multi-edges by switches, then runs simulated annealing with
# degree-preserving 2-switches to cut the number of vertex pairs at distance
# greater than D. The side size h ratchets upward on success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PATIENCE 800

static clock_t g_t0;
static double g_budget = 1.0;
static uint64_t g_rs = 88172645463325252ULL;

static int d_ = 1, D_ = 1;
static int H = 0, N = 0, W = 0;
static int *nb = NULL;          /* N*d adjacency; A = 0..H-1, B = H..2H-1 */
static int *best_e = NULL;
static long best_n = 0, best_m = 0;

static double elapsed(void) {
    return (double)(clock() - g_t0) / (double)CLOCKS_PER_SEC;
}

static uint64_t rnext(void) {
    uint64_t x = g_rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    g_rs = x;
    return x * 2685821657736338717ULL;
}

static uint64_t rnd(uint64_t n) {
    return n ? rnext() % n : 0;
}

static double rndf(void) {
    return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0);
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int contains(const int *row, int v) {
    for (int k = 0; k < d_; k++)
        if (row[k] == v) return 1;
    return 0;
}

static void replace_in_row(int v, int from, int to) {
    int *r = nb + (size_t)v * d_;
    for (int k = 0; k < d_; k++) {
        if (r[k] == from) {
            r[k] = to;
            return;
        }
    }
}

/* Degree-preserving switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static void apply_switch(int a1, int i, int a2, int j) {
    int *r1 = nb + (size_t)a1 * d_;
    int *r2 = nb + (size_t)a2 * d_;
    int b1 = r1[i], b2 = r2[j];
    r1[i] = b2;
    r2[j] = b1;
    replace_in_row(b1, a1, a2);
    replace_in_row(b2, a2, a1);
}

static int dup_before(int a, int i) {
    const int *r = nb + (size_t)a * d_;
    for (int k = 0; k < i; k++)
        if (r[k] == r[i]) return 1;
    return 0;
}

/* Fills res with reach bitsets (within distance D). Returns ordered missing pairs. */
static long reach(uint64_t *res, uint64_t *scr) {
    memset(res, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++)
        res[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    uint64_t *src = res, *dst = scr;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = dst + (size_t)v * W;
            const uint64_t *s = src + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            const int *row = nb + (size_t)v * d_;
            for (int l = 0; l < d_; l++) {
                const uint64_t *u = src + (size_t)row[l] * W;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        uint64_t *tmp = src;
        src = dst;
        dst = tmp;
    }
    if (src != res) memcpy(res, src, sizeof(uint64_t) * (size_t)N * W);
    long miss = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *o = res + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pop64(o[w]);
        miss += N - c;
    }
    return miss;
}

static int row_full(const uint64_t *R, int v) {
    int c = 0;
    const uint64_t *o = R + (size_t)v * W;
    for (int w = 0; w < W; w++) c += pop64(o[w]);
    return c == N;
}

/* Random d-regular bipartite graph on 2h vertices, multi-edges removed by switches. */
static int build_random(int h) {
    H = h;
    N = 2 * h;
    W = (N + 63) / 64;
    nb = realloc(nb, sizeof(int) * (size_t)N * d_);
    if (!nb) return 0;
    int *p = malloc(sizeof(int) * (size_t)h);
    if (!p) return 0;
    for (int l = 0; l < d_; l++) {
        for (int a = 0; a < h; a++) p[a] = a;
        for (int a = h - 1; a > 0; a--) {
            int j = (int)rnd((uint64_t)(a + 1));
            int t = p[a];
            p[a] = p[j];
            p[j] = t;
        }
        for (int a = 0; a < h; a++) {
            nb[(size_t)a * d_ + l] = h + p[a];
            nb[(size_t)(h + p[a]) * d_ + l] = a;
        }
    }
    free(p);
    for (int a = 0; a < H; a++) {
        for (int i = 0; i < d_; i++) {
            int tries = 0;
            while (dup_before(a, i)) {
                if (++tries > 4000) return 0;
                int a2 = (int)rnd((uint64_t)(H - 1));
                if (a2 >= a) a2++;
                int j = (int)rnd((uint64_t)d_);
                int b1 = nb[(size_t)a * d_ + i];
                int b2 = nb[(size_t)a2 * d_ + j];
                if (contains(nb + (size_t)a * d_, b2) || contains(nb + (size_t)a2 * d_, b1))
                    continue;
                apply_switch(a, i, a2, j);
            }
        }
    }
    return 1;
}

static void store_best(void) {
    long n = 2L * H, m = (long)H * d_;
    if (n <= best_n) return;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    long c = 0;
    for (int a = 0; a < H; a++)
        for (int l = 0; l < d_; l++) {
            e[2 * c] = a;
            e[2 * c + 1] = nb[(size_t)a * d_ + l];
            c++;
        }
    free(best_e);
    best_e = e;
    best_n = n;
    best_m = m;
}

static int attempt(int h, double tlim) {
    if (!build_random(h)) return 0;
    uint64_t *cur = malloc(sizeof(uint64_t) * (size_t)N * W);
    uint64_t *cand = malloc(sizeof(uint64_t) * (size_t)N * W);
    uint64_t *scr = malloc(sizeof(uint64_t) * (size_t)N * W);
    int *save = malloc(sizeof(int) * 4 * (size_t)d_);
    if (!cur || !cand || !scr || !save) {
        free(cur); free(cand); free(scr); free(save);
        return 0;
    }
    long cost = reach(cur, scr);
    long last = 0;
    for (long it = 0; cost > 0; it++) {
        if (elapsed() > tlim || it - last > PATIENCE) break;

        /* pick a1: bias toward an A vertex that still has unreached pairs */
        int a1 = -1;
        if (rndf() < 0.5) {
            for (int tries = 0; tries < 40; tries++) {
                int v = (int)rnd((uint64_t)N);
                if (v < H && !row_full(cur, v)) {
                    a1 = v;
                    break;
                }
            }
        }
        if (a1 < 0) a1 = (int)rnd((uint64_t)H);
        int a2 = (int)rnd((uint64_t)(H - 1));
        if (a2 >= a1) a2++;
        int i = (int)rnd((uint64_t)d_);
        int j = (int)rnd((uint64_t)d_);
        int b1 = nb[(size_t)a1 * d_ + i];
        int b2 = nb[(size_t)a2 * d_ + j];
        if (contains(nb + (size_t)a1 * d_, b2) || contains(nb + (size_t)a2 * d_, b1))
            continue;

        int rows[4] = {a1, a2, b1, b2};
        for (int q = 0; q < 4; q++)
            memcpy(save + (size_t)q * d_, nb + (size_t)rows[q] * d_, sizeof(int) * (size_t)d_);
        apply_switch(a1, i, a2, j);

        long c2 = reach(cand, scr);
        double T = 0.6;
        if (c2 <= cost || rndf() < exp(-(double)(c2 - cost) / T)) {
            uint64_t *t = cur;
            cur = cand;
            cand = t;
            cost = c2;
            last = it;
        } else {
            for (int q = 0; q < 4; q++)
                memcpy(nb + (size_t)rows[q] * d_, save + (size_t)q * d_, sizeof(int) * (size_t)d_);
        }
    }
    int ok = (cost == 0);
    if (ok) store_best();
    free(cur);
    free(cand);
    free(scr);
    free(save);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: d D seed budget [h_start]\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    g_rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!g_rs) g_rs = 1;
    for (int w = 0; w < 10; w++) rnext();
    g_budget = atof(argv[4]);
    long hs = (argc > 5) ? atol(argv[5]) : 2;
    g_t0 = clock();

    if (d_ < 2 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    if (hs < d_) hs = d_;

    long good = hs - 1;
    long step = 4;
    long h = hs;
    while (elapsed() < g_budget) {
        double cap = elapsed() + fmax(1.0, 0.15 * g_budget);
        if (cap > g_budget) cap = g_budget;
        int ok = attempt((int)h, cap);
        if (ok) {
            good = h;
            step = good / 32 + 1;
        } else {
            step = step / 2;
            if (step < 1) step = 1;
        }
        h = good + step;
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%ld %ld\n", best_n, best_m);
    for (long c = 0; c < best_m; c++)
        printf("%d %d\n", best_e[2 * c], best_e[2 * c + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction kept as a safe baseline.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _c_search(d, D, seed, budget, h_start, timeout):
    """Run the C engine; returns (n, edges), or (0, []) if it found nothing."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", h_start], timeout=timeout)
    return lib.parse_graph_text(text)


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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 3 and d >= 2:
        budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
        h_start = max(d, lib.moore_bound(d, D) // 40, best_n // 2 + 1)
        try:
            n, e = _c_search(d, D, seed, budget, h_start, budget + 5.0)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
