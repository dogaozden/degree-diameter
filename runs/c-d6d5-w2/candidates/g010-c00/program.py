"""Switch-repair growth search for bipartite graphs with max degree d and diameter D.

Approach: for each candidate order 2h, start from a random d-regular bipartite
graph (circulant, randomised by edge switches) and minimise the number of
unreached ordered pairs with simulated annealing over degree-preserving edge
switches. Distances are computed with bitset BFS. The order grows whenever an
annealing run reaches zero cost, and the step halves after failures. The best
valid graph is returned, or a safe K_{d,d} / projective-plane fallback.
"""
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define TSTART 8.0
#define TEND 0.05

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

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

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static inline int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DEG, DIAM;
static int H, N, W;
static int *nbr = NULL;
static uint64_t *bufA = NULL, *bufB = NULL, *cur = NULL, *nxt = NULL;
static int *bestnbr = NULL;
static int best_h = 0;

/* Vertices: A = 0..H-1, B = H..2H-1. nbr[v*DEG + k] lists neighbours of v. */

static int contains(int v, int x) {
    const int *p = nbr + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (p[k] == x) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *p = nbr + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (p[k] == old) { p[k] = nw; return; }
}

/* Propose the switch (x1,y1),(x2,y2) -> (x1,y2),(x2,y1). Returns 0 if invalid. */
static int propose(int *x1, int *y1, int *x2, int *y2) {
    int a = rnd_int(H), b = rnd_int(H);
    if (a == b) return 0;
    int p = nbr[a * DEG + rnd_int(DEG)];
    int q = nbr[b * DEG + rnd_int(DEG)];
    if (contains(a, q) || contains(b, p)) return 0;
    *x1 = a; *y1 = p; *x2 = b; *y2 = q;
    return 1;
}

static void apply_sw(int x1, int y1, int x2, int y2) {
    replace_nb(x1, y1, y2);
    replace_nb(x2, y2, y1);
    replace_nb(y1, x1, x2);
    replace_nb(y2, x2, x1);
}

static void undo_sw(int x1, int y1, int x2, int y2) {
    replace_nb(x1, y2, y1);
    replace_nb(x2, y1, y2);
    replace_nb(y1, x2, x1);
    replace_nb(y2, x1, x2);
}

/* Number of ordered vertex pairs at distance > DIAM (bitset BFS). */
static long long eval_cost(void) {
    int d = DEG;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            const int *p = nbr + (size_t)v * d;
            for (int k = 0; k < d; k++) {
                const uint64_t *c2 = cur + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += popc(c[w]);
        total += N - cnt;
    }
    return total;
}

/* Try to find a valid graph on 2h vertices. On success, store it as the new best. */
static int attempt(int h, double tend) {
    H = h;
    N = 2 * h;
    W = (N + 63) / 64;
    nbr = malloc(sizeof(int) * (size_t)N * DEG);
    bufA = malloc(sizeof(uint64_t) * (size_t)N * W);
    bufB = malloc(sizeof(uint64_t) * (size_t)N * W);
    if (!nbr || !bufA || !bufB) {
        free(nbr); free(bufA); free(bufB);
        nbr = NULL; bufA = NULL; bufB = NULL;
        return 0;
    }
    cur = bufA;
    nxt = bufB;

    /* Circulant d-regular bipartite start (valid since h > DEG). */
    for (int i = 0; i < h; i++)
        for (int j = 0; j < DEG; j++)
            nbr[i * DEG + j] = h + (i + j) % h;
    for (int t = 0; t < h; t++)
        for (int j = 0; j < DEG; j++)
            nbr[(h + t) * DEG + j] = ((t - j) % h + h) % h;

    /* Randomise with switches (no evaluation). */
    int mix = 20 * h * DEG;
    for (int s = 0; s < mix; s++) {
        int x1, y1, x2, y2;
        if (propose(&x1, &y1, &x2, &y2)) apply_sw(x1, y1, x2, y2);
    }

    int ok = 0;
    double t0 = elapsed();
    double span = tend - t0;
    if (span > 0.0) {
        long long cost = eval_cost();
        long long it = 0;
        double temp = TSTART;
        while (cost > 0) {
            if ((it & 31) == 0) {
                double now = elapsed();
                if (now >= tend) break;
                double frac = (now - t0) / span;
                temp = TSTART * (1.0 - frac) + TEND;
            }
            it++;
            int x1, y1, x2, y2;
            if (!propose(&x1, &y1, &x2, &y2)) continue;
            apply_sw(x1, y1, x2, y2);
            long long nc = eval_cost();
            long long dl = nc - cost;
            if (dl <= 0 || rnd_unit() < exp(-(double)dl / temp)) {
                cost = nc;
            } else {
                undo_sw(x1, y1, x2, y2);
            }
        }
        ok = (cost == 0);
    }

    if (ok) {
        /* A rows are the first h*DEG entries and hold every edge. */
        int *nb = malloc(sizeof(int) * (size_t)h * DEG);
        if (nb) {
            memcpy(nb, nbr, sizeof(int) * (size_t)h * DEG);
            free(bestnbr);
            bestnbr = nb;
            best_h = h;
        } else {
            ok = 0;
        }
    }

    free(nbr); free(bufA); free(bufB);
    nbr = NULL; bufA = NULL; bufB = NULL; cur = NULL; nxt = NULL;
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 2 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    /* Safe start: K_{d,d} has diameter 2, so it is valid for DIAM >= 2. */
    best_h = DEG;
    bestnbr = malloc(sizeof(int) * (size_t)DEG * DEG);
    for (int i = 0; i < DEG; i++)
        for (int j = 0; j < DEG; j++)
            bestnbr[i * DEG + j] = DEG + j;

    int step = best_h / 4 + 1;
    int fails = 0;
    while (elapsed() < DEADLINE) {
        double now = elapsed();
        double rem = DEADLINE - now;
        if (rem < 0.3) break;
        int cand = best_h + step;
        if (cand > 1000000) break;
        double share = rem * 0.35;
        if (share < 1.0) share = (rem < 1.0) ? rem : 1.0;
        double cap = now + share;
        if (cap > DEADLINE) cap = DEADLINE;
        if (attempt(cand, cap)) {
            fails = 0;
        } else {
            fails++;
            if (step > 1) {
                step = (step + 1) / 2;
            } else if (fails >= 4) {
                break;
            }
        }
    }

    printf("%d %d\n", 2 * best_h, best_h * DEG);
    for (int i = 0; i < best_h; i++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", i, bestnbr[i * DEG + j]);
    free(bestnbr);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
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

    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search nearly all of the budget. The reserve covers the
    # one-off C compile, parsing and validation.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            timeout=remaining + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
