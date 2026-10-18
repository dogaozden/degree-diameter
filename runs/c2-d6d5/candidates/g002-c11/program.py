import time

import lib


# ----------------------------------------------------------------------------
# Generic C engine: simulated annealing over d-regular bipartite graphs with a
# fixed order N. The state is a double-edge-swap neighbourhood, which keeps
# degrees and bipartiteness. The cost is the number of ordered vertex pairs at
# distance greater than D, computed with bitset ball growth. Moves are biased
# toward vertices that still have bad pairs.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int N, D, d, H, W;
static int *nb;
static unsigned char *adj;
static uint64_t *buf[3];
static int curb;
static int *badlist;
static int nbad;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static void repl(int v, int old, int nw) {
    int *p = nb + (long)v * d;
    for (int j = 0; j < d; j++) {
        if (p[j] == old) { p[j] = nw; return; }
    }
}

static int try_swap(int a1, int b1, int a2, int b2) {
    if (a1 == a2 || b1 == b2) return 0;
    if (adj[(long)a1 * N + b2] || adj[(long)a2 * N + b1]) return 0;
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    adj[(long)a1 * N + b1] = 0; adj[(long)b1 * N + a1] = 0;
    adj[(long)a2 * N + b2] = 0; adj[(long)b2 * N + a2] = 0;
    adj[(long)a1 * N + b2] = 1; adj[(long)b2 * N + a1] = 1;
    adj[(long)a2 * N + b1] = 1; adj[(long)b1 * N + a2] = 1;
    return 1;
}

static void undo_swap(int a1, int b1, int a2, int b2) {
    repl(a1, b2, b1);
    repl(b1, a2, a1);
    repl(a2, b1, b2);
    repl(b2, a1, a2);
    adj[(long)a1 * N + b2] = 0; adj[(long)b2 * N + a1] = 0;
    adj[(long)a2 * N + b1] = 0; adj[(long)b1 * N + a2] = 0;
    adj[(long)a1 * N + b1] = 1; adj[(long)b1 * N + a1] = 1;
    adj[(long)a2 * N + b2] = 1; adj[(long)b2 * N + a2] = 1;
}

/* Ball growth. Uses the two buffers that are not buf[curb]. Returns the
   number of unreached ordered pairs; *res is the buffer holding the result. */
static long long evaluate(int *res) {
    int a = (curb + 1) % 3, b = (curb + 2) % 3;
    uint64_t *A = buf[a];
    memset(A, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) A[(long)v * W + v / 64] |= 1ULL << (v % 64);
    for (int it = 0; it < D; it++) {
        uint64_t *Bf = buf[b];
        for (int v = 0; v < N; v++) {
            uint64_t *t = Bf + (long)v * W;
            const uint64_t *s = A + (long)v * W;
            for (int w = 0; w < W; w++) t[w] = s[w];
            const int *p = nb + (long)v * d;
            for (int j = 0; j < d; j++) {
                const uint64_t *r = A + (long)p[j] * W;
                for (int w = 0; w < W; w++) t[w] |= r[w];
            }
        }
        int tt = a; a = b; b = tt;
        A = buf[a];
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const uint64_t *row = A + (long)v * W;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(row[w]);
        cost += N - pc;
    }
    *res = a;
    return cost;
}

static void rebuild_bad(void) {
    const uint64_t *R = buf[curb];
    nbad = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const uint64_t *row = R + (long)v * W;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(row[w]);
        if (pc < N) badlist[nbad++] = v;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    N = atoi(argv[5]);
    if (d < 1 || D < 1 || N < 2 * d || (N & 1) || N > 4000) { printf("0 0\n"); return 0; }

    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    H = N / 2;
    W = (N + 63) / 64;
    nb = malloc(sizeof(int) * (size_t)N * d);
    adj = calloc((size_t)N * N, 1);
    badlist = malloc(sizeof(int) * (size_t)N);
    for (int k = 0; k < 3; k++) buf[k] = malloc(sizeof(uint64_t) * (size_t)N * W);
    if (!nb || !adj || !badlist || !buf[0] || !buf[1] || !buf[2]) { printf("0 0\n"); return 0; }

    /* Circulant bipartite start: A_i ~ B_{i+s}, s < d. */
    for (int i = 0; i < H; i++) {
        for (int s = 0; s < d; s++) {
            int b = H + (i + s) % H;
            nb[i * d + s] = b;
            adj[(long)i * N + b] = 1;
            adj[(long)b * N + i] = 1;
        }
    }
    for (int j = 0; j < H; j++) {
        for (int s = 0; s < d; s++) {
            int i = ((j - s) % H + H) % H;
            nb[(H + j) * d + s] = i;
        }
    }

    /* Randomise by double-edge swaps. */
    long tries = 20L * N * d;
    for (long t = 0; t < tries; t++) {
        int a1 = rndint(H), b1 = nb[a1 * d + rndint(d)];
        int a2 = rndint(H), b2 = nb[a2 * d + rndint(d)];
        try_swap(a1, b1, a2, b2);
    }

    curb = 0;
    int r;
    long long cur = evaluate(&r);
    curb = r;
    rebuild_bad();

    double T0 = 3.0, T1 = 0.15;
    clock_t c0 = clock();
    double elapsed = 0.0;
    long long iter = 0;
    while (cur > 0) {
        if ((iter & 31) == 0) {
            elapsed = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (elapsed >= limit) break;
        }
        iter++;
        double frac = elapsed / limit;
        if (frac > 1.0) frac = 1.0;
        double T = T0 * pow(T1 / T0, frac);

        int x;
        if (nbad > 0 && rnd01() < 0.5) x = badlist[rndint(nbad)];
        else x = rndint(N);
        int a1, b1, a2, b2;
        if (x < H) {
            a1 = x;
            b1 = nb[x * d + rndint(d)];
        } else {
            b1 = x;
            a1 = nb[x * d + rndint(d)];
        }
        a2 = rndint(H);
        b2 = nb[a2 * d + rndint(d)];
        if (!try_swap(a1, b1, a2, b2)) continue;

        int rr;
        long long c2 = evaluate(&rr);
        double delta = (double)(c2 - cur);
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            curb = rr;
            cur = c2;
            rebuild_bad();
        } else {
            undo_swap(a1, b1, a2, b2);
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    long M = (long)N * d / 2;
    printf("%d %ld\n", N, M);
    for (int v = 0; v < N; v++) {
        for (int j = 0; j < d; j++) {
            int u = nb[v * d + j];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (used for calibration-style cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Glue around the C engine.
# ----------------------------------------------------------------------------

def _attempt(d, D, N, seed, secs):
    """Run the annealer for a graph of order N. Return (n, edges) if valid, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.2f}", N], timeout=secs + 8.0)
        n, edges = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n < 1 or not edges:
        return None
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D) and pg[0] > best[0]:
            best = pg
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Ladder over the order N: succeed -> grow the step, fail -> shrink it.
    total = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + total
    step = 1  # N = best_n + 2 * step; step halves on failure and doubles on success
    attempts = 0
    while step >= 1:
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        secs = min(remaining - 0.5, max(1.5, 0.3 * total))
        N = best[0] + 2 * step
        res = _attempt(d, D, N, seed + attempts, secs)
        attempts += 1
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
            step *= 2
        else:
            step //= 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
