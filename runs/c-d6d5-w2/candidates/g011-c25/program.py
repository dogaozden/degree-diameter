import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow-and-repair search on bipartite d-regular graphs.
#
# State: M vertices per side, edges stored as (A index, B index) pairs. Every
# vertex has degree DEG. Moves are degree-preserving edge switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), accepted by Metropolis on the cost
# "ordered vertex pairs at distance > DIAM", computed with bitset BFS.
#
# When the cost reaches 0 the graph is valid and is saved. Growth adds one A
# and one B vertex: each of DEG random old edges (x,y) is replaced by (x,b)
# and (a,y), so all degrees stay DEG and the bipartition is kept. Annealing
# then repairs the new bad pairs. The search keeps the last valid graph and
# prints it at the deadline.
#
# Start: stdin graph, which must be d-regular and bipartite with vertices
# 0..n/2-1 on side A and n/2..n-1 on side B. The driver passes PG(2,d-1)
# when d-1 is a prime power, otherwise K_{d,d}.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define WMAX ((2 * MAXM + 63) / 64)
#define TEMP0 1.5

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int DEG, DIAM, M, Ms;
static int *ea, *eb, *sa, *sb, *adj, *cntv;
static unsigned char *mat;
static uint64_t *cur, *nxt;

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

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered vertex pairs (u,v), u != v or not, with dist > DIAM. Zero iff valid. */
static long long eval_cost(void) {
    int N = 2 * M;
    int W = (N + 63) >> 6;
    int E = M * DEG;
    memset(cntv, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < E; e++) {
        int u = ea[e], v = M + eb[e];
        if (cntv[u] < DEG) adj[(size_t)u * DEG + cntv[u]++] = v;
        if (cntv[v] < DEG) adj[(size_t)v * DEG + cntv[v]++] = u;
    }
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < cntv[v]; k++) {
                const uint64_t *s2 = cur + (size_t)adj[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(s[w]);
        bad += N - pc;
    }
    return bad;
}

static void save_valid(void) {
    Ms = M;
    memcpy(sa, ea, sizeof(int) * (size_t)M * DEG);
    memcpy(sb, eb, sizeof(int) * (size_t)M * DEG);
}

/* Add one A vertex a = M and one B vertex b = M, keeping all degrees at DEG. */
static void grow(void) {
    int old = M, a = old, b = old;
    int E = old * DEG;
    M = old + 1;
    for (int k = 0; k < DEG; k++) {
        int e;
        do {
            e = rnd_int(E);
        } while (ea[e] >= old || eb[e] >= old);
        int x = ea[e], y = eb[e];
        mat[(size_t)x * MAXM + y] = 0;
        mat[(size_t)x * MAXM + b] = 1;
        mat[(size_t)a * MAXM + y] = 1;
        eb[e] = b;
        ea[E + k] = a;
        eb[E + k] = y;
    }
}

static int load_start(int n, int me) {
    if (n < 2 || (n & 1)) return 0;
    int half = n / 2;
    if (half >= MAXM - 1 || me != half * DEG) return 0;
    int *ta = malloc(sizeof(int) * (size_t)me);
    int *tb = malloc(sizeof(int) * (size_t)me);
    int *dc = calloc((size_t)n, sizeof(int));
    int ok = 1;
    for (int i = 0; i < me && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || v >= n || u >= half || v < half) { ok = 0; break; }
        int b = v - half;
        if (mat[(size_t)u * MAXM + b]) { ok = 0; break; }
        mat[(size_t)u * MAXM + b] = 1;
        ta[i] = u;
        tb[i] = b;
        dc[u]++;
        dc[v]++;
    }
    if (ok) {
        for (int v = 0; v < n; v++) {
            if (dc[v] != DEG) { ok = 0; break; }
        }
    }
    if (ok) {
        M = half;
        memcpy(ea, ta, sizeof(int) * (size_t)me);
        memcpy(eb, tb, sizeof(int) * (size_t)me);
    }
    free(ta);
    free(tb);
    free(dc);
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
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    ea = malloc(sizeof(int) * (size_t)MAXM * DEG);
    eb = malloc(sizeof(int) * (size_t)MAXM * DEG);
    sa = malloc(sizeof(int) * (size_t)MAXM * DEG);
    sb = malloc(sizeof(int) * (size_t)MAXM * DEG);
    adj = malloc(sizeof(int) * (size_t)2 * MAXM * DEG);
    cntv = malloc(sizeof(int) * (size_t)2 * MAXM);
    cur = malloc(sizeof(uint64_t) * (size_t)2 * MAXM * WMAX);
    nxt = malloc(sizeof(uint64_t) * (size_t)2 * MAXM * WMAX);
    mat = calloc((size_t)MAXM * MAXM, 1);

    int n, me;
    if (scanf("%d %d", &n, &me) != 2 || !load_start(n, me)) {
        printf("0 0\n");
        return 0;
    }

    long long cost = eval_cost();
    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            save_valid();
            if (M + 1 >= MAXM) break;
            grow();
            cost = eval_cost();
            continue;
        }
        int E = M * DEG;
        for (int it = 0; it < 128 && cost > 0; it++) {
            int e1 = rnd_int(E), e2 = rnd_int(E);
            if (e1 == e2) continue;
            int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
            if (a1 == a2 || b1 == b2) continue;
            if (mat[(size_t)a1 * MAXM + b2] || mat[(size_t)a2 * MAXM + b1]) continue;
            mat[(size_t)a1 * MAXM + b1] = 0;
            mat[(size_t)a2 * MAXM + b2] = 0;
            mat[(size_t)a1 * MAXM + b2] = 1;
            mat[(size_t)a2 * MAXM + b1] = 1;
            eb[e1] = b2;
            eb[e2] = b1;
            long long c2 = eval_cost();
            int acc = (c2 <= cost) || (rnd_unit() < exp(-(double)(c2 - cost) / TEMP0));
            if (acc) {
                cost = c2;
            } else {
                mat[(size_t)a1 * MAXM + b2] = 0;
                mat[(size_t)a2 * MAXM + b1] = 0;
                mat[(size_t)a1 * MAXM + b1] = 1;
                mat[(size_t)a2 * MAXM + b2] = 1;
                eb[e1] = b1;
                eb[e2] = b2;
            }
        }
    }

    if (Ms > 0) {
        int nn = 2 * Ms, mm = Ms * DEG;
        printf("%d %d\n", nn, mm);
        for (int e = 0; e < mm; e++) printf("%d %d\n", sa[e], Ms + sb[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions used as safe fallbacks and as the C start graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_regular(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (d-regular), else None."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: safe fallback first, then one C grow-and-repair run.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, d-regular with diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    start = best
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        reg = _pg_regular(d)
        if reg is not None:
            start = reg  # d-regular, diameter 3, so valid for every D >= 3

    if best_n >= lib.moore_bound(d, D):
        return best

    # The C deadline is measured from process start; compile time sits inside
    # the 2.0 s reserve. Stay near 90% of the limit for safety.
    rem = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if rem >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{rem:.2f}"],
                            stdin_graph=start, timeout=rem + 20.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
