"""Repair search for bipartite graphs with max degree d and diameter D.

Approach (differs from the lift search): start from a small d-regular bipartite
graph, then grow it by inserting vertex pairs. Insertion removes d disjoint
A-B edges and reattaches them to a new A vertex and a new B vertex, so every
vertex keeps degree exactly d. After each insertion, simulated annealing with
2-switch moves (which preserve degrees and bipartiteness) repairs the bad
pairs. The cost is the number of ordered vertex pairs at distance > D, computed
exactly with bitset ball propagation. When an epoch fails, the search restores
the best valid graph and retries with a smaller insertion batch.

Risk: this path is far from the lift construction that produced the 684
record, so it may score below the parent on d=6, D=5. Validity is preserved:
the best valid graph found is returned, and the fallbacks (K_{d,d}, PG(2,q)
incidence graphs) are checked with lib.is_valid before return.
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

#define MAXN 2400
#define MAXW 38
#define MAXDEG 8
#define EPOCH 3000
#define TEMP_HI 4.0
#define TEMP_LO 0.15
#define GS_CAP 64

static int DEG, DIAM, NMAX, N, NA, NB, W;
static int nb[MAXN * MAXDEG];
static int lA[MAXN], lB[MAXN];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

static int bestN = 0, bestNA = 0, bestNB = 0;
static int bNb[MAXN * MAXDEG];
static int bA[MAXN], bB[MAXN];

static int mv_a1, mv_a2, mv_b1, mv_b2;
static uint64_t rs[2];
static struct timespec T_START;
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
    return (double)(ts.tv_sec - T_START.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T_START.tv_nsec);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Sum over vertices of the number of vertices at distance > DIAM (ordered pairs). */
static long long eval_cost(void) {
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        uint64_t *r = RA + (size_t)v * W;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t *cur = RA, *nxt = RB;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int k = 0; k < DEG; k++) {
                const uint64_t *t = cur + (size_t)nb[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(r[w]);
        bad += N - c;
    }
    return bad;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < DEG; k++)
        if (nb[a * DEG + k] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int k = 0; k < DEG; k++)
        if (nb[v * DEG + k] == old) { nb[v * DEG + k] = nw; return; }
}

/* 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Keeps all degrees and bipartiteness. */
static int do_switch(void) {
    if (NA < 2) return 0;
    int a1 = lA[rnd_int(NA)], a2 = lA[rnd_int(NA)];
    if (a1 == a2) return 0;
    int b1 = nb[a1 * DEG + rnd_int(DEG)];
    int b2 = nb[a2 * DEG + rnd_int(DEG)];
    if (b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    repl(a1, b1, b2);
    repl(a2, b2, b1);
    repl(b1, a1, a2);
    repl(b2, a2, a1);
    mv_a1 = a1; mv_a2 = a2; mv_b1 = b1; mv_b2 = b2;
    return 1;
}

static void undo_switch(void) {
    int a1 = mv_a1, a2 = mv_a2, b1 = mv_b1, b2 = mv_b2;
    repl(a1, b2, b1);
    repl(a2, b1, b2);
    repl(b1, a2, a1);
    repl(b2, a1, a2);
}

/* Add two vertices (one A, one B) keeping every degree equal to DEG. */
static int insert_pair(void) {
    if (N + 2 > NMAX || NA < DEG || NB < DEG) return 0;
    int us[MAXDEG], vs[MAXDEG];
    int i = 0, tries = 0;
    while (i < DEG) {
        if (++tries > 100000) return 0;
        int u = lA[rnd_int(NA)];
        int v = nb[u * DEG + rnd_int(DEG)];
        int ok = 1;
        for (int j = 0; j < i; j++)
            if (us[j] == u || vs[j] == v) { ok = 0; break; }
        if (ok) { us[i] = u; vs[i] = v; i++; }
    }
    int a = N++, b = N++;
    lA[NA++] = a;
    lB[NB++] = b;
    for (int k = 0; k < DEG; k++) {
        repl(us[k], vs[k], b);
        repl(vs[k], us[k], a);
    }
    for (int k = 0; k < DEG; k++) {
        nb[a * DEG + k] = vs[k];
        nb[b * DEG + k] = us[k];
    }
    return 1;
}

/* Circulant d-regular bipartite graph with h + h vertices. */
static void init_circulant(int h) {
    N = 2 * h;
    NA = h;
    NB = h;
    for (int i = 0; i < h; i++) { lA[i] = i; lB[i] = h + i; }
    for (int i = 0; i < h; i++)
        for (int s = 0; s < DEG; s++) {
            nb[i * DEG + s] = h + (i + s) % h;
            nb[(h + i) * DEG + s] = (i - s + h) % h;
        }
}

static void save_best(void) {
    bestN = N;
    bestNA = NA;
    bestNB = NB;
    memcpy(bNb, nb, sizeof(int) * (size_t)N * DEG);
    memcpy(bA, lA, sizeof(int) * (size_t)NA);
    memcpy(bB, lB, sizeof(int) * (size_t)NB);
}

static void restore_best(void) {
    N = bestN;
    NA = bestNA;
    NB = bestNB;
    memcpy(nb, bNb, sizeof(int) * (size_t)N * DEG);
    memcpy(lA, bA, sizeof(int) * (size_t)NA);
    memcpy(lB, bB, sizeof(int) * (size_t)NB);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time nmax [n0]\n");
        return 1;
    }
    timespec_get(&T_START, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    NMAX = atoi(argv[5]);
    int n0 = argc > 6 ? atoi(argv[6]) : 0;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (NMAX > MAXN) NMAX = MAXN;

    uint64_t sm = sd * 2654435761ULL + 991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int h = n0 / 2;
    if (h < DEG) h = DEG;
    if (2 * h > NMAX) h = NMAX / 2;
    if (h < DEG) {
        printf("0 0\n");
        return 0;
    }
    init_circulant(h);
    for (int t = 0; t < 20 * N; t++) do_switch();

    long long cost = eval_cost();
    int steps = 0;
    int gs = 1;

    while (elapsed() < DEADLINE) {
        if (cost == 0) {
            if (N > bestN) save_best();
            gs = gs * 2;
            if (gs > GS_CAP) gs = GS_CAP;
            int grown = 0;
            for (int g = 0; g < gs; g++) grown += insert_pair();
            if (grown == 0) break;
            cost = eval_cost();
            steps = 0;
            continue;
        }
        if (steps >= EPOCH) {
            if (bestN > 0) {
                restore_best();
            } else {
                init_circulant(DEG);
                for (int t = 0; t < 20 * N; t++) do_switch();
            }
            gs = gs / 2;
            if (gs < 1) gs = 1;
            for (int g = 0; g < gs; g++) insert_pair();
            cost = eval_cost();
            steps = 0;
            continue;
        }
        double frac = (double)steps / (double)EPOCH;
        double T = TEMP_HI * pow(TEMP_LO / TEMP_HI, frac);
        steps++;
        if (!do_switch()) continue;
        long long c2 = eval_cost();
        long long dl = c2 - cost;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / T)) {
            cost = c2;
        } else {
            undo_switch();
        }
    }

    if (bestN > 0) {
        printf("%d %d\n", bestN, bestNA * DEG);
        for (int i = 0; i < bestNA; i++) {
            int a = bA[i];
            for (int k = 0; k < DEG; k++)
                printf("%d %d\n", a, bNb[a * DEG + k]);
        }
    } else {
        printf("0 0\n");
    }
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
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
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

    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if D >= 2 and remaining >= 1.0:
        nmax = min(lib.moore_bound(d, D), 2400)
        n0 = max(2 * d, best_n - best_n % 2)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", nmax, n0],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
