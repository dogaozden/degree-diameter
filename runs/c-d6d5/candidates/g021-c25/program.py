import time

import lib


# ----------------------------------------------------------------------------
# C engine: vertex-level search over bipartite d-regular graphs.
#
# No group structure is imposed. The state is a d-regular bipartite graph with
# N vertices per side (A = 0..N-1, B = N..2N-1). Moves are degree-preserving
# double edge swaps. The cost is the number of ordered vertex pairs at distance
# greater than DIAM, computed with bitset ball expansion. Simulated annealing
# runs at a fixed N until the cost reaches 0. Then the graph is saved and grown
# by one vertex per side. Growth inserts a new A and a new B vertex by
# replacing d-1 disjoint edges (a_i, b_i) with (a_i, b') and (a', b_i), and
# adding (a', b'). This keeps every degree equal to d, so annealing resumes
# from a nearly valid state. Only zero-cost graphs are ever output.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1400
#define VMAX (2 * NMAX)
#define WMAXB ((VMAX + 63) / 64)
#define STAGE 4000
#define T_HOT 2.0
#define T_COLD 0.2

static int DEG, DIAM, N, E;
static int *ea, *eb, *adj;          /* edge k = (ea[k], eb[k]); adj[v*DEG + t] */
static int *sea, *seb, *bea, *beb;  /* stage-best copy and global best copy */
static int bestN = 0;
static uint64_t *Ra, *Rb;
static int cntv[VMAX];
static int used[NMAX];
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

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_nb_upto(int v, int u, int cnt) {
    const int *row = adj + (size_t)v * DEG;
    for (int t = 0; t < cnt; t++) if (row[t] == u) return 1;
    return 0;
}

static int has_nb(int v, int u) { return has_nb_upto(v, u, DEG); }

/* In row v, replace neighbour old by nw. */
static void rep(int v, int old, int nw) {
    int *row = adj + (size_t)v * DEG;
    for (int t = 0; t < DEG; t++)
        if (row[t] == old) { row[t] = nw; return; }
}

/* Edge k1 = (a,b), k2 = (c,e) become (a,e), (c,b). Applying it twice restores the start. */
static void apply_swap(int k1, int k2) {
    int a = ea[k1], b = eb[k1], c = ea[k2], e = eb[k2];
    rep(a, b, e);
    rep(e, c, a);
    rep(b, a, c);
    rep(c, e, b);
    ea[k1] = a; eb[k1] = e;
    ea[k2] = c; eb[k2] = b;
}

static void rebuild_adj(void) {
    memset(cntv, 0, sizeof(int) * (size_t)(2 * N));
    for (int k = 0; k < E; k++) {
        int a = ea[k], b = eb[k];
        adj[(size_t)a * DEG + cntv[a]++] = b;
        adj[(size_t)b * DEG + cntv[b]++] = a;
    }
}

/* Number of ordered pairs (v, w) with dist(v, w) > DIAM. */
static long long eval_cost(void) {
    int V = 2 * N, W = (V + 63) >> 6;
    uint64_t *R = Ra, *NR = Rb;
    memset(R, 0, sizeof(uint64_t) * (size_t)V * W);
    for (int v = 0; v < V; v++) R[(size_t)v * W + (v >> 6)] = 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < V; v++) {
            uint64_t *out = NR + (size_t)v * W;
            const uint64_t *in = R + (size_t)v * W;
            for (int w = 0; w < W; w++) out[w] = in[w];
            const int *row = adj + (size_t)v * DEG;
            for (int t = 0; t < DEG; t++) {
                const uint64_t *src = R + (size_t)row[t] * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        uint64_t *tmp = R; R = NR; NR = tmp;
    }
    long long unc = 0;
    for (int v = 0; v < V; v++) {
        int c = 0;
        const uint64_t *in = R + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pc64(in[w]);
        unc += V - c;
    }
    return unc;
}

/* Random d-regular bipartite start: one greedy matching per layer, retried on failure. */
static int init_random(int n0) {
    N = n0;
    E = N * DEG;
    for (int l = 0; l < DEG; l++) {
        memset(used, 0, sizeof(int) * (size_t)N);
        for (int i = 0; i < N; i++) {
            int found = -1;
            for (int tr = 0; tr < 64 && found < 0; tr++) {
                int j = rnd_int(N);
                if (!used[j] && !has_nb_upto(i, N + j, l)) found = j;
            }
            for (int j = 0; j < N && found < 0; j++)
                if (!used[j] && !has_nb_upto(i, N + j, l)) found = j;
            if (found < 0) return 0;
            used[found] = 1;
            adj[(size_t)i * DEG + l] = N + found;
            adj[(size_t)(N + found) * DEG + l] = i;
            ea[l * N + i] = i;
            eb[l * N + i] = N + found;
        }
    }
    return 1;
}

/* Add one vertex per side, keeping all degrees equal to DEG. Returns 0 on failure. */
static int grow(void) {
    int oldN = N;
    int chosen[32], nc = 0;
    int tries = 0;
    while (nc < DEG - 1) {
        if (++tries > 20000) return 0;
        int k = rnd_int(E), ok = 1;
        for (int i = 0; i < nc && ok; i++) {
            int kk = chosen[i];
            if (ea[kk] == ea[k] || eb[kk] == eb[k]) ok = 0;
        }
        if (ok) chosen[nc++] = k;
    }
    /* Shift B labels up by one: B ids >= oldN move to id + 1. */
    for (int k = 0; k < E; k++) if (eb[k] >= oldN) eb[k]++;
    for (int v = 0; v < oldN; v++) {
        int *row = adj + (size_t)v * DEG;
        for (int t = 0; t < DEG; t++) if (row[t] >= oldN) row[t]++;
    }
    for (int v = 2 * oldN - 1; v >= oldN; v--)
        memcpy(adj + (size_t)(v + 1) * DEG, adj + (size_t)v * DEG, sizeof(int) * (size_t)DEG);

    N = oldN + 1;
    int ap = oldN, bp = 2 * N - 1;
    for (int i = 0; i < nc; i++) {
        int k = chosen[i];
        int a = ea[k], b = eb[k];
        rep(a, b, bp);
        rep(b, a, ap);
        eb[k] = bp;
        ea[E + i] = ap;
        eb[E + i] = b;
        adj[(size_t)ap * DEG + i] = b;
        adj[(size_t)bp * DEG + i] = a;
    }
    ea[E + DEG - 1] = ap;
    eb[E + DEG - 1] = bp;
    adj[(size_t)ap * DEG + DEG - 1] = bp;
    adj[(size_t)bp * DEG + DEG - 1] = ap;
    E += DEG;
    return 1;
}

/* One annealing stage at fixed N. Ends early at cost 0. Restores the stage-best state. */
static void run_stage(long long cur) {
    long long bestc = cur;
    memcpy(sea, ea, sizeof(int) * (size_t)E);
    memcpy(seb, eb, sizeof(int) * (size_t)E);
    for (int it = 0; it < STAGE && cur > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        double frac = (double)it / STAGE;
        double temp = T_HOT * pow(T_COLD / T_HOT, frac);
        int k1 = rnd_int(E), k2 = rnd_int(E);
        if (k1 == k2) continue;
        int a = ea[k1], b = eb[k1], c = ea[k2], e = eb[k2];
        if (a == c || b == e) continue;
        if (has_nb(a, e) || has_nb(c, b)) continue;
        apply_swap(k1, k2);
        long long nc = eval_cost();
        long long dl = nc - cur;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(sea, ea, sizeof(int) * (size_t)E);
                memcpy(seb, eb, sizeof(int) * (size_t)E);
            }
        } else {
            apply_swap(k1, k2);
        }
    }
    if (cur != bestc) {
        memcpy(ea, sea, sizeof(int) * (size_t)E);
        memcpy(eb, seb, sizeof(int) * (size_t)E);
        rebuild_adj();
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [n0]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 100;
    if (DEG < 3 || DEG > 16 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    ea = calloc((size_t)NMAX * DEG, sizeof(int));
    eb = calloc((size_t)NMAX * DEG, sizeof(int));
    sea = calloc((size_t)NMAX * DEG, sizeof(int));
    seb = calloc((size_t)NMAX * DEG, sizeof(int));
    bea = calloc((size_t)NMAX * DEG, sizeof(int));
    beb = calloc((size_t)NMAX * DEG, sizeof(int));
    adj = calloc((size_t)VMAX * DEG, sizeof(int));
    Ra = calloc((size_t)VMAX * WMAXB, sizeof(uint64_t));
    Rb = calloc((size_t)VMAX * WMAXB, sizeof(uint64_t));

    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    if (n0 < DEG) n0 = DEG;
    if (n0 > NMAX - 2) n0 = NMAX - 2;
    int ok = 0;
    for (int tries = 0; tries < 200 && !ok; tries++) ok = init_random(n0);
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    rebuild_adj();

    while (elapsed() < DEADLINE) {
        long long c = eval_cost();
        if (c == 0) {
            bestN = N;
            memcpy(bea, ea, sizeof(int) * (size_t)E);
            memcpy(beb, eb, sizeof(int) * (size_t)E);
            if (N + 2 >= NMAX) break;
            if (!grow()) break;
            continue;
        }
        run_stage(c);
    }

    if (bestN > 0) {
        printf("%d %d\n", 2 * bestN, bestN * DEG);
        for (int k = 0; k < bestN * DEG; k++)
            printf("%d %d\n", bea[k], beb[k]);
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
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: bipartite, 2-regular, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2 and optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the annealer nearly all of the budget. The reserve covers the
    # one-off C compile (outside the C deadline), parsing and validation.
    remaining = 0.92 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", max(d, 100)],
                            timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
