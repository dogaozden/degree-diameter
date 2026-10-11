import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New engine: tabu search over voltage lifts of ARBITRARY finite groups.
#
# The group is handed to C as a full multiplication table, so the same search
# runs on cyclic, direct-product and semidirect-product groups. The base graph
# has K A-vertices and K B-vertices with DEG darts per A-vertex, arranged as
# DEG permutations p_l of K. Dart (l, i) joins A_i to B_{p_l(i)} with voltage
# s. The lift has 2KG vertices, is bipartite, is DEG-regular and is valid iff
# every orbit representative reaches all vertices within DIAM steps.
#
# Search: best-of-sample tabu search. Each step samples moves (change one
# voltage, or swap two base targets of one permutation), applies the best
# non-tabu one, and forbids reverting a voltage for a short tenure. A stall
# counter perturbs the best state. The C run returns as soon as a valid lift
# is found.
# ----------------------------------------------------------------------------

C_TABU = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXT 128
#define MAXG 4096
#define BIGC 1000000000000LL
#define NSAMP 48
#define STALL 250

static int DEG, DIAM, K, G, NV, T;
static int *mt;
static int dI[MAXT], dJ[MAXT], dS[MAXT];
static int sS[MAXT], sJ[MAXT];
static int *adjv, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;
static long long *tabu;
static double DEADLINE;
static uint64_t rs0, rs1;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs0;
    const uint64_t s0 = rs1;
    rs0 = s0;
    s1 ^= s1 << 23;
    rs1 = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs1 + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

/* Cost = sum over orbit representatives of unreached vertices; 0 iff valid lift. */
static long long eval_cost(void) {
    for (int t = 0; t < T; t++)
        for (int u = t + 1; u < T; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) return BIGC;
    memset(cnt, 0, sizeof(int) * (size_t)NV);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G, s = dS[t];
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + mt[g * G + s];
            adjv[(size_t)a * DEG + cnt[a]++] = b;
            adjv[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NV);
            curstamp = 0;
        }
        curstamp++;
        int src = r * G;
        int fsz = 1, reached = 1;
        fr[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adjv + (size_t)fr[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        nx[nsz++] = v;
                    }
                }
            }
            memcpy(fr, nx, sizeof(int) * (size_t)nsz);
            fsz = nsz;
            reached += nsz;
        }
        total += NV - reached;
    }
    return total;
}

static void random_state(void) {
    int p[MAXT];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int x = p[i]; p[i] = p[j]; p[j] = x;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
}

static void save_state(void) {
    memcpy(sS, dS, sizeof(int) * (size_t)T);
    memcpy(sJ, dJ, sizeof(int) * (size_t)T);
}

static void restore_state(void) {
    memcpy(dS, sS, sizeof(int) * (size_t)T);
    memcpy(dJ, sJ, sizeof(int) * (size_t)T);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed time K G < table\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    G = atoi(argv[6]);
    uint64_t sm = sd * 2654435761ULL + 4242ULL;
    rs0 = splitmix(&sm);
    rs1 = splitmix(&sm);

    if (DEG < 1 || DEG > 32 || DIAM < 1 || K < 1 || K > 16 || G < 1 || G > MAXG
        || DEG * K > MAXT) {
        printf("0 0\n");
        return 0;
    }
    T = DEG * K;
    NV = 2 * K * G;

    int hn, hm;
    if (scanf("%d %d", &hn, &hm) != 2 || hm != G * G) {
        printf("0 0\n");
        return 0;
    }
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int k = 0; k < hm; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= G * G || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        mt[u] = v;
    }
    /* Element 0 must be the identity: the BFS sources are the fibre representatives r*G. */
    for (int y = 0; y < G; y++) {
        if (mt[y] != y || mt[y * G] != y) {
            printf("0 0\n");
            return 0;
        }
    }

    adjv = malloc(sizeof(int) * (size_t)NV * (size_t)DEG);
    cnt = malloc(sizeof(int) * (size_t)NV);
    stamp = calloc((size_t)NV, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NV);
    nx = malloc(sizeof(int) * (size_t)NV);
    tabu = calloc((size_t)T * (size_t)G, sizeof(long long));
    for (int t = 0; t < T; t++) dI[t] = t % K;

    random_state();
    long long cur = eval_cost();
    long long best = cur;
    save_state();
    long long it = 0;
    int stall = 0;

    while (cur > 0) {
        if ((it & 3) == 0 && elapsed() > DEADLINE) break;
        it++;
        long long bc = BIGC * 4;
        int btype = -1, bt = -1, bg = -1, bt2 = -1;
        for (int s = 0; s < NSAMP; s++) {
            if (rnd_unit() < 0.8) {
                int t = rnd_int(T), g = rnd_int(G), old = dS[t];
                if (g == old) continue;
                dS[t] = g;
                long long c = eval_cost();
                dS[t] = old;
                if (tabu[(size_t)t * G + g] > it && c >= best) continue;
                if (c < bc || (c == bc && rnd_unit() < 0.5)) {
                    bc = c; btype = 0; bt = t; bg = g;
                }
            } else {
                if (K < 2) continue;
                int l = rnd_int(DEG), i1 = rnd_int(K), i2 = rnd_int(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                int x = dJ[t1], y = dJ[t2];
                dJ[t1] = y;
                dJ[t2] = x;
                long long c = eval_cost();
                dJ[t1] = x;
                dJ[t2] = y;
                if (c < bc || (c == bc && rnd_unit() < 0.5)) {
                    bc = c; btype = 1; bt = t1; bt2 = t2;
                }
            }
        }
        if (btype < 0) continue;
        if (btype == 0) {
            int old = dS[bt];
            tabu[(size_t)bt * G + old] = it + 8 + rnd_int(10);
            dS[bt] = bg;
        } else {
            int x = dJ[bt];
            dJ[bt] = dJ[bt2];
            dJ[bt2] = x;
        }
        cur = eval_cost();
        if (cur < best) {
            best = cur;
            stall = 0;
            save_state();
        } else {
            stall++;
        }
        if (stall > STALL && cur > 0) {
            restore_state();
            int nper = 2 + rnd_int(3);
            for (int k = 0; k < nper; k++) dS[rnd_int(T)] = rnd_int(G);
            cur = eval_cost();
            best = cur;
            stall = 0;
        }
    }

    if (cur == 0) {
        printf("%d %d\n", NV, T * G);
        for (int t = 0; t < T; t++) {
            for (int g = 0; g < G; g++) {
                int a = dI[t] * G + g;
                int b = (K + dJ[t]) * G + mt[g * G + dS[t]];
                printf("%d %d\n", a, b);
            }
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _direct(a, b):
    """Multiplication of Z_a x Z_b, element (x, y) coded as x*b + y."""
    def mul(x, y):
        return ((x // b + y // b) % a) * b + (x % b + y % b) % b
    return mul


def _groups(G, rng):
    """Finite groups of order G as (name, mul): cyclic, direct products, semidirect products."""
    out = [("cyc", lambda x, y: (x + y) % G)]
    for a in range(2, G):
        if G % a == 0 and a <= G // a:
            out.append((f"dir{a}", _direct(a, G // a)))
    for k in range(2, G):
        if G % k or G // k < 2:
            continue
        m = G // k
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        for r in rng.sample(rs, min(2, len(rs))):
            _, mul, _ = lib.semidirect_group(m, k, r)
            out.append((f"sd{m}_{k}_{r}", mul))
    rng.shuffle(out)
    return out


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
            consider(*pg)

    if best_n >= lib.moore_bound(d, D) or d > 12:
        return best

    def left():
        return 0.88 * time_limit - (time.monotonic() - start) - 1.0

    rng = random.Random(seed)
    run = 0
    while left() > 2.0 and run < 10000:
        run += 1
        K = rng.choice((1, 1, 2, 2, 3, 4))
        if d * K > 96:
            continue
        # Target: the smallest group order giving a lift strictly larger than best_n.
        G = best_n // (2 * K) + 1
        if G > 1000:
            continue
        groups = _groups(G, rng)
        if not groups:
            continue
        _, mul = rng.choice(groups)
        pairs = [(x * G + y, mul(x, y)) for x in range(G) for y in range(G)]
        rem = left()
        slice_ = min(rem, max(3.0, rem / 3.0))
        try:
            out = lib.run_c(C_TABU, [d, D, seed * 1000 + run, f"{slice_:.2f}", K, G],
                            stdin_graph=(G, pairs), timeout=slice_ + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass
        if best_n >= lib.moore_bound(d, D):
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
