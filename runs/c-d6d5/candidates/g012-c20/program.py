import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over an explicitly supplied finite group.
#
# The group is passed on stdin as its full multiplication table (element 0 is
# the identity). A lift has K A-blocks and K B-blocks, each of order G, with
# DEG layers. Layer l is a permutation p_l of the K blocks plus one voltage
# per block pair, so every vertex has degree DEG. Dart t = (i, j, s) joins
# A_{i,g} to B_{j, g*s} for all g. Left multiplication is an automorphism, so
# diameter <= D iff BFS of depth D from each of the 2K block identities covers
# the graph.
#
# Search: simulated annealing on the weighted count of uncovered pairs, with
# breakout weights (raised when the true cost stalls), restarts from random
# configurations, and iterated local search from the best configuration of
# earlier runs.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define ITERS 6000
#define ILS_ITERS 3000
#define BRK 150
#define KMAX 8

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

static int DEG, DIAM, K, G, T, N;
static int *mulT;
static int *dI, *dJ, *dS, *bestJ, *bestS, *eJ, *eS;
static int *adj, *cnt, *stamp, *fr, *nx;
static int curstamp = 0;
static long long *wt, *unc;
static long long wsum_w = 0, last_w = 0;

static void zero_unc(void) {
    for (int r = 0; r < 2 * K; r++) unc[r] = 0;
}

/* Returns the true cost (uncovered ordered pairs from the 2K block identities).
   Sets unc[] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                zero_unc();
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int t = 0; t < T; t++) {
        int ai = dI[t] * G, bj = (K + dJ[t]) * G, s = dS[t];
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + mulT[g * G + s];
            if (cnt[a] >= DEG || cnt[b] >= DEG) {
                zero_unc();
                last_w = BIGC;
                return BIGC;
            }
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)N);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                for (int e = 0; e < DEG; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = N - count;
        total += N - count;
    }
    long long w = 0;
    for (int r = 0; r < 2 * K; r++) w += wt[r] * unc[r];
    last_w = w;
    return total;
}

static void random_init(void) {
    int p[KMAX];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            dI[t] = i;
            dJ[t] = p[i];
            dS[t] = rnd_int(G);
        }
    }
}

/* Random kicks: within-layer target swaps and voltage changes. */
static void perturb(int nm) {
    for (int s = 0; s < nm; s++) {
        if (K > 1 && rnd_unit() < 0.3) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(T);
            dS[t] = rnd_int(G);
        }
    }
}

/* Annealing on the weighted cost with breakout weight bumps.
   The caller must have just called eval_cost() on the start state.
   Best state by true cost goes to bestJ/bestS. Returns the best true cost. */
static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost;
    long long wcur = last_w;
    long long prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
    memcpy(bestS, dS, sizeof(int) * (size_t)T);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < 2 * K; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < 2 * K; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (2.0 * K);
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (K > 1 && rnd_unit() < 0.25) {
            int l = rnd_int(DEG);
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(T);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2;
                wcur = w2;
            } else {
                dS[t] = olds;
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)T);
            memcpy(bestS, dS, sizeof(int) * (size_t)T);
        }
    }
    return bestc;
}

static void emit(const int *J, const int *S) {
    printf("%d %d\n", N, T * G);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++)
            printf("%d %d\n", dI[t] * G + g, (K + J[t]) * G + mulT[g * G + S[t]]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit K  (group table on stdin)\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    K = atoi(argv[5]);
    if (DEG < 1 || DIAM < 1 || K < 1 || K > KMAX) {
        printf("0 0\n");
        return 0;
    }

    int gn = 0, gm = 0;
    if (scanf("%d %d", &gn, &gm) != 2 || gn < 1 || gm != gn * gn) {
        printf("0 0\n");
        return 0;
    }
    G = gn;
    mulT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int i = 0; i < gm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || u >= G * G || v < 0 || v >= G) {
            printf("0 0\n");
            return 0;
        }
        mulT[u] = v;
    }

    N = 2 * K * G;
    T = DEG * K;
    dI = malloc(sizeof(int) * (size_t)T);
    dJ = malloc(sizeof(int) * (size_t)T);
    dS = malloc(sizeof(int) * (size_t)T);
    bestJ = malloc(sizeof(int) * (size_t)T);
    bestS = malloc(sizeof(int) * (size_t)T);
    eJ = malloc(sizeof(int) * (size_t)T);
    eS = malloc(sizeof(int) * (size_t)T);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * (size_t)N);
    stamp = calloc((size_t)N, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)N);
    nx = malloc(sizeof(int) * (size_t)N);
    wt = malloc(sizeof(long long) * (size_t)(2 * K));
    unc = malloc(sizeof(long long) * (size_t)(2 * K));
    for (int t = 0; t < T; t++) dI[t] = t % K;

    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int have = 0;
    long long ecost = BIGC;
    while (elapsed() < DEADLINE) {
        long long cost, bc;
        for (int r = 0; r < 2 * K; r++) wt[r] = 1;
        wsum_w = 2 * K;
        if (have && rnd_unit() < 0.5) {
            memcpy(dJ, eJ, sizeof(int) * (size_t)T);
            memcpy(dS, eS, sizeof(int) * (size_t)T);
            perturb(2 + rnd_int(4));
            cost = eval_cost();
            bc = run_sa(ILS_ITERS, 0.35, cost);
        } else {
            random_init();
            cost = eval_cost();
            bc = run_sa(ITERS, 1.0, cost);
        }
        if (bc == 0) {
            emit(bestJ, bestS);
            return 0;
        }
        if (bc < ecost) {
            ecost = bc;
            have = 1;
            memcpy(eJ, bestJ, sizeof(int) * (size_t)T);
            memcpy(eS, bestS, sizeof(int) * (size_t)T);
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python side: group tables, candidate pool, safe fallbacks, driver.
# ----------------------------------------------------------------------------

def _is_prime(p):
    return p >= 2 and all(p % r for r in range(2, int(p ** 0.5) + 1))


def _prime_factors(n):
    f, x, p = [], n, 2
    while p * p <= x:
        if x % p == 0:
            f.append(p)
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        f.append(x)
    return f


def _primitive_root(p):
    fs = _prime_factors(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fs):
            return g
    raise ValueError("no primitive root")


def _groups_of_order(G):
    """Descriptions of several group families of order G (identity is element 0 in each)."""
    descs = [("cyc", G)]
    for a in range(2, G):
        if G % a == 0 and a * a <= G and G // a >= 2:
            descs.append(("ab", a, G // a))
    for k in range(2, G):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        found = 0
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                descs.append(("sd", m, k, r))
                found += 1
                if found >= 2:
                    break
    for p in range(3, G + 1):
        if G % p == 0 and _is_prime(p):
            k = G // p
            if k >= 2 and (p - 1) % k == 0:
                descs.append(("aff", p, k))
    return descs


def _group_mul(desc):
    kind = desc[0]
    if kind == "cyc":
        G = desc[1]
        return G, (lambda x, y: (x + y) % G)
    if kind == "ab":
        a, b = desc[1], desc[2]
        return a * b, (lambda x, y: ((x // b + y // b) % a) * b + (x % b + y % b) % b)
    if kind == "sd":
        G, mulf, _ = lib.semidirect_group(desc[1], desc[2], desc[3])
        return G, mulf
    if kind == "aff":
        # Maps x -> a*x + b over Z_p with a in the subgroup H of order k; element (a_index, b).
        p, k = desc[1], desc[2]
        g = _primitive_root(p)
        H = [pow(g, j * (p - 1) // k, p) for j in range(k)]
        hidx = {h: i for i, h in enumerate(H)}

        def mulf(x, y):
            ai, b = divmod(x, p)
            aj, c = divmod(y, p)
            return hidx[H[ai] * H[aj] % p] * p + (H[ai] * c + b) % p

        return p * k, mulf
    raise ValueError(f"unknown group {desc}")


def _mul_table(desc):
    """Return (G, edges) where edges encodes the multiplication table as pairs (x*G+y, x*y)."""
    G, mulf = _group_mul(desc)
    if any(mulf(0, y) != y or mulf(y, 0) != y for y in range(G)):
        raise ValueError("identity is not element 0")
    rng = random.Random(12345)
    for _ in range(300):
        x, y, z = rng.randrange(G), rng.randrange(G), rng.randrange(G)
        if mulf(mulf(x, y), z) != mulf(x, mulf(y, z)):
            raise ValueError("not associative")
    edges = []
    for x in range(G):
        for y in range(G):
            v = mulf(x, y)
            if not 0 <= v < G:
                raise ValueError("product out of range")
            edges.append((x * G + y, v))
    return G, edges


def _pool(best_n, rng):
    """Candidate (K, G, group) triples whose lift order 2KG beats best_n, mixed by order."""
    pool = []
    for K in (1, 2, 3):
        lo = best_n // (2 * K) + 1
        spread = max(3, lo // 15)
        for G in range(lo, lo + spread):
            for desc in _groups_of_order(G):
                pool.append((2 * K * G + rng.uniform(0, 60), K, G, desc))
    pool.sort(key=lambda t: t[0])
    return [(K, G, desc) for _, K, G, desc in pool]


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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    end = start + 0.80 * time_limit - 1.0
    rng = random.Random(1000003 * seed + 97 * d + D)
    pool = _pool(best_n, rng)
    target_runs = 6
    runs = 0
    for K, G, desc in pool:
        if 2 * K * G <= best_n:
            continue
        if runs >= 12:
            break
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        left = max(1, target_runs - runs)
        slice_s = min(remaining, max(2.0, remaining / left))
        try:
            Gc, edges = _mul_table(desc)
            if Gc != G:
                continue
            out = lib.run_c(C_SOURCE, [d, D, seed * 1000 + runs, f"{slice_s:.2f}", K],
                            stdin_graph=(G, edges), timeout=slice_s + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass
        runs += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
