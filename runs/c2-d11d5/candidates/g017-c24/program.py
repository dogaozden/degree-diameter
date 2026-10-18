"""Bold rewrite: the bi-Cayley lift search now runs entirely in C.

Each call to the C engine fixes a base size k and a semidirect group Z_m x| Z_k2 (with
r^k2 = 1 mod m). It then runs simulated annealing over layer permutations and voltages.
Acceptance requires every pair to be within distance D, checked by BFS from one
representative per block (both groups act transitively on each block). Python ratchets
the target order and passes the best valid result to lib.is_valid.

The fallback is K_{d,d}, or a projective-plane / Araujo-Pardo-Lopez construction when
applicable. Every returned graph is checked with lib.is_valid.
"""
import math
import random
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley voltage-lift annealing over G = Z_M x|_R Z_K2 with K base blocks per side.
 * Usage: prog d D seed time_limit K M K2 R
 * Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h.
 * Layer l joins A_i to B_{perm[l][i]} with A_{i,g} ~ B_{perm[l][i], g*volt[l][i]}.
 * Stdout: "N E" plus the edges of a valid graph, or "0 0".
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 6
#define MAXG 12000
#define MAXN 24000
#define PATIENCE 15000

static int d, D, K, M, K2, R, G, N;
static int pw[64];
static int perm[MAXD][MAXK], iperm[MAXD][MAXK];
static int volt[MAXD][MAXK], vinv[MAXD][MAXK];
static int stampv[MAXN], queuev[MAXN];
static int curstamp = 0;
static uint64_t rs = 88172645463325252ULL;
static const long PEN = 50000L;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int mulg(int x, int y) {
    int a1 = x / K2, b1 = x % K2, a2 = y / K2, b2 = y % K2;
    int a = (int)((a1 + (long)pw[b1] * a2) % M);
    int b = (b1 + b2) % K2;
    return a * K2 + b;
}

static int invg(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int na = (int)((M - (long)pw[nb] * a % M) % M);
    return na * K2 + nb;
}

/* Neighbour of v in layer l. */
static int neighbor(int v, int l) {
    int KG = K * G;
    if (v < KG) {
        int i = v / G, g = v % G;
        int j = perm[l][i];
        return (K + j) * G + mulg(g, volt[l][i]);
    } else {
        int idx = v - KG;
        int j = idx / G, h = idx % G;
        int i = iperm[l][j];
        return i * G + mulg(h, vinv[l][i]);
    }
}

/* Number of vertices NOT reached within distance D from src. */
static long bfs_unreached(int src) {
    curstamp++;
    int head = 0, tail = 0;
    queuev[tail++] = src;
    stampv[src] = curstamp;
    for (int lev = 0; lev < D && head < tail && tail < N; lev++) {
        int end = tail;
        while (head < end) {
            int v = queuev[head++];
            for (int l = 0; l < d; l++) {
                int w = neighbor(v, l);
                if (stampv[w] != curstamp) {
                    stampv[w] = curstamp;
                    queuev[tail++] = w;
                }
            }
        }
    }
    return (long)(N - tail);
}

/* Duplicate parallel edges: same block i with same (j, voltage) in two layers. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][i] == perm[l2][i] && volt[l][i] == volt[l2][i]) c++;
    return c;
}

static long cost_full(void) {
    long c = 0;
    for (int i = 0; i < K; i++) c += bfs_unreached(i * G);
    for (int j = 0; j < K; j++) c += bfs_unreached((K + j) * G);
    return c + PEN * dup_count();
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) iperm[l][perm[l][i]] = i;
        for (int i = 0; i < K; i++) {
            volt[l][i] = rndi(G);
            vinv[l][i] = invg(volt[l][i]);
        }
    }
}

static int search(double deadline) {
    while (now() < deadline) {
        random_init();
        long cur = cost_full();
        double T0 = 2.0 + 0.02 * (double)cur;
        long best = cur, last = 0;
        for (long it = 1;; it++) {
            if (cur == 0) return 1;
            if ((it & 15) == 0 && now() > deadline) return 0;
            if (it - last > PATIENCE) break;
            double T = T0 * exp(-(double)it / 4000.0);
            if (T < 0.2) T = 0.2;

            int l = rndi(d);
            int bp[MAXK], bi[MAXK], bv[MAXK], bvi[MAXK];
            memcpy(bp, perm[l], sizeof bp);
            memcpy(bi, iperm[l], sizeof bi);
            memcpy(bv, volt[l], sizeof bv);
            memcpy(bvi, vinv[l], sizeof bvi);

            if (K >= 2 && rnd01() < 0.3) {
                int i1 = rndi(K), i2 = rndi(K - 1);
                if (i2 >= i1) i2++;
                int j1 = perm[l][i1], j2 = perm[l][i2];
                perm[l][i1] = j2;
                perm[l][i2] = j1;
                iperm[l][j2] = i1;
                iperm[l][j1] = i2;
            } else {
                int i = rndi(K), s = rndi(G);
                volt[l][i] = s;
                vinv[l][i] = invg(s);
            }

            long nc = cost_full();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < best) {
                    best = cur;
                    last = it;
                }
            } else {
                memcpy(perm[l], bp, sizeof bp);
                memcpy(iperm[l], bi, sizeof bi);
                memcpy(volt[l], bv, sizeof bv);
                memcpy(vinv[l], bvi, sizeof bvi);
            }
        }
    }
    return 0;
}

static void print_graph(void) {
    int KG = K * G;
    long m = (long)KG * d;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < KG; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, neighbor(v, l));
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 1 || d > MAXD || D < 2 || K < 1 || K > MAXK || M < 2 || K2 < 1 || K2 > 40) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * K * G;
    if (G > MAXG || N > MAXN) {
        printf("0 0\n");
        return 0;
    }
    R %= M;
    if (R < 0) R += M;
    pw[0] = 1 % M;
    for (int t = 1; t <= K2; t++) pw[t] = (int)((long)pw[t - 1] * R % M);
    if (pw[K2] != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    double deadline = now() + limit * 0.95 - 0.1;
    if (search(deadline)) {
        print_graph();
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _run_lift(d, D, k, m, k2, r, seed, budget):
    """Run the C lift annealer once. Returns (n, edges) or None."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), k, m, k2, r],
                         stdin_graph=None, timeout=budget + 15.0)
        n, edges = lib.parse_graph_text(text)
    except Exception:
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best  # K_{d,d} is optimal for diameter 2

    # Exact constructions.
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    except Exception:
        pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bold change: all lift search happens in C, with the target order ratcheted upward.
    lift_end = final - 1.0
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = float(best_n) * 1.02

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.5:
            break
        k = pick_k()
        target = max(2, int(goal // (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(best_n * 1.02, goal * 0.99)
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            goal = max(goal, best_n * 1.02)
            continue
        budget = min(remaining, min(8.0, max(2.0, 0.3 * remaining)))
        trials[k] += 1
        res = _run_lift(d, D, k, m, k2, r, rng.randrange(1 << 30), budget)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
            goal = max(goal, res[0] * 1.04)
        else:
            goal = max(best_n * 1.02, goal * 0.99)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
