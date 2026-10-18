import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over voltage lifts of a bipartite base with k vertices
# per side, over the semidirect product Z_m x|_r Z_k2 (order G = m*k2).
#
# Layer l pairs A-index i with B-index sig[l][i] (sig[l] is a permutation) and
# voltage sv[l][i]. A-vertex (i, x) joins B-vertex (sig, x*s). This is a
# d-regular bipartite graph on 2*k*G vertices. G acts on each block by left
# multiplication, so the diameter check needs only BFS from the 2k block
# representatives. Cost = total unreached pairs over those BFS runs + a
# penalty for duplicate edges. Cost 0 means valid, and the graph is printed.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 12
#define MAXG 2500

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d, D, k, G, m, k2, r, N;
static int *mt, *iv, *pw, *nb, *stamp, *queue;
static int curstamp = 0;
static int sig[MAXD][MAXK], isig[MAXD][MAXK], sv[MAXD][MAXK];

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    int a2 = (int)(((long long)a + (long long)pw[b] * c) % m);
    int b2 = (b + e) % k2;
    return a2 * k2 + b2;
}

static int build_group(void) {
    G = m * k2;
    if (m < 1 || k2 < 1 || G < 2 || G > MAXG) return 0;
    pw = malloc(sizeof(int) * (size_t)k2);
    if (!pw) return 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
    if ((((long long)pw[k2 - 1] * r) % m) != (1 % m)) return 0;
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    iv = malloc(sizeof(int) * (size_t)G);
    if (!mt || !iv) return 0;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[x * G + y] = gmul(x, y);
    for (int y = 0; y < G; y++) if (mt[y] != y) return 0;  /* identity is 0 */
    for (int x = 0; x < G; x++) {
        int found = -1;
        for (int y = 0; y < G; y++) if (mt[x * G + y] == 0) { found = y; break; }
        if (found < 0) return 0;
        iv[x] = found;
    }
    return 1;
}

static void fix_inv(int l) {
    for (int i = 0; i < k; i++) isig[l][sig[l][i]] = i;
}

/* Fill nb[v*d + l] = neighbour of v in layer l. */
static void make_adj(void) {
    for (int i = 0; i < k; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < d; l++) {
                int j = sig[l][i];
                nb[v * d + l] = (k + j) * G + mt[x * G + sv[l][i]];
            }
        }
    for (int j = 0; j < k; j++)
        for (int y = 0; y < G; y++) {
            int v = (k + j) * G + y;
            for (int l = 0; l < d; l++) {
                int i = isig[l][j];
                int s = sv[l][i];
                nb[v * d + l] = i * G + mt[y * G + iv[s]];
            }
        }
}

/* Number of vertices within distance D of src (including src). */
static int bfs_count(int src) {
    curstamp++;
    int head = 0, tail = 0;
    queue[tail++] = src;
    stamp[src] = curstamp;
    int depth = 0;
    while (head < tail && depth < D) {
        int levelEnd = tail;
        while (head < levelEnd) {
            int v = queue[head++];
            for (int l = 0; l < d; l++) {
                int u = nb[v * d + l];
                if (stamp[u] != curstamp) {
                    stamp[u] = curstamp;
                    queue[tail++] = u;
                }
            }
        }
        depth++;
    }
    return tail;
}

static long long evaluate(void) {
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l][i] == sig[l2][i] && sv[l][i] == sv[l2][i]) dup++;
    make_adj();
    long long unr = 0;
    for (int b = 0; b < 2 * k; b++) unr += (long long)(N - bfs_count(b * G));
    return unr + 1000LL * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    m = atoi(argv[5]);
    k2 = atoi(argv[6]);
    r = atoi(argv[7]);
    k = atoi(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 1 || k2 < 1
        || r < 0 || (m > 1 && r >= m) || (long long)m * k2 > MAXG) {
        printf("0 0\n");
        return 0;
    }
    if (!build_group()) { printf("0 0\n"); return 0; }
    N = 2 * k * G;
    nb = malloc(sizeof(int) * (size_t)N * (size_t)d);
    stamp = calloc((size_t)N, sizeof(int));
    queue = malloc(sizeof(int) * (size_t)N);
    if (!nb || !stamp || !queue) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k; i++) {
            sig[l][i] = p[i];
            sv[l][i] = rint_(G);
        }
        fix_inv(l);
    }

    clock_t c0 = clock();
    long long cost = evaluate();
    const double T0 = 40.0, T1 = 0.2;
    while (cost != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        if (k >= 2 && rint_(2) == 0) {
            int l = rint_(d), i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int t = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t;
            fix_inv(l);
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t;
                fix_inv(l);
            }
        } else {
            int l = rint_(d), i = rint_(k);
            int old = sv[l][i];
            int nw = rint_(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                sv[l][i] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    long long M = (long long)k * G * d;
    printf("%d %lld\n", N, M);
    for (int i = 0; i < k; i++)
        for (int x = 0; x < G; x++)
            for (int l = 0; l < d; l++) {
                int u = i * G + x;
                int v = (k + sig[l][i]) * G + mt[x * G + sv[l][i]];
                printf("%d %d\n", u, v);
            }
    return 0;
}
"""


_KS = (1, 2, 3, 4, 5, 6)
_MAX_G = 2000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 of order m*k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if m * k2 > _MAX_G:
            continue
        if k2 == 1 or rng.random() < 0.4:
            return m, k2, 1
        if k2 % 2 == 0 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
            continue
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid safe fallback for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum for this calibration case

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    end = t0 + max(1.0, 0.9 * time_limit - 2.0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    errors = 0

    while errors < 3:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break

        if rng.random() < 0.25:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.05 * rng.random())

        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 16 + 2)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        n_new = 2 * k * m * k2
        if n_new <= best[0]:
            continue

        budget = min(remaining - 0.5, max(1.0, min(10.0, 0.5 + n_new / 150.0)))
        if budget < 0.5:
            break

        trials[k] += 1
        try:
            out = lib.run_c(LIFT_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", m, k2, r, k],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            errors += 1
            continue
        if n > 0:
            wins[k] += 1
        consider(n, e)

    return best
