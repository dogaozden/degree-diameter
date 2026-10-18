import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

/*
 * Bi-Cayley lift search over Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).
 * Base: k A-blocks and k B-blocks, d layers. Layer l pairs A_i with B_{layers[l][i]}
 * through voltage S[l][i]: A_{i,g} ~ B_{p,g*s}. Every vertex gets degree d.
 *
 * Search: simulated annealing with defect-targeted voltage moves and layer swaps.
 * Restarts are iterated local search: half of the restarts perturb the elite
 * (lowest-cost) state found so far instead of starting from random voltages.
 * Diameter is checked on the 2k block representatives, using left-multiplication
 * automorphisms.
 */

#define MAXD 64
#define MAXK 8
#define MAXK2 64
#define PEN 1000LL
#define ITERS 3000
#define PATIENCE 900
#define MAXG 200000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d, D, k, m, k2, r, G, N;
static int pw[MAXK2];
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int eL[MAXD][MAXK];
static int eS[MAXD][MAXK];
static int *nbr;
static uint32_t *curr, *cand, *scratch;
static int pc16[1 << 16];
static uint32_t FULL;

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_(long long b, long long e, long long mod) {
    long long res = 1 % mod;
    b %= mod;
    while (e > 0) {
        if (e & 1) res = res * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return res;
}

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long A = ((long long)a + (long long)pw[b] * (long long)c) % m;
    int B = (b + e) % k2;
    return (int)A * k2 + B;
}

/* Layer l: A_{i,g} ~ B_{p,g*s}, with p = layers[l][i], s = S[l][i]. */
static void rebuild_layer(int l) {
    int *nb = nbr + (size_t)l * (size_t)N;
    for (int i = 0; i < k; i++) {
        int p = layers[l][i];
        int s = S[l][i];
        for (int g = 0; g < G; g++) {
            int u = i * G + g;
            int v = (k + p) * G + gmul(g, s);
            nb[u] = v;
            nb[v] = u;
        }
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < k; i++) S[l][i] = rint_(G);
        rebuild_layer(l);
    }
}

/* R[v] bit b set iff block representative b is within distance D of vertex v. */
static void eval_reach(uint32_t *R) {
    int NB = 2 * k;
    for (int v = 0; v < N; v++) R[v] = 0;
    for (int b = 0; b < NB; b++) R[b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = R[v];
            for (int l = 0; l < d; l++) x |= R[nbr[(size_t)l * N + v]];
            scratch[v] = x;
            if (x != R[v]) changed = 1;
        }
        memcpy(R, scratch, sizeof(uint32_t) * (size_t)N);
        if (!changed) break;
    }
}

static long long cost_of(const uint32_t *R) {
    long long covered = 0;
    for (int v = 0; v < N; v++) covered += pc16[R[v]];
    long long unr = (long long)(2 * k) * (long long)N - covered;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int a = 0; a < d; a++)
            for (int b2 = a + 1; b2 < d; b2++)
                if (layers[a][i] == layers[b2][i] && S[a][i] == S[b2][i]) dup++;
    return unr + PEN * dup;
}

static void print_graph(void) {
    printf("%d %d\n", N, k * G * d);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N + u]);
}

static void fail_exit(void) {
    printf("0 0\n");
}

int main(int argc, char **argv) {
    if (argc < 9) { fail_exit(); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    r = atoi(argv[8]);

    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > MAXK2) {
        fail_exit();
        return 0;
    }
    r %= m;
    if (r < 0) r += m;
    if (gcd_(r, m) != 1 || powmod_(r, k2, m) != 1 % m) { fail_exit(); return 0; }
    G = m * k2;
    if (G > MAXG) { fail_exit(); return 0; }
    N = 2 * k * G;

    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);

    nbr = (int *)malloc(sizeof(int) * (size_t)d * (size_t)N);
    curr = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)N);
    cand = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)N);
    scratch = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)N);
    if (!nbr || !curr || !cand || !scratch) { fail_exit(); return 0; }
    FULL = (1u << (2 * k)) - 1u;
    pc16[0] = 0;
    for (int x = 1; x < (1 << 16); x++) pc16[x] = pc16[x >> 1] + (x & 1);

    rs = (uint64_t)seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int have_elite = 0;
    long long ecost = 0;

    while (cpu() < tl) {
        if (have_elite && rint_(2) == 0) {
            memcpy(layers, eL, sizeof(layers));
            memcpy(S, eS, sizeof(S));
            int np = 2 + rint_(3);
            for (int j = 0; j < np; j++) {
                int l = rint_(d), i = rint_(k);
                S[l][i] = rint_(G);
            }
            for (int l = 0; l < d; l++) rebuild_layer(l);
        } else {
            random_state();
        }

        eval_reach(curr);
        long long cost = cost_of(curr);
        long long best_here = cost;
        int last_imp = 0;
        double c0 = (double)(cost > 1 ? cost : 1);

        for (int t = 0; t < ITERS && cost != 0; t++) {
            if (cpu() >= tl) break;
            if (t - last_imp > PATIENCE) break;
            double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
            if (temp < 0.5) temp = 0.5;

            if (k >= 2 && rdbl() < 0.25) {
                /* Layer-swap move. */
                int l = rint_(d);
                int i1 = rint_(k);
                int i2 = rint_(k - 1);
                if (i2 >= i1) i2++;
                int tv = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tv;
                rebuild_layer(l);
                eval_reach(cand);
                long long c2 = cost_of(cand);
                if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
                    memcpy(curr, cand, sizeof(uint32_t) * (size_t)N);
                    cost = c2;
                    if (cost < best_here) { best_here = cost; last_imp = t; }
                } else {
                    tv = layers[l][i1];
                    layers[l][i1] = layers[l][i2];
                    layers[l][i2] = tv;
                    rebuild_layer(l);
                }
                continue;
            }

            /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
            int l = -1, i = -1;
            if (rdbl() < 0.4) {
                int nbad = 0, pickv = -1;
                for (int v = 0; v < N; v++) {
                    if (curr[v] != FULL) {
                        nbad++;
                        if (rint_(nbad) == 0) pickv = v;
                    }
                }
                if (pickv >= 0) {
                    int blk = pickv / G;
                    l = rint_(d);
                    if (blk < k) {
                        i = blk;
                    } else {
                        int p = blk - k;
                        for (int j = 0; j < k; j++)
                            if (layers[l][j] == p) { i = j; break; }
                    }
                }
            }
            if (i < 0) {
                l = rint_(d);
                i = rint_(k);
            }

            int old = S[l][i];
            int nw = rint_(G);
            if (nw == old) continue;
            S[l][i] = nw;
            rebuild_layer(l);
            eval_reach(cand);
            long long c2 = cost_of(cand);
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
                memcpy(curr, cand, sizeof(uint32_t) * (size_t)N);
                cost = c2;
                if (cost < best_here) { best_here = cost; last_imp = t; }
            } else {
                S[l][i] = old;
                rebuild_layer(l);
            }
        }

        if (cost == 0) {
            print_graph();
            return 0;
        }
        if (!have_elite || cost < ecost) {
            memcpy(eL, layers, sizeof(layers));
            memcpy(eS, S, sizeof(S));
            ecost = cost;
            have_elite = 1;
        }
    }

    fail_exit();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: exact constructions, group sampling, and the time-sliced driver.
# ----------------------------------------------------------------------------

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
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral type
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    # Leave a margin for compilation, parsing and the final validity check.
    end = t0 + max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Time-sliced lift search. Each slice is one C run for a sampled (k, group).
    ks = (1, 2, 3, 4, 5, 6)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining, max(3.0, min(8.0, remaining / 3.0)))

        k = pick_k()
        base = best[0] // (2 * k)
        # Group-order window widened to about +35% above the current base order.
        lo = base + 1
        hi = int(base * 1.35) + 3
        target = rng.randint(lo, max(lo, hi))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue

        trials[k] += 1
        try:
            text = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1 << 30), f"{slice_s:.2f}", k, m, k2, r],
                timeout=slice_s + 5.0,
            )
            n, e = lib.parse_graph_text(text)
        except (RuntimeError, ValueError):
            continue
        if n > 0 and n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
