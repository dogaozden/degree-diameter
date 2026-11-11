import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift annealer over semidirect products Z_m x| Z_k2.
#
# Base graph: k blocks on side A and k blocks on side B, each block a copy of
# the group G (order m*k2). The graph is the union of d layers. Layer l pairs
# A-block i with B-block perm[l][i] and voltage S[l][i]: A(i,g) ~ B(j, g*s).
# Left multiplication is an automorphism, so the graph has diameter <= D iff
# every block representative (block b, identity) reaches every vertex within D
# steps. The cost is the number of missing (vertex, representative) pairs plus
# a penalty per duplicate (i, j, s) triple, which would create a multi-edge.
# Simulated annealing runs until cost 0 or the time limit.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, N_;
static int *mulT, *perm, *Sv, *nbr, *cntk;
static u64 *ra, *rb;
static const long long PEN = 30;

static void build_group(int m, int k2, int r) {
    G_ = m * k2;
    mulT = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    long long *pw = malloc(sizeof(long long) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * (long long)r) % m;
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G_; y++) {
            int c = y / k2, e = y % k2;
            long long A = ((long long)a + pw[b] * (long long)c) % m;
            mulT[(size_t)x * G_ + y] = (int)(A * k2 + (b + e) % k2);
        }
    }
    free(pw);
}

/* Layer l: A(i,g) -- B(perm[l][i], mul(g, S[l][i])). Each vertex gets one
   neighbour per layer, so the graph is d-regular and bipartite. */
static void build_nbr(void) {
    int d = d_, k = k_, G = G_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = perm[l * k + i], s = Sv[l * k + i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (k + j) * G + mulT[(size_t)g * G + s];
                nbr[(size_t)a * d + l] = b;
                nbr[(size_t)b * d + l] = a;
            }
        }
    }
}

static long long evalmiss(void) {
    int N = N_, d = d_, k = k_, D = D_, G = G_;
    build_nbr();
    u64 *cur = ra, *alt = rb;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int it = 0; it < D; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            const int *nb = nbr + (size_t)v * d;
            for (int t = 0; t < d; t++) x |= cur[nb[t]];
            alt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *tmp = cur; cur = alt; alt = tmp;
        if (!changed) break;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) miss += 2 * k - __builtin_popcountll(cur[v]);
    return miss;
}

static long long dupcount(void) {
    int k = k_, G = G_, d = d_;
    long long dup = 0;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int key = (i * k + perm[l * k + i]) * G + Sv[l * k + i];
            if (cntk[key]++) dup++;
        }
    }
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int key = (i * k + perm[l * k + i]) * G + Sv[l * k + i];
            cntk[key] = 0;
        }
    }
    return dup;
}

static long long fullcost(void) { return evalmiss() + PEN * dupcount(); }

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    int m = atoi(argv[5]), k2 = atoi(argv[6]), r = atoi(argv[7]), k = atoi(argv[8]);
    if (d < 1 || D < 1 || k < 1 || 2 * k > 64 || m < 1 || k2 < 1) { printf("0 0\n"); return 0; }
    long long Gl = (long long)m * k2;
    if (Gl < 2 || Gl > 3000) { printf("0 0\n"); return 0; }
    if (r < 0 || r >= m) r = 1 % m;

    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int t = 0; t < 20; t++) rnd();

    d_ = d; D_ = D; k_ = k;
    build_group(m, k2, r);
    N_ = 2 * k * G_;
    perm = malloc(sizeof(int) * (size_t)d * k);
    Sv = malloc(sizeof(int) * (size_t)d * k);
    nbr = malloc(sizeof(int) * (size_t)N_ * d);
    ra = malloc(sizeof(u64) * (size_t)N_);
    rb = malloc(sizeof(u64) * (size_t)N_);
    cntk = calloc((size_t)k * k * G_, sizeof(int));
    if (!perm || !Sv || !nbr || !ra || !rb || !cntk) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * k + i]; perm[l * k + i] = perm[l * k + j]; perm[l * k + j] = t;
        }
        for (int i = 0; i < k; i++) Sv[l * k + i] = rint_(G_);
    }

    const double T0 = 20.0, T1 = 0.3;
    double T = T0;
    clock_t c0 = clock();
    long long cost = fullcost();
    int found = (cost == 0);
    long long iters = 0;

    while (!found) {
        if ((iters & 255) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double frac = el / limit;
            T = T0 * pow(T1 / T0, frac);
        }
        iters++;

        if (k >= 2 && rint_(10) < 3) {
            int l = rint_(d), i1 = rint_(k), i2 = rint_(k);
            if (i1 == i2) continue;
            int *p = &perm[l * k];
            int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            long long nc = fullcost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            }
        } else {
            int idx = rint_(d * k);
            int old = Sv[idx];
            int nw = rint_(G_);
            if (nw == old) continue;
            Sv[idx] = nw;
            long long nc = fullcost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                Sv[idx] = old;
            }
        }
        if (cost == 0) found = 1;
    }

    if (!found) { printf("0 0\n"); return 0; }

    /* nbr was rebuilt by the evaluation that produced the accepted state. */
    long long me = (long long)k * G_ * d;
    printf("%d %lld\n", N_, me);
    for (int a = 0; a < k * G_; a++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", a, nbr[(size_t)a * d + l]);
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


def _group_for_order(G, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order G = m*k2, or None."""
    divs = [k2 for k2 in range(1, min(G, 40) + 1) if G % k2 == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        r = 1 if rng.random() < 0.3 else rng.choice(cands)
        return m, k2, r
    return None


KS = (2, 3, 4, 5, 6, 8)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    # Exact construction for D = 3 when d-1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in KS}
    wins = {k: 0 for k in KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(KS)
        return max(KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    deadline = t0 + max(1.0, time_limit - 4.0)
    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 2.5:
                break
            k = pick_k()
            n0 = best[0]
            Gmin = n0 // (2 * k) + 1          # smallest G with 2kG > n0
            G = Gmin + rng.randrange(0, 1 + Gmin // 40)
            if G > 3000:
                continue
            grp = _group_for_order(G, rng)
            if grp is None:
                continue
            m, k2, r = grp
            slice_t = min(remaining - 1.0, max(4.0, min(10.0, remaining / 4.0)))
            if slice_t < 1.0:
                break
            trials[k] += 1
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, rng.randrange(1, 1 << 30), f"{slice_t:.2f}", m, k2, r, k],
                    timeout=slice_t + 10.0,
                )
                n, e = lib.parse_graph_text(out)
            except Exception:
                continue
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                wins[k] += 1
    except Exception:
        pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
