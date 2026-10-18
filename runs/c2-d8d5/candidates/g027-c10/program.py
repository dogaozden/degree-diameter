import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# A lift has K base vertices per side and DG layers. Layer l sends A-vertex i
# to B-vertex sig[l][i] with voltage volt[l][i] in a finite group G = GM x| GK
# (element a*GK+b, product (a,b)(c,d) = (a + r^b c, b + d)). The lift has
# vertices A(i,x) and B(j,y), with edge A(i,x)-B(j, x*s) for each dart.
# Left multiplication is an automorphism, so distances from the 2K sources
# A(i,e), B(j,e) determine validity. The cost is the number of unreached
# (source, vertex) pairs plus a penalty per duplicate dart. Cost 0 means a
# valid d-regular bipartite graph of diameter <= D on 2*K*G vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
#define PENALTY 1000LL

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, DIAM, DG, GM, GK, GR, G, NV;
static int *mulT, *invT, *PW;
static int *sig, *tau, *volt;
static int *dist, *qu;

static int gmul_slow(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, d = y % GK;
    long long p = PW[b];
    long long aa = ((long long)a + p * (long long)c) % GM;
    return (int)(aa * GK + (b + d) % GK);
}

static int ginv_slow(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long long v = (-((long long)PW[nb] * a)) % GM;
    if (v < 0) v += GM;
    return (int)(v * GK + nb);
}

static void random_state(void) {
    int *perm = malloc(sizeof(int) * (size_t)K);
    for (int l = 0; l < DG; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            sig[l * K + i] = perm[i];
            tau[l * K + perm[i]] = i;
            volt[l * K + i] = rint_(G);
        }
    }
    free(perm);
}

static void swap_sig(int l, int i1, int i2) {
    int a = sig[l * K + i1], b = sig[l * K + i2];
    sig[l * K + i1] = b;
    sig[l * K + i2] = a;
    tau[l * K + a] = i2;
    tau[l * K + b] = i1;
}

static long long dupcount(void) {
    long long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DG; l++)
            for (int l2 = l + 1; l2 < DG; l2++)
                if (sig[l * K + i] == sig[l2 * K + i] && volt[l * K + i] == volt[l2 * K + i])
                    c++;
    return c;
}

static long long unreached_sum(void) {
    long long tot = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = s * G;
        for (int v = 0; v < NV; v++) dist[v] = -1;
        int h = 0, t = 0, seen = 1;
        qu[t++] = src;
        dist[src] = 0;
        while (h < t) {
            int v = qu[h++];
            int dv = dist[v];
            if (dv >= DIAM) continue;
            if (v < K * G) {
                int i = v / G, x = v - i * G;
                for (int l = 0; l < DG; l++) {
                    int idx = l * K + i;
                    int u = (K + sig[idx]) * G + mulT[x * G + volt[idx]];
                    if (dist[u] < 0) { dist[u] = dv + 1; qu[t++] = u; seen++; }
                }
            } else {
                int bq = v / G;
                int jj = bq - K;
                int y = v - bq * G;
                for (int l = 0; l < DG; l++) {
                    int i = tau[l * K + jj];
                    int u = i * G + mulT[y * G + invT[volt[l * K + i]]];
                    if (dist[u] < 0) { dist[u] = dv + 1; qu[t++] = u; seen++; }
                }
            }
        }
        tot += NV - seen;
    }
    return tot;
}

static void output_solution(void) {
    int E = K * DG * G;
    printf("%d %d\n", NV, E);
    for (int l = 0; l < DG; l++) {
        for (int i = 0; i < K; i++) {
            int idx = l * K + i;
            int j = sig[idx], s = volt[idx];
            for (int x = 0; x < G; x++) {
                int u = i * G + x;
                int v = (K + j) * G + mulT[x * G + s];
                printf("%d %d\n", u, v);
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    GM = atoi(argv[4]);
    GK = atoi(argv[5]);
    GR = atoi(argv[6]);
    u64 seed = (u64)strtoull(argv[7], NULL, 10);
    double limit = atof(argv[8]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 10; w++) rnd();

    if (DG < 1 || DG > 64 || DIAM < 1 || K < 1 || K > 64 || GM < 1 || GK < 1) {
        printf("0 0\n");
        return 0;
    }
    G = GM * GK;
    if (G < 2 || G > 2000 || GR < 0 || GR >= GM) { printf("0 0\n"); return 0; }
    NV = 2 * K * G;

    sig = malloc(sizeof(int) * (size_t)DG * K);
    tau = malloc(sizeof(int) * (size_t)DG * K);
    volt = malloc(sizeof(int) * (size_t)DG * K);
    dist = malloc(sizeof(int) * (size_t)NV);
    qu = malloc(sizeof(int) * (size_t)NV);
    PW = malloc(sizeof(int) * (size_t)GK);
    mulT = malloc(sizeof(int) * (size_t)G * G);
    invT = malloc(sizeof(int) * (size_t)G);
    if (!sig || !tau || !volt || !dist || !qu || !PW || !mulT || !invT) {
        printf("0 0\n");
        return 0;
    }

    PW[0] = 1 % GM;
    for (int b = 1; b < GK; b++) PW[b] = (int)(((long long)PW[b - 1] * GR) % GM);
    if ((((long long)PW[GK - 1] * GR) % GM) != (1 % GM)) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[x * G + y] = gmul_slow(x, y);
    for (int x = 0; x < G; x++) invT[x] = ginv_slow(x);
    for (int x = 0; x < G; x++) {
        if (mulT[x] != x || mulT[x * G] != x || mulT[x * G + invT[x]] != 0) {
            printf("0 0\n");
            return 0;
        }
    }

    random_state();
    clock_t c0 = clock();
    long long cur = unreached_sum() + PENALTY * dupcount();
    const double T0 = 4.0, T1 = 0.12;

    while (cur != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        if (K >= 2 && rdbl() < 0.3) {
            int l = rint_(DG), i1 = rint_(K), i2 = rint_(K);
            if (i1 == i2) continue;
            swap_sig(l, i1, i2);
            long long nc = unreached_sum() + PENALTY * dupcount();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                swap_sig(l, i1, i2);
            }
        } else {
            int l = rint_(DG), i = rint_(K);
            int idx = l * K + i;
            int old = volt[idx];
            int nv = rint_(G);
            if (nv == old) continue;
            volt[idx] = nv;
            long long nc = unreached_sum() + PENALTY * dupcount();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                volt[idx] = old;
            }
        }
    }

    if (cur == 0) output_solution();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (2, 3, 4, 5, 6, 7, 8)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_for(gmin, rng):
    """Return (m, k2, r, G) with G = m*k2 >= gmin and r^k2 = 1 mod m, or None."""
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 6])
        m = max(2, -(-gmin // k2))
        if k2 == 1:
            return m, 1, 1, m
        cands = [c for c in range(1, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
            return m, k2, r, m * k2
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    # Exact construction for D = 3 when d - 1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Lift search: climb in order of the lift, each success adds 2*k vertices.
    end = t0 + max(2.0, time_limit * 0.9 - 2.0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    last_k = None

    while True:
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break

        if last_k is not None and rng.random() < 0.5:
            k = last_k
        elif rng.random() < 0.3:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.05 * rng.random())

        cur_n = best[0]
        gmin = cur_n // (2 * k) + 1  # 2*k*G > cur_n
        if rng.random() < 0.3:
            gmin += rng.randrange(0, max(1, gmin // 50) + 1)

        grp = _group_for(gmin, rng)
        if grp is None:
            continue
        m, k2, r, _G = grp

        slice_s = min(remaining - 1.0, max(4.0, remaining * 0.3))
        trials[k] += 1
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 1 << 30), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
            n, e = lib.parse_graph_text(out)
        except Exception:
            n, e = 0, []

        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            wins[k] += 1
            last_k = k

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
