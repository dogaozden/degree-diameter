"""Bold variant: C-native simulated annealing over bi-Cayley lifts.

The C engine picks a base size K and a semidirect group Z_m x| Z_k2, then anneals the
voltages of a d-layer lift so that every block representative reaches every vertex within D
steps. Left translation by the group is an automorphism, so checking the K block
representatives is enough to prove diameter <= D. A goal order ratchets up on success and
eases back on failure.

Python handles the exact fallbacks (K_{d,d}, projective planes, Araujo-Lopez) and validates
every returned graph with lib.is_valid.
"""
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 8
#define MAXL 40
#define MAXN 40000
#define PEN 24

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Semidirect product Z_m x| Z_k2 with r^k2 = 1 mod m; element a*k2 + b. */
static int gm, gk2, gG;
static int gpw[256];   /* gpw[b] = r^b mod m */

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    int t = (int)((long long)gpw[b] * c % gm);
    return ((a + t) % gm) * gk2 + (b + e) % gk2;
}

static int ginv(int x) {
    int a = x / gk2, b = x % gk2, nb = (gk2 - b) % gk2;
    int t = (int)((long long)gpw[nb] * a % gm);
    return ((gm - t) % gm) * gk2 + nb;
}

static void set_group(int m, int k2, int r) {
    gm = m;
    gk2 = k2;
    gG = m * k2;
    gpw[0] = 1 % m;
    for (int b = 1; b < k2; b++) gpw[b] = (int)((long long)gpw[b - 1] * r % m);
}

/* Lift state: block i on the A side is vertices i*G..; block j on the B side is (K+j)*G... */
static int K, G, NV;
static int lay[MAXL][MAXK], vol[MAXL][MAXK];
static int nbr[MAXL][MAXN];
static uint32_t RA[MAXN], RB[MAXN];

/* Rebuild layer l: A_{i,g} ~ B_{lay[l][i], g*s}, so the B side gets the inverse map. */
static void set_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = lay[l][i], s = vol[l][i], si = ginv(s);
        int bi = i * G, bj = (K + j) * G;
        for (int g = 0; g < G; g++) {
            nbr[l][bi + g] = bj + gmul(g, s);
            nbr[l][bj + g] = bi + gmul(g, si);
        }
    }
}

/* Cost = missing (block representative, vertex) pairs within distance D, plus duplicate penalty.
 * Cost 0 means the lift is simple, d-regular, bipartite, and of diameter <= D. */
static int evaluate(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && vol[l1][i] == vol[l2][i]) dup++;

    uint32_t *cur = RA, *nxt = RB;
    for (int v = 0; v < NV; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint32_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long miss = 0;
    for (int v = 0; v < NV; v++) miss += 2 * K - __builtin_popcount(cur[v]);
    return (int)(miss + (long)PEN * dup);
}

static void randomize(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rndint(G);
        set_layer(l);
    }
}

/* Simulated annealing on the current (K, G) with a temperature cycle. */
static int anneal(double until, long patience) {
    randomize();
    int cost = evaluate();
    int best = cost;
    long last = 0;
    for (long t = 1; cost > 0; t++) {
        if ((t & 63) == 0 && now() > until) return 0;
        if (t - last > patience) return 0;
        double T = 0.25 + 2.0 * exp(-(double)(t % 20000) / 3000.0);
        int l = rndint(d);
        int oldL[MAXK], oldV[MAXK];
        memcpy(oldL, lay[l], sizeof oldL);
        memcpy(oldV, vol[l], sizeof oldV);
        if (K >= 2 && rnd01() < 0.3) {
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t2 = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = t2;
        } else {
            vol[l][rndint(K)] = rndint(G);
        }
        set_layer(l);
        int nc = evaluate();
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
            cost = nc;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            memcpy(lay[l], oldL, sizeof oldL);
            memcpy(vol[l], oldV, sizeof oldV);
            set_layer(l);
        }
    }
    return 1;
}

static long gcd_l(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Find m with m*k2 >= target and r with gcd(r,m)=1, r^k2 = 1 mod m. Returns m or 0. */
static int sample_group(int target, int k2, int *out_r) {
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    for (int tries = 0; tries < 400; tries++) {
        long r;
        if (k2 == 1) r = 1;
        else if (tries == 0) r = m - 1;
        else if (tries % 7 == 0) r = 1;
        else r = 2 + rndint((int)(m > 2 ? m - 2 : 1));
        if (r < 1 || r >= m) continue;
        if (gcd_l(r, m) != 1) continue;
        if (powmod_l(r, k2, m) != 1 % m) continue;
        *out_r = (int)r;
        return (int)m;
    }
    return 0;
}

static const int K2_LIST[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 24};
#define NK2 ((int)(sizeof K2_LIST / sizeof K2_LIST[0]))
static int kwins[MAXK + 1], ktrials[MAXK + 1];

static int pick_K(void) {
    if (rnd01() < 0.25) return 1 + rndint(MAXK);
    int bestk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (kwins[k] + 1.0) / (ktrials[k] + 2.0) + 0.05 * rnd01();
        if (v > bv) {
            bv = v;
            bestk = k;
        }
    }
    return bestk;
}

static long moore_bound(void) {
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int bestN = 0, bK, bG, bm, bk2, br;
static int blay[MAXL][MAXK], bvol[MAXL][MAXK];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long mb = moore_bound();
    int goal = 4 * d;

    while (now() < t_end) {
        if ((long)goal > mb) goal = (int)mb;
        int k = pick_K();
        int target = goal / (2 * k) + rndint(3);
        if (target < 1) target = 1;
        int k2 = K2_LIST[rndint(NK2)];
        int r = 1;
        int m = sample_group(target, k2, &r);
        if (!m) continue;
        long Gl = (long)m * k2;
        if (2L * k * Gl > MAXN || 2L * k * Gl > mb) continue;

        K = k;
        G = (int)Gl;
        NV = 2 * K * G;
        set_group(m, k2, r);
        ktrials[k]++;

        double remaining = t_end - now();
        double slice = remaining * 0.25;
        if (slice < 2.0) slice = 2.0;
        if (slice > 10.0) slice = 10.0;
        double until = now() + slice;
        if (until > t_end) until = t_end;

        int ok = anneal(until, 5000);
        if (ok) {
            kwins[k]++;
            if (NV > bestN) {
                bestN = NV;
                bK = K;
                bG = G;
                bm = m;
                bk2 = k2;
                br = r;
                memcpy(blay, lay, sizeof lay);
                memcpy(bvol, vol, sizeof vol);
            }
            goal = NV + NV / 32 + 1;
        } else {
            int floor_ = bestN > 0 ? bestN + 1 : 4 * d;
            goal = floor_ + (goal - floor_) * 97 / 100;
            if (goal < floor_) goal = floor_;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    K = bK;
    G = bG;
    NV = 2 * K * G;
    set_group(bm, bk2, br);
    memcpy(lay, blay, sizeof lay);
    memcpy(vol, bvol, sizeof vol);
    for (int l = 0; l < d; l++) set_layer(l);
    if (evaluate() != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", NV, (long)NV * d / 2);
    for (int u = 0; u < NV; u++)
        for (int l = 0; l < d; l++) {
            int v = nbr[l][u];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, always valid for D >= 2
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions. PG(2, d-1) is optimal for D = 3 when d-1 is a prime power.
    if D >= 3:
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

    total = max(1.0, 0.88 * time_limit - 2.0)
    final = t0 + total
    remaining = final - time.monotonic()
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.0, 2)],
                             timeout=remaining + 2.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
