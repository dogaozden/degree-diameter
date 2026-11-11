import math
import random
import time
from math import gcd, isqrt

import lib


# ----------------------------------------------------------------------------
# C engine: fast annealer over bi-Cayley lifts of Z_m x| Z_k2 (order G = m*k2).
#
# The lift has 2k blocks of G vertices (block b, element x -> vertex b*G + x).
# A-block i (0..k-1) and B-block k+j are joined through each layer l: dart
# (i, x) -- (k + lay[l][i], x * vol[l][i]). Left multiplication by G is an
# automorphism, so the graph is vertex-transitive within each block. Hence
# diameter <= D iff every vertex lies within D of each of the 2k identity
# vertices. Reachability is a 2k-bit mask per vertex, propagated D rounds.
# Cost = number of unreached (vertex, source-block) pairs. Simulated
# annealing moves: change a voltage, or swap two entries of a layer
# permutation. Output is the lift once cost reaches 0.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, NB_, N_;
static int *mulT, *invT;
static int *lay, *ilay, *vol;
static uint32_t *reach, *nxt;

static inline int nbr(int v, int l) {
    int blk = v / G_;
    int x = v - blk * G_;
    if (blk < k_) {
        int j = lay[l * k_ + blk];
        return (k_ + j) * G_ + mulT[x * G_ + vol[l * k_ + blk]];
    } else {
        int j = blk - k_;
        int i = ilay[l * k_ + j];
        return i * G_ + mulT[x * G_ + invT[vol[l * k_ + i]]];
    }
}

static long long cost_fn(void) {
    int V = N_;
    for (int v = 0; v < V; v++) reach[v] = 0;
    for (int b = 0; b < NB_; b++) reach[b * G_] = 1u << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < V; v++) {
            uint32_t r = reach[v];
            for (int l = 0; l < d_; l++) r |= reach[nbr(v, l)];
            nxt[v] = r;
            if (r != reach[v]) changed = 1;
        }
        uint32_t *t = reach; reach = nxt; nxt = t;
        if (!changed) break;
    }
    long long c = 0;
    for (int v = 0; v < V; v++) c += NB_ - __builtin_popcount(reach[v]);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    int m = atoi(argv[6]), k2 = atoi(argv[7]), r = atoi(argv[8]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || k_ > 8 || m < 1 || k2 < 1 || r < 0) {
        printf("0 0\n");
        return 0;
    }
    G_ = m * k2;
    if (G_ > 1500) { printf("0 0\n"); return 0; }
    NB_ = 2 * k_;
    N_ = NB_ * G_;
    r %= m;

    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;

    long long *pw = malloc(sizeof(long long) * (k2 + 1));
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * (long long)r) % m;

    mulT = malloc(sizeof(int) * (size_t)G_ * G_);
    invT = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G_; y++) {
            int c = y / k2, e = y % k2;
            long long A = ((long long)a + pw[b] * c) % m;
            int B = (b + e) % k2;
            mulT[x * G_ + y] = (int)(A * k2 + B);
        }
    }
    for (int x = 0; x < G_; x++) {
        invT[x] = 0;
        for (int y = 0; y < G_; y++) {
            if (mulT[x * G_ + y] == 0) { invT[x] = y; break; }
        }
    }

    lay = malloc(sizeof(int) * d_ * k_);
    ilay = malloc(sizeof(int) * d_ * k_);
    vol = malloc(sizeof(int) * d_ * k_);
    reach = malloc(sizeof(uint32_t) * (size_t)N_);
    nxt = malloc(sizeof(uint32_t) * (size_t)N_);
    int *tmp = malloc(sizeof(int) * k_);
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) tmp[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = tmp[i]; tmp[i] = tmp[j]; tmp[j] = t;
        }
        for (int i = 0; i < k_; i++) {
            lay[l * k_ + i] = tmp[i];
            ilay[l * k_ + tmp[i]] = i;
            vol[l * k_ + i] = rint_(G_);
        }
    }
    free(tmp);

    clock_t c0 = clock();
    long long cost = cost_fn();
    const double T0 = 3.0, T1 = 0.05;
    double T = T0;
    long long iter = 0;
    while (cost > 0) {
        if ((iter & 31) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double cyc = el / limit * 3.0;
            double ph = cyc - floor(cyc);
            T = T0 * pow(T1 / T0, ph);
        }
        iter++;
        if (k_ >= 2 && rint_(10) < 3) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *P = lay + l * k_;
            int t = P[i1]; P[i1] = P[i2]; P[i2] = t;
            ilay[l * k_ + P[i1]] = i1;
            ilay[l * k_ + P[i2]] = i2;
            long long nc = cost_fn();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = P[i1]; P[i1] = P[i2]; P[i2] = t;
                ilay[l * k_ + P[i1]] = i1;
                ilay[l * k_ + P[i2]] = i2;
            }
        } else {
            int l = rint_(d_), i = rint_(k_);
            int idx = l * k_ + i;
            int old = vol[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[idx] = nv;
            long long nc = cost_fn();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                vol[idx] = old;
            }
        }
    }

    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }

    int cap = k_ * G_ * d_;
    int *EU = malloc(sizeof(int) * (size_t)(cap + 1));
    int *EV = malloc(sizeof(int) * (size_t)(cap + 1));
    int me = 0;
    int nA = k_ * G_;
    for (int v = 0; v < nA; v++) {
        int t[64];
        int nt = 0;
        for (int l = 0; l < d_; l++) {
            int w = nbr(v, l);
            int dup = 0;
            for (int q = 0; q < nt; q++) if (t[q] == w) { dup = 1; break; }
            if (!dup) t[nt++] = w;
        }
        for (int q = 0; q < nt; q++) {
            EU[me] = v;
            EV[me] = t[q];
            me++;
        }
    }
    printf("%d %d\n", N_, me);
    for (int i = 0; i < me; i++) printf("%d %d\n", EU[i], EV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_GMAX = 1500


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _find_rs(m, k2, rng):
    """Up to three valid r values with r^k2 = 1 (mod m) and gcd(r, m) = 1 (r = 1 is always valid)."""
    if m < 2:
        return []
    if k2 == 1:
        return [1]
    res = [1]
    cand = [m - 1] if m > 2 else []
    if m > 2:
        cand += [rng.randrange(2, m) for _ in range(40)]
    for r in cand:
        if gcd(r, m) == 1 and pow(r, k2, m) == 1 % m and r not in res:
            res.append(r)
            if len(res) >= 3:
                break
    return res


def _configs(lo, hi, rng, cap=40):
    """Candidate (k, m, k2, r) with lift order 2*k*m*k2 in [lo, hi], sorted by order ascending."""
    trip = []
    for k in range(1, 9):
        g_lo = max(2, -(-lo // (2 * k)))
        g_hi = min(hi // (2 * k), _GMAX)
        for G in range(g_lo, g_hi + 1):
            for k2 in range(1, isqrt(G) + 1):
                if G % k2 == 0:
                    for kk in {k2, G // k2}:
                        trip.append((k, G // kk, kk))
    rng.shuffle(trip)
    out = []
    for (k, m, k2) in trip:
        if len(out) >= cap:
            break
        if m < 2:
            continue
        for r in _find_rs(m, k2, rng):
            out.append((k, m, k2, r))
    out.sort(key=lambda c: 2 * c[0] * c[1] * c[2])
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Ladder: repeatedly look for a valid bi-Cayley lift just above the current best order.
    deadline = t0 + max(2.0, time_limit - 5.0)
    step = 64
    fails = 0
    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            lo = best[0] + 1
            cfgs = _configs(lo, lo + step, rng)
            if not cfgs:
                step *= 2
                continue
            improved = False
            for (k, m, k2, r) in cfgs[:4]:
                remaining = deadline - time.monotonic()
                if remaining < 1.0:
                    break
                slice_t = min(remaining - 0.5, 1.5 * (1.6 ** min(fails, 6)))
                try:
                    out = lib.run_c(
                        C_SOURCE,
                        [d, D, rng.randrange(1 << 30), f"{slice_t:.2f}", k, m, k2, r],
                        None,
                        timeout=slice_t + 15.0,
                    )
                    n, e = lib.parse_graph_text(out)
                except Exception:
                    continue
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                    improved = True
                    break
            if improved:
                fails = 0
                step = max(32, step)
            else:
                fails += 1
                step = max(2, step // 2)
    except Exception:
        pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
