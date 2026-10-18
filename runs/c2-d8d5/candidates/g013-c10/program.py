import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts on semidirect products.
#
# Group G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e)).
# The graph has 2K blocks of |G| vertices: A_i (i<K) and B_j (j<K). Each
# A-block has d darts. Layer l maps A_i to B_{lay[l][i]} with voltage
# vol[l][i]: A_{i,g} ~ B_{j, g*s}. Since every lay[l] is a permutation, each
# B-block receives exactly d darts too, so the max degree is d.
#
# Left multiplication by G is an automorphism, so distances from the 2K
# identity vertices determine the diameter. The cost is the total number of
# unreached (distance > D) pairs from those sources, computed by BFS.
# Moves: change one voltage, or swap two targets within one layer.
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

static int d_, D_, K_, G_, m_, k2_, r_, N_;
static int *mulT, *invT, *pw, *lay, *ilay, *vol, *dist, *qu;

static int nb(int v, int l) {
    if (v < K_ * G_) {
        int i = v / G_, g = v % G_;
        int j = lay[l * K_ + i];
        int s = vol[l * K_ + i];
        return (K_ + j) * G_ + mulT[g * G_ + s];
    } else {
        int w = v - K_ * G_;
        int j = w / G_, h = w % G_;
        int i = ilay[l * K_ + j];
        int s = vol[l * K_ + i];
        return i * G_ + mulT[h * G_ + invT[s]];
    }
}

static void rebuild_ilay(int l) {
    for (int i = 0; i < K_; i++) ilay[l * K_ + lay[l * K_ + i]] = i;
}

/* Number of vertices not within distance D_ of src. */
static int bfs_bad(int src) {
    for (int v = 0; v < N_; v++) dist[v] = -1;
    int h = 0, t = 0;
    dist[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist[v] >= D_) continue;
        for (int l = 0; l < d_; l++) {
            int u = nb(v, l);
            if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
        }
    }
    return N_ - t;
}

static long long full_cost(void) {
    long long c = 0;
    for (int b = 0; b < 2 * K_; b++) c += bfs_bad(b * G_);
    return c;
}

static int build_group(void) {
    G_ = m_ * k2_;
    if (G_ < 1 || G_ > 3000) return 0;
    pw = malloc(sizeof(int) * (size_t)k2_);
    long long p = 1 % m_;
    for (int b = 0; b < k2_; b++) { pw[b] = (int)p; p = p * r_ % m_; }
    mulT = malloc(sizeof(int) * (size_t)G_ * G_);
    invT = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2_, b = x % k2_;
        for (int y = 0; y < G_; y++) {
            int c = y / k2_, e = y % k2_;
            long long ra = ((long long)a + (long long)pw[b] * c) % m_;
            mulT[x * G_ + y] = (int)(ra * k2_ + (b + e) % k2_);
        }
    }
    for (int x = 0; x < G_; x++) invT[x] = -1;
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            if (mulT[x * G_ + y] == 0) invT[x] = y;
    for (int x = 0; x < G_; x++) if (invT[x] < 0) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    m_ = atoi(argv[5]);
    k2_ = atoi(argv[6]);
    r_ = atoi(argv[7]);
    K_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || m_ < 1 || k2_ < 1 || K_ < 1 || K_ > 8) { printf("0 0\n"); return 0; }
    if (!build_group()) { printf("0 0\n"); return 0; }

    N_ = 2 * K_ * G_;
    lay = malloc(sizeof(int) * (size_t)d_ * K_);
    ilay = malloc(sizeof(int) * (size_t)d_ * K_);
    vol = malloc(sizeof(int) * (size_t)d_ * K_);
    dist = malloc(sizeof(int) * (size_t)N_);
    qu = malloc(sizeof(int) * (size_t)N_);
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) lay[l * K_ + i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = lay[l * K_ + i]; lay[l * K_ + i] = lay[l * K_ + j]; lay[l * K_ + j] = t;
        }
        rebuild_ilay(l);
        for (int i = 0; i < K_; i++) vol[l * K_ + i] = rint_(G_);
    }

    long long cost = full_cost();
    int found = (cost == 0);
    clock_t c0 = clock();
    const double T0 = 8.0, T1 = 0.3;

    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        if (K_ == 1 || rdbl() < 0.7) {
            int l = rint_(d_), i = rint_(K_);
            int idx = l * K_ + i;
            int old = vol[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[idx] = nv;
            long long nc = full_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[idx] = old;
            }
        } else {
            int l = rint_(d_);
            int i1 = rint_(K_);
            int i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int a = l * K_ + i1, b = l * K_ + i2;
            int t = lay[a]; lay[a] = lay[b]; lay[b] = t;
            rebuild_ilay(l);
            long long nc = full_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = lay[a]; lay[a] = lay[b]; lay[b] = t;
                rebuild_ilay(l);
            }
        }
        if (cost == 0) found = 1;
    }

    if (!found) { printf("0 0\n"); return 0; }

    int cap = K_ * G_ * d_;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    int m = 0;
    for (int v = 0; v < K_ * G_; v++) {
        for (int l = 0; l < d_; l++) {
            int u = nb(v, l);
            int dup = 0;
            for (int l2 = 0; l2 < l; l2++) if (nb(v, l2) == u) { dup = 1; break; }
            if (!dup) { eu[m] = v; ev[m] = u; m++; }
        }
    }
    printf("%d %d\n", N_, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue and constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 with order m*k2 >= target, or None."""
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12])
        m = max(2, -(-target // k2))
        if m * k2 > 3000:
            continue
        if k2 == 1:
            return m, 1, 1
        cands = [c for c in range(1, m)
                 if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions for D = 3 (calibration case returns immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: annealing over bi-Cayley lifts with K blocks on a group of
    # order G, run inside C. Each run tries to reach 2*K*G > current best.
    deadline = t0 + max(1.0, 0.85 * time_limit - 3.0)
    failures = 0
    while failures < 25:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        K = rng.choice((1, 1, 2, 2, 3, 4))
        need = best[0] // (2 * K) + 1
        target = need + rng.randrange(0, 1 + need // 50)
        g = _sample_group(target, rng)
        if g is None:
            failures += 1
            continue
        m, k2, r = g
        if 2 * K * m * k2 <= best[0]:
            failures += 1
            continue
        slice_s = min(remaining - 0.3, 6.0)
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", m, k2, r, K],
                            timeout=slice_s + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            failures += 1
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
        else:
            failures += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
