import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: lifted-graph annealer over semidirect products Z_m x| Z_k2.
#
# Construction: a bipartite base graph with k vertices per side. Layer t is a
# permutation sig[t] of {0..k-1} plus a voltage volt[t][i] in G, so A_i is
# joined to B_{sig[t][i]} with voltage volt[t][i]. The lift has vertices
# (side, i, g) for g in G, with A(i,g) ~ B(j, g*s) for each dart (i -> j, s).
# Left multiplication by G is an automorphism, so the diameter test only
# needs BFS from the 2k representatives (side, i, identity). The cost is the
# number of unreached (source, vertex) pairs, and the search is simulated
# annealing over voltages and layer permutations. Parallel darts are allowed
# (they just merge in the output), so reachability is the only constraint.
# A zero-cost state is printed as a valid graph and the run ends.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define MAXG 3000

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, N_, m_, k2_, r_;
static int *MUL, *INV, *pw;
static int sig[MAXD][MAXK], sinv[MAXD][MAXK], volt[MAXD][MAXK];
static int *mark, *qu;
static int stamp_ = 0;

/* Builds the multiplication and inverse tables for Z_m x| Z_k2 (element a*k2+b).
   Returns 0 if r is not a valid action (r^k2 != 1 mod m) or the table is not a group. */
static int build_group(void) {
    int G = G_, m = m_, k2 = k2_;
    pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r_ % m);
    if ((long long)pw[k2 - 1] * r_ % m != 1 % m) return 0;
    MUL = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    if (!MUL || !INV) return 0;
    for (int x = 0; x < G; x++) {
        int a1 = x / k2, b1 = x % k2;
        for (int y = 0; y < G; y++) {
            int a2 = y / k2, b2 = y % k2;
            int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % m);
            int b = (b1 + b2) % k2;
            MUL[x * G + y] = a * k2 + b;
        }
    }
    for (int x = 0; x < G; x++) INV[x] = -1;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MUL[x * G + y] == 0) { INV[x] = y; break; }
    for (int x = 0; x < G; x++) if (INV[x] < 0) return 0;
    return 1;
}

/* Neighbour number t of lift vertex v. A-side ids 0..kG-1, B-side ids kG..2kG-1. */
static inline int nb(int v, int t) {
    int kG = k_ * G_;
    if (v < kG) {
        int i = v / G_, g = v - i * G_;
        int j = sig[t][i];
        int s = volt[t][i];
        return kG + j * G_ + MUL[g * G_ + s];
    } else {
        int w = v - kG;
        int j = w / G_, h = w - j * G_;
        int i = sinv[t][j];
        int s = volt[t][i];
        return i * G_ + MUL[h * G_ + INV[s]];
    }
}

/* Number of vertices within distance D_ of src. */
static int reach_count(int src) {
    stamp_++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    mark[src] = stamp_;
    for (int depth = 0; depth < D_ && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            for (int t = 0; t < d_; t++) {
                int u = nb(v, t);
                if (mark[u] != stamp_) { mark[u] = stamp_; qu[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over the 2k representatives. Zero means valid. */
static long long cost_fn(void) {
    long long c = 0;
    for (int i = 0; i < k_; i++) c += N_ - reach_count(i * G_);
    for (int j = 0; j < k_; j++) c += N_ - reach_count(k_ * G_ + j * G_);
    return c;
}

static void output_graph(void) {
    int kG = k_ * G_;
    int cap = kG * d_ + 1;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    int m = 0;
    for (int v = 0; v < kG; v++) {
        int nbs[MAXD];
        int c = 0;
        for (int t = 0; t < d_; t++) {
            int u = nb(v, t);
            int dup = 0;
            for (int q = 0; q < c; q++) if (nbs[q] == u) { dup = 1; break; }
            if (!dup) nbs[c++] = u;
        }
        for (int q = 0; q < c; q++) { eu[m] = v; ev[m] = nbs[q]; m++; }
    }
    printf("%d %d\n", N_, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", eu[e], ev[e]);
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
    k_ = atoi(argv[8]);
    if (d_ < 1 || d_ > MAXD || D_ < 1 || k_ < 1 || k_ > MAXK || m_ < 1 || k2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    if (G_ < 2 || G_ > MAXG) { printf("0 0\n"); return 0; }
    r_ = ((r_ % m_) + m_) % m_;
    if (!build_group()) { printf("0 0\n"); return 0; }

    N_ = 2 * k_ * G_;
    mark = calloc((size_t)N_, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N_);
    if (!mark || !qu) { printf("0 0\n"); return 0; }

    for (int t = 0; t < d_; t++) {
        for (int i = 0; i < k_; i++) sig[t][i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = sig[t][i]; sig[t][i] = sig[t][j]; sig[t][j] = tmp;
        }
        for (int i = 0; i < k_; i++) {
            sinv[t][sig[t][i]] = i;
            volt[t][i] = rint_(G_);
        }
    }

    long long cur = cost_fn();
    if (cur == 0) { output_graph(); return 0; }

    clock_t c0 = clock();
    const double T0 = 40.0, T1 = 0.5;
    double el = 0.0, frac = 0.0, T = T0;
    long iter = 0;
    while (1) {
        if ((++iter & 31) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            frac = el / limit;
            T = T0 * pow(T1 / T0, frac);
        }
        int t = rint_(d_), i = rint_(k_);
        long long c2;
        if (k_ >= 2 && rdbl() < 0.3) {
            int i2 = rint_(k_);
            if (i2 == i) continue;
            int tmp = sig[t][i]; sig[t][i] = sig[t][i2]; sig[t][i2] = tmp;
            sinv[t][sig[t][i]] = i;
            sinv[t][sig[t][i2]] = i2;
            c2 = cost_fn();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                tmp = sig[t][i]; sig[t][i] = sig[t][i2]; sig[t][i2] = tmp;
                sinv[t][sig[t][i]] = i;
                sinv[t][sig[t][i2]] = i2;
            }
        } else {
            int old = volt[t][i];
            int nw = rint_(G_);
            if (nw == old) continue;
            volt[t][i] = nw;
            c2 = cost_fn();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                volt[t][i] = old;
            }
        }
        if (cur == 0) { output_graph(); return 0; }
    }
    printf("0 0\n");
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


def _group_options(G, rng):
    """Return (m, k2, r) triples with m * k2 == G giving Z_m x| Z_k2 (r = 1 is direct product)."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if k2 == 1:
            opts.append((G, 1, 1))
            continue
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:3]:
            opts.append((m, k2, r))
    return opts


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, time_limit - 7.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

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

    # Lift search over semidirect-product voltage graphs, run in C.
    while True:
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        k = rng.choice((1, 1, 2, 2, 3, 4))
        G = best[0] // (2 * k) + 1          # 2*k*G > best order
        if rng.random() < 0.3:
            G += rng.randrange(1, 4)
        if G < 2:
            G = 2
        if G > 3000:
            break
        opts = _group_options(G, rng)
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        slice_s = min(remaining, rng.uniform(2.0, 5.0))
        if slice_s < 1.0:
            break
        seed_i = rng.randrange(1, 1 << 30)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed_i, f"{slice_s:.2f}", m, k2, r, k],
                            timeout=slice_s + 15.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
