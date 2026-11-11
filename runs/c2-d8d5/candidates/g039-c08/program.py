import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: cyclic-or-semidirect bi-Cayley lifts of a small base
# multigraph (k left blocks, k right blocks, d darts per block), with voltages
# in Z_m x| Z_k2. The group acts on each block by left multiplication, which is
# a graph automorphism, so diameter only has to be checked from the 2k base
# vertices. Each evaluation is 2k BFS runs over the lift, and a C simulated
# annealer searches the voltages and layer permutations.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000LL

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, G_;
static int *pw, *invE, *mulT, *lay, *S, *rin, *rinv, *dist, *qu;

/* (a,b)*(c,e) = (a + r^b c, b + e), element coded a*k2 + b. */
static int mulE(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    long long t = ((long long)pw[b] * c + a) % m_;
    return (int)t * k2_ + (b + e) % k2_;
}

/* inverse of (a,b) is (-r^(-b) a, -b). */
static int invOf(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = ((long long)pw[nb] * a) % m_;
    int na = (int)((m_ - t) % m_);
    return na * k2_ + nb;
}

#define MUL(x, y) mulT[(size_t)(x) * (size_t)G_ + (size_t)(y)]

static void rebuild(void) {
    for (int j = 0; j < k_; j++) {
        int cnt = 0;
        for (int l = 0; l < d_; l++)
            for (int i = 0; i < k_; i++)
                if (lay[l * k_ + i] == j && cnt < d_) {
                    rin[j * d_ + cnt] = i;
                    rinv[j * d_ + cnt] = invE[S[l * k_ + i]];
                    cnt++;
                }
    }
}

/* Left vertex (i,x) has darts to (j, x*s). Right vertex (j,y) has darts to (i, y*s^-1). */
static int nbrs(int v, int *out) {
    int blk = v / G_, x = v % G_;
    if (blk < k_) {
        int i = blk;
        for (int l = 0; l < d_; l++) {
            int j = lay[l * k_ + i];
            out[l] = (k_ + j) * G_ + MUL(x, S[l * k_ + i]);
        }
    } else {
        int j = blk - k_;
        for (int t = 0; t < d_; t++) {
            int i = rin[j * d_ + t];
            out[t] = i * G_ + MUL(x, rinv[j * d_ + t]);
        }
    }
    return d_;
}

/* Unreached ordered pairs from the 2k base sources, plus a penalty for duplicate darts. */
static long long cost_fn(void) {
    rebuild();
    int N = 2 * k_ * G_;
    long long total = 0;
    int nb[256];
    for (int b = 0; b < 2 * k_; b++) {
        for (int v = 0; v < N; v++) dist[v] = -1;
        int src = b * G_;
        dist[src] = 0;
        int h = 0, t = 0, vis = 1;
        qu[t++] = src;
        while (h < t) {
            int v = qu[h++];
            if (dist[v] >= D_) continue;
            nbrs(v, nb);
            for (int q = 0; q < d_; q++) {
                int u = nb[q];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    qu[t++] = u;
                    vis++;
                }
            }
        }
        total += N - vis;
    }
    long long dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (lay[l1 * k_ + i] == lay[l2 * k_ + i] && S[l1 * k_ + i] == S[l2 * k_ + i])
                    dup++;
    total += dup * PEN;
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    long long rr = atoll(argv[8]);
    if (d_ < 1 || d_ > 200 || D_ < 1 || k_ < 1 || k_ > 8 || m_ < 2 || k2_ < 1 ||
        (long long)m_ * k2_ > 4000) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    int r = (int)(((rr % m_) + m_) % m_);
    long long p = 1 % m_;
    for (int b = 0; b < k2_; b++) p = p * r % m_;
    if (p != 1 % m_) { printf("0 0\n"); return 0; }

    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;

    int G = G_, k = k_, d = d_;
    int N = 2 * k * G;

    pw = malloc(sizeof(int) * (size_t)k2_);
    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);

    invE = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) invE[x] = invOf(x);

    mulT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[(size_t)x * G + y] = mulE(x, y);

    lay = malloc(sizeof(int) * (size_t)d * k);
    S = malloc(sizeof(int) * (size_t)d * k);
    rin = malloc(sizeof(int) * (size_t)k * d);
    rinv = malloc(sizeof(int) * (size_t)k * d);
    dist = malloc(sizeof(int) * (size_t)N);
    qu = malloc(sizeof(int) * (size_t)N);
    if (!pw || !invE || !mulT || !lay || !S || !rin || !rinv || !dist || !qu) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d; l++) {
        int perm[8];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) lay[l * k + i] = perm[i];
        for (int i = 0; i < k; i++) S[l * k + i] = rint_(G);
    }

    long long cost = cost_fn();
    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        if (k >= 2 && rint_(10) < 2) {
            int l = rint_(d);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int *pa = &lay[l * k + i1], *pb = &lay[l * k + i2];
            int t = *pa; *pa = *pb; *pb = t;
            long long nc = cost_fn();
            long long dl = nc - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cost = nc;
            } else {
                t = *pa; *pa = *pb; *pb = t;
            }
        } else {
            int l = rint_(d), i = rint_(k);
            int idx = l * k + i;
            int old = S[idx];
            int nw = rint_(G);
            if (nw == old) continue;
            S[idx] = nw;
            long long nc = cost_fn();
            long long dl = nc - cost;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cost = nc;
            } else {
                S[idx] = old;
            }
        }
    }

    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }
    int E = k * G * d;
    printf("%d %d\n", N, E);
    for (int i = 0; i < k; i++)
        for (int x = 0; x < G; x++)
            for (int l = 0; l < d; l++) {
                int j = lay[l * k + i];
                int u = i * G + x;
                int v = (k + j) * G + MUL(x, S[l * k + i]);
                printf("%d %d\n", u, v);
            }
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


def _run_lift(d, D, k, m, k2, r, seed, seconds):
    """Run the C lift annealer once. Returns (n, edges); n == 0 means no graph found."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D == 2 or d < 2 or time_limit < 6:
        return best

    # Lift search: each run searches one group order just above the current best.
    margin = 3.0 + 0.04 * time_limit
    end = t0 + time_limit - margin
    ks = (1, 2, 3, 4)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    fails = 0
    while fails < 10:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, base // 100 + 2))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best[0] or G > 4000:
            continue
        slice_t = min(3.0 + 0.03 * time_limit, remaining)
        if slice_t < 1.0:
            break
        trials[k] += 1
        try:
            n, e = _run_lift(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), slice_t)
        except Exception:
            fails += 1
            continue
        if n > 0:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
