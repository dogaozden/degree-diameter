import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley (voltage) lifts of a base
# bipartite graph with K left and K right blocks, each of degree d, over the
# semidirect product G = Z_M x| Z_K2 (element a*K2+b, r^K2 = 1 mod M).
#
# Vertex (block i, element g) on the left is i*G+g, on the right (K+j)*G+x.
# Dart (layer l, left block i) joins left (i,g) to right (perm[l][i], g*s)
# with voltage s = vol[l][i]. Left multiplication by h is an automorphism of
# the lift, so the diameter check only needs BFS from the 2K block roots
# (p, e). The cost is the number of vertices left unreached within D summed
# over those roots, plus a large penalty for duplicate darts. Cost 0 means a
# simple d-regular bipartite graph of diameter <= D, which is printed.
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

#define PEN 1000LL

static int d_, D_, K_, M_, K2_, R_, G_, N_;
static int *pw, *perm, *invp, *vol, *vinv, *nbr, *dist, *queue;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* (a,b)*(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    int A = (int)(((long long)a + (long long)pw[b] * c) % M_);
    int B = (b + e) % K2_;
    return A * K2_ + B;
}

/* inverse of (a,b) is (-r^(-b) a, -b) */
static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    int A = (int)((M_ - ((long long)pw[nb] * a) % M_) % M_);
    return A * K2_ + nb;
}

static void build_nbr(void) {
    int K = K_, G = G_, d = d_;
    for (int idx = 0; idx < K * d; idx++) vinv[idx] = ginv(vol[idx]);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++) {
            int u = i * G + g;
            for (int l = 0; l < d; l++) {
                int idx = l * K + i;
                nbr[u * d + l] = (K + perm[idx]) * G + gmul(g, vol[idx]);
            }
        }
    for (int j = 0; j < K; j++)
        for (int x = 0; x < G; x++) {
            int u = (K + j) * G + x;
            for (int l = 0; l < d; l++) {
                int i = invp[l * K + j];
                int idx = l * K + i;
                nbr[u * d + l] = i * G + gmul(x, vinv[idx]);
            }
        }
}

static int dupcount(void) {
    int n = K_ * d_, cnt = 0;
    for (int a = 0; a < n; a++)
        for (int b = a + 1; b < n; b++)
            if (a % K_ == b % K_ && perm[a] == perm[b] && vol[a] == vol[b]) cnt++;
    return cnt;
}

static long long evaluate(void) {
    build_nbr();
    long long cost = 0;
    int d = d_, D = D_;
    for (int s = 0; s < 2 * K_; s++) {
        int src = s * G_;
        for (int v = 0; v < N_; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[src] = 0;
        queue[t++] = src;
        while (h < t) {
            int v = queue[h++];
            int dv = dist[v];
            if (dv >= D) continue;
            for (int l = 0; l < d; l++) {
                int w = nbr[v * d + l];
                if (dist[w] < 0) { dist[w] = dv + 1; queue[t++] = w; }
            }
        }
        cost += N_ - t;
    }
    cost += PEN * (long long)dupcount();
    return cost;
}

static void swap_perm(int l, int a, int b, int i1, int i2) {
    int t = perm[a]; perm[a] = perm[b]; perm[b] = t;
    invp[l * K_ + perm[a]] = i1;
    invp[l * K_ + perm[b]] = i2;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    K_ = atoi(argv[3]);
    M_ = atoi(argv[4]);
    K2_ = atoi(argv[5]);
    R_ = atoi(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);

    if (d_ < 1 || D_ < 1 || K_ < 1 || K_ > 64 || M_ < 2 || K2_ < 1 || K2_ > 1000) {
        printf("0 0\n");
        return 0;
    }
    R_ %= M_;
    if (R_ < 0 || gcd_(R_, M_) != 1) { printf("0 0\n"); return 0; }
    pw = malloc(sizeof(int) * (size_t)K2_);
    if (!pw) { printf("0 0\n"); return 0; }
    pw[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw[b] = (int)((long long)pw[b - 1] * R_ % M_);
    if ((long long)pw[K2_ - 1] * R_ % M_ != 1 % M_) { printf("0 0\n"); return 0; }

    G_ = M_ * K2_;
    N_ = 2 * K_ * G_;
    int KD = K_ * d_;
    perm = malloc(sizeof(int) * (size_t)KD);
    invp = malloc(sizeof(int) * (size_t)KD);
    vol = malloc(sizeof(int) * (size_t)KD);
    vinv = malloc(sizeof(int) * (size_t)KD);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * (size_t)N_);
    queue = malloc(sizeof(int) * (size_t)N_);
    if (!perm || !invp || !vol || !vinv || !nbr || !dist || !queue) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        int *p = perm + l * K_;
        for (int i = 0; i < K_; i++) p[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K_; i++) invp[l * K_ + p[i]] = i;
    }
    for (int idx = 0; idx < KD; idx++) vol[idx] = rint_(G_);

    long long cost = evaluate();
    const double T0 = 3.0, T1 = 0.1, CYC = 3.0;
    clock_t c0 = clock();

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double fr = el / limit * CYC;
        fr -= floor(fr);
        double T = T0 * pow(T1 / T0, fr);
        long long nc;

        if (K_ >= 2 && rdbl() < 0.2) {
            int l = rint_(d_);
            int i1 = rint_(K_), i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int a = l * K_ + i1, b = l * K_ + i2;
            swap_perm(l, a, b, i1, i2);
            nc = evaluate();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cost = nc;
            else swap_perm(l, a, b, i1, i2);
        } else {
            int idx = rint_(KD);
            int nv = rint_(G_);
            int old = vol[idx];
            if (nv == old) continue;
            vol[idx] = nv;
            nc = evaluate();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cost = nc;
            else vol[idx] = old;
        }
    }

    if (cost == 0) {
        build_nbr();
        int U = K_ * G_;
        printf("%d %d\n", N_, U * d_);
        for (int u = 0; u < U; u++)
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", u, nbr[u * d_ + l]);
    } else {
        printf("0 0\n");
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


def _pick_r(m, k2, rng):
    """Return r with gcd(r, m) = 1 and r^k2 = 1 mod m, or None."""
    if m <= 2 or k2 == 1:
        return 1
    if rng.random() < 0.15:
        return 1
    if k2 == 2 and rng.random() < 0.3:
        return m - 1
    for _ in range(100):
        c = rng.randrange(2, m)
        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
            return c
    return None


_K2_CHOICES = (1, 1, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 16)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target and small excess, or None."""
    for _ in range(200):
        k2 = rng.choice(_K2_CHOICES)
        m_lo = max(2, -(-target // k2))
        m = m_lo + rng.randrange(0, m_lo // 40 + 1)
        r = _pick_r(m, k2, rng)
        if r is not None:
            return m, k2, r
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction when it applies (calibration case returns at once).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: C annealer over group lifts, growing the order each success.
    deadline = t0 + max(1.0, time_limit * 0.85 - 3.0)
    ks = (1, 2, 2, 3, 3, 4, 4, 5, 6)
    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            k = rng.choice(ks)
            # Need 2*k*G > current best order.
            target = max(2, -(-(best[0] + 1) // (2 * k)))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            slice_s = min(remaining, max(3.0, min(12.0, 0.3 * remaining)))
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, k, m, k2, r, rng.randrange(1, 1 << 30), f"{slice_s:.2f}"],
                    timeout=slice_s + 15.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass  # keep the valid fallback and try another group
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
