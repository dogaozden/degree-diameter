import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts on Z_m x| Z_k2.
#
# Base graph: k A-blocks and k B-blocks, each a copy of G = m*k2 elements.
# Each of the d layers l has a permutation pi_l of the blocks and a voltage
# S[l][i] per A-block i. Edge: (i, x) -- (k + pi_l(i), x * S[l][i]).
# The lift is d-regular and G acts on it by left multiplication, so the
# distance structure is determined by one BFS per block from its identity
# vertex (2k BFS runs of O(N d) each). The cost is the number of unreached
# (source, target) pairs plus G times the number of duplicate darts. Cost 0
# gives a valid simple d-regular bipartite graph with diameter <= D.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXL 32
#define MAXK 32
#define MAXG 3000

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (u64)n); }
static double rnddbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int *mulT, *invT, *dist, *queue_;
static int pi_[MAXL][MAXK], ipi_[MAXL][MAXK], S_[MAXL][MAXK];

static int gmul(int x, int y) { return mulT[x * G_ + y]; }

/* Neighbour of vertex v in layer l. Vertex id = block * G + element. */
static int nbr_of(int v, int l) {
    int kG = k_ * G_;
    if (v < kG) {
        int i = v / G_, x = v - i * G_;
        int j = pi_[l][i];
        return (k_ + j) * G_ + gmul(x, S_[l][i]);
    } else {
        int jj = v - kG;
        int j = jj / G_, y = jj - j * G_;
        int i = ipi_[l][j];
        return i * G_ + gmul(y, invT[S_[l][i]]);
    }
}

static void set_ipi(int l) {
    for (int i = 0; i < k_; i++) ipi_[l][pi_[l][i]] = i;
}

/* Unreached (source, target) pairs, summed over the 2k block sources. */
static long long cost_fn(void) {
    long long total = 0;
    for (int b = 0; b < 2 * k_; b++) {
        int src = b * G_;
        for (int v = 0; v < N_; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        queue_[tail++] = src;
        while (head < tail) {
            int v = queue_[head++];
            if (dist[v] >= D_) continue;
            for (int l = 0; l < d_; l++) {
                int u = nbr_of(v, l);
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    queue_[tail++] = u;
                }
            }
        }
        total += N_ - tail;
    }
    return total;
}

/* Duplicate darts: same A-block, same target block and same voltage. */
static int dup_count(void) {
    int dups = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (pi_[l1][i] == pi_[l2][i] && S_[l1][i] == S_[l2][i]) dups++;
    return dups;
}

static long long full_cost(void) {
    return cost_fn() + (long long)G_ * dup_count();
}

static void random_state(void) {
    for (int l = 0; l < d_; l++) {
        int perm[MAXK];
        for (int i = 0; i < k_; i++) perm[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k_; i++) pi_[l][i] = perm[i];
        set_ipi(l);
        for (int i = 0; i < k_; i++) S_[l][i] = rndint(G_);
    }
}

static void output_graph(void) {
    printf("%d %d\n", N_, k_ * G_ * d_);
    for (int i = 0; i < k_; i++)
        for (int x = 0; x < G_; x++)
            for (int l = 0; l < d_; l++) {
                int u = i * G_ + x;
                int v = (k_ + pi_[l][i]) * G_ + gmul(x, S_[l][i]);
                printf("%d %d\n", u, v);
            }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double secs = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 1 || d_ > MAXL || D_ < 1 || k_ < 1 || k_ > MAXK || m_ < 1 || k2_ < 1 || k2_ > 64) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    if (G_ < 2 || G_ > MAXG) { printf("0 0\n"); return 0; }
    r_ = ((r_ % m_) + m_) % m_;

    /* Semidirect product: element (a, b) coded a*k2 + b; need r^k2 = 1 mod m. */
    long long pw[64];
    pw[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw[t] = pw[t - 1] * r_ % m_;
    if ((pw[k2_ - 1] * r_) % m_ != 1 % m_) { printf("0 0\n"); return 0; }

    mulT = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    invT = malloc(sizeof(int) * (size_t)G_);
    N_ = 2 * k_ * G_;
    dist = malloc(sizeof(int) * (size_t)N_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    if (!mulT || !invT || !dist || !queue_) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G_; x++) {
        int a = x / k2_, b = x % k2_;
        for (int y = 0; y < G_; y++) {
            int c = y / k2_, dd = y % k2_;
            long long aa = (a + pw[b] * c) % m_;
            int bb = (b + dd) % k2_;
            mulT[x * G_ + y] = (int)(aa * k2_ + bb);
        }
    }
    for (int x = 0; x < G_; x++) {
        int a = x / k2_, b = x % k2_;
        int nb = (k2_ - b) % k2_;
        long long na = (m_ - (pw[nb] * a) % m_) % m_;
        invT[x] = (int)(na * k2_ + nb);
    }

    random_state();
    long long cur = full_cost();
    int found = (cur == 0);
    double T0 = 0.5 * G_ + 2.0, T1 = 0.2;
    clock_t c0 = clock();

    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= secs) break;
        double T = T0 * pow(T1 / T0, el / secs);

        if (k_ >= 2 && rnddbl() < 0.35) {
            int l = rndint(d_);
            int i1 = rndint(k_);
            int i2 = rndint(k_ - 1);
            if (i2 >= i1) i2++;
            int t = pi_[l][i1]; pi_[l][i1] = pi_[l][i2]; pi_[l][i2] = t;
            set_ipi(l);
            long long nc = full_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rnddbl() < exp(-(double)delta / T)) {
                cur = nc;
                if (cur == 0) found = 1;
            } else {
                t = pi_[l][i1]; pi_[l][i1] = pi_[l][i2]; pi_[l][i2] = t;
                set_ipi(l);
            }
        } else {
            int l = rndint(d_);
            int i = rndint(k_);
            int old = S_[l][i];
            int nw = rndint(G_);
            if (nw == old) continue;
            S_[l][i] = nw;
            long long nc = full_cost();
            long long delta = nc - cur;
            if (delta <= 0 || rnddbl() < exp(-(double)delta / T)) {
                cur = nc;
                if (cur == 0) found = 1;
            } else {
                S_[l][i] = old;
            }
        }
    }

    if (found) output_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: constructions, group sampling and the search driver.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6, 8)
_K2S = (1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 24, 28, 30, 36, 40)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with m * k2 >= target. Always succeeds (r = 1 fallback)."""
    k2 = rng.choice(_K2S)
    m = max(2, -(-target // k2))
    if k2 == 1 or rng.random() < 0.3:
        return m, k2, 1
    for _ in range(80):
        c = rng.randrange(2, m) if m > 2 else 1
        if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
            return m, k2, c
    return m, k2, 1


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 1, optimal for D = 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Exact projective-plane construction for D = 3 (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: C annealer over bi-Cayley lifts, aiming above the current order.
    end = t0 + max(2.0, time_limit - max(3.0, 0.07 * time_limit))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    try:
        while True:
            remaining = end - time.monotonic()
            if remaining < 1.5:
                break
            k = pick_k()
            half = best[0] // 2
            base = half // k + 1  # need 2 * k * G > current order
            Gt = base + rng.randrange(0, base // 25 + 2)
            m, k2, r = _sample_group(Gt, rng)
            secs = min(3.0, max(0.8, remaining / 8.0))
            secs = min(secs, remaining - 1.0)
            if secs < 0.5:
                break
            trials[k] += 1
            try:
                out = lib.run_c(C_SOURCE,
                                [d, D, rng.randrange(1, 1 << 30), f"{secs:.2f}", k, m, k2, r],
                                timeout=secs + 10.0)
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
