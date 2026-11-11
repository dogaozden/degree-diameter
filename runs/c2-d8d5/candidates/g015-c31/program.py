import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealer over semidirect products Z_m x| Z_k2.
#
# A bipartite lift has K blocks per side, each of size G (|G| = m*k2). There
# are d "layers". In layer l, A-block i is matched to B-block P[l][i] with
# voltage S[l][i], so A(i,g) ~ B(P, g*s). Each layer is a perfect matching
# between blocks, so the lift is d-regular and bipartite.
#
# Left multiplication by any group element is an automorphism, so the
# unreached count is the same for every vertex in a block. The cost is
# therefore computed with one BFS per block representative (2K BFS runs
# total), which is much cheaper than a full all-pairs bitset check. Cost 0
# means diameter <= D. Duplicate darts (same i, same j, same s) are
# penalised.
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

#define PEN 20

static int d_, D_, K, G, N;
static int *mul, *inv_, *pw;
static int *P, *Pinv, *S, *nbr;
static int *stamp, *queue_;
static int curstamp = 0;

static void build_nbr(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l * K + i], s = S[l * K + i];
            for (int g = 0; g < G; g++)
                nbr[(i * G + g) * d_ + l] = (K + j) * G + mul[g * G + s];
        }
        for (int j = 0; j < K; j++) {
            int i = Pinv[l * K + j], s = S[l * K + i];
            int si = inv_[s];
            for (int h = 0; h < G; h++)
                nbr[((K + j) * G + h) * d_ + l] = i * G + mul[h * G + si];
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (P[l1 * K + i] == P[l2 * K + i] && S[l1 * K + i] == S[l2 * K + i]) c++;
    return c;
}

static long long cost_fn(void) {
    build_nbr();
    long long bad = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        curstamp++;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        stamp[src] = curstamp;
        for (int dep = 0; dep < D_ && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int v = queue_[head++];
                const int *nv = nbr + (size_t)v * d_;
                for (int l = 0; l < d_; l++) {
                    int u = nv[l];
                    if (stamp[u] != curstamp) {
                        stamp[u] = curstamp;
                        queue_[tail++] = u;
                    }
                }
            }
        }
        bad += N - tail;
    }
    return bad + (long long)PEN * dupcount();
}

static void fix_pinv(int l) {
    for (int i = 0; i < K; i++) Pinv[l * K + P[l * K + i]] = i;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    int m = atoi(argv[6]), k2 = atoi(argv[7]);
    long long r = atoll(argv[8]);
    if (d_ < 1 || d_ > 32 || D_ < 1 || K < 1 || K > 32 || m < 1 || k2 < 1) {
        printf("0 0\n");
        return 0;
    }
    long long Gll = (long long)m * k2;
    if (Gll > 5000 || 2LL * K * Gll > 30000) { printf("0 0\n"); return 0; }
    G = (int)Gll;
    N = 2 * K * G;
    r %= m;
    if (r < 0) r += m;

    pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    if ((long long)pw[k2 - 1] * r % m != 1 % m) { printf("0 0\n"); return 0; }

    /* Semidirect product Z_m x| Z_k2: (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2). Element x = a*k2 + b. */
    mul = malloc(sizeof(int) * (size_t)G * G);
    for (int x = 0; x < G; x++) {
        int a1 = x / k2, b1 = x % k2;
        for (int y = 0; y < G; y++) {
            int a2 = y / k2, b2 = y % k2;
            long long aa = ((long long)a1 + (long long)pw[b1] * a2) % m;
            mul[x * G + y] = (int)(aa * k2 + (b1 + b2) % k2);
        }
    }
    inv_ = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        inv_[x] = -1;
        for (int y = 0; y < G; y++)
            if (mul[x * G + y] == 0) { inv_[x] = y; break; }
        if (inv_[x] < 0) { printf("0 0\n"); return 0; }
    }

    int sz = d_ * K;
    P = malloc(sizeof(int) * sz);
    Pinv = malloc(sizeof(int) * sz);
    S = malloc(sizeof(int) * sz);
    int *Pb = malloc(sizeof(int) * sz);
    int *Pib = malloc(sizeof(int) * sz);
    int *Sb = malloc(sizeof(int) * sz);
    nbr = malloc(sizeof(int) * (size_t)N * d_);
    stamp = calloc((size_t)N, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)N);
    int *perm = malloc(sizeof(int) * K);
    if (!mul || !inv_ || !P || !Pinv || !S || !Pb || !Pib || !Sb || !nbr || !stamp || !queue_ || !perm) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            P[l * K + i] = perm[i];
            S[l * K + i] = rint_(G);
        }
        fix_pinv(l);
    }

    long long cur = cost_fn();
    clock_t c0 = clock();
    const double T0 = 8.0, T1 = 0.3;

    while (cur > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        memcpy(Pb, P, sizeof(int) * sz);
        memcpy(Pib, Pinv, sizeof(int) * sz);
        memcpy(Sb, S, sizeof(int) * sz);

        int mv = rint_(100);
        if (K >= 2 && mv < 35) {
            int l = rint_(d_);
            int i1 = rint_(K);
            int i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            int t = P[l * K + i1]; P[l * K + i1] = P[l * K + i2]; P[l * K + i2] = t;
            fix_pinv(l);
        } else {
            int l = rint_(d_), i = rint_(K);
            int ns = rint_(G);
            if (ns == S[l * K + i]) continue;
            S[l * K + i] = ns;
        }

        long long nc = cost_fn();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            memcpy(P, Pb, sizeof(int) * sz);
            memcpy(Pinv, Pib, sizeof(int) * sz);
            memcpy(S, Sb, sizeof(int) * sz);
        }
    }

    if (cur != 0) { printf("0 0\n"); return 0; }
    cost_fn();  /* make nbr match the accepted state */

    long long M = (long long)K * G * d_;
    printf("%d %lld\n", N, M);
    for (int a = 0; a < K * G; a++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", a, nbr[a * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6, 8)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_for(G, rng):
    """Return (m, k2, r) with m * k2 == G, forming Z_m x| Z_k2 with r^k2 == 1 mod m.

    Falls back to the cyclic group Z_G (k2 = 1), which always works.
    """
    if rng.random() < 0.3:
        return G, 1, 1 % G
    divs = [k for k in range(2, G + 1) if G % k == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        cands = [c for c in range(1, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return G, 1, 1 % G


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

    # Degree 2 is a cycle: C_{2D} is bipartite with diameter D.
    if d == 2:
        consider(*lib.haar_graph(D, [0, 1]))
        return best

    # Voltage-lift search in C over semidirect products, with a bandit over K.
    usable = max(0.0, min(0.9 * time_limit, time_limit - 2.0))
    deadline = t0 + usable
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    budget_cap = max(3.0, 0.1 * time_limit)
    exceptions = 0

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    while time.monotonic() < deadline - 1.5 and exceptions < 5:
        remaining = deadline - time.monotonic()
        budget = min(remaining - 1.0, budget_cap)
        if budget < 1.0:
            break
        k = pick_k()
        lo = best[0] // (2 * k) + 1          # smallest block size that beats the current best
        G = lo + rng.randrange(0, max(2, lo // 40))
        m, k2, r = _group_for(G, rng)
        G = m * k2
        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            exceptions += 1
            continue
        if n > 0:
            wins[k] += 1
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
