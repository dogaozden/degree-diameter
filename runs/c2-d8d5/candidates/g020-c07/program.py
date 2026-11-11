import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over bi-Cayley lifts on semidirect products Z_m x| Z_k2.
#
# Base graph: k A-blocks and k B-blocks, each of size G = m*k2. Layer l (l < d)
# is a permutation P[l] matching A-block i to B-block P[l][i] with voltage
# S[l][i]: A(i,g) ~ B(P, g*S). Every vertex then has exactly d darts.
# Left multiplication by the group is an automorphism, so distances from any
# vertex are determined by distances from the 2k block representatives. The
# cost is the number of (block representative, vertex) pairs at distance > D,
# plus a penalty for duplicate darts. Cost 0 means the lift is valid, and the
# first valid lift is printed and the run stops.
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

static int d_, D_, K_, K2_, M_, R_, G_, NV_;
static int pw_[128];
static int *P_, *S_, *Pinv_, *Sinv_, *nb_, *dist_, *que_, *Pb_, *Sb_;

/* element x = a*K2 + b means (a, b); (a,b)*(c,e) = (a + r^b c, b + e). */
static int mul_(int x, int y) {
    int a = x / K2_, b = x % K2_, c = y / K2_, e = y % K2_;
    return ((a + pw_[b] * c) % M_) * K2_ + (b + e) % K2_;
}

/* inverse of (a,b) is (-r^(-b) a, -b). */
static int inv_(int x) {
    int a = x / K2_, b = x % K2_;
    int nbk = (K2_ - b) % K2_;
    int ai = (M_ - (int)(((long long)pw_[nbk] * a) % M_)) % M_;
    return ai * K2_ + nbk;
}

static void fixl(int l) {
    for (int i = 0; i < K_; i++) Pinv_[l * K_ + P_[l * K_ + i]] = i;
    for (int i = 0; i < K_; i++) Sinv_[l * K_ + i] = inv_(S_[l * K_ + i]);
}

static void build_adj(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) {
            int j = P_[l * K_ + i], s = S_[l * K_ + i];
            for (int g = 0; g < G_; g++)
                nb_[(i * G_ + g) * d_ + l] = (K_ + j) * G_ + mul_(g, s);
        }
    }
    for (int l = 0; l < d_; l++) {
        for (int j = 0; j < K_; j++) {
            int i = Pinv_[l * K_ + j];
            int si = Sinv_[l * K_ + i];
            for (int h = 0; h < G_; h++)
                nb_[((K_ + j) * G_ + h) * d_ + l] = i * G_ + mul_(h, si);
        }
    }
}

static int bfs_count(int src) {
    for (int v = 0; v < NV_; v++) dist_[v] = -1;
    int h = 0, t = 0, cnt = 1;
    dist_[src] = 0;
    que_[t++] = src;
    while (h < t) {
        int v = que_[h++];
        if (dist_[v] >= D_) continue;
        for (int l = 0; l < d_; l++) {
            int u = nb_[v * d_ + l];
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                que_[t++] = u;
                cnt++;
            }
        }
    }
    return cnt;
}

static long long evaluate(void) {
    build_adj();
    long long bad = 0;
    for (int b = 0; b < 2 * K_; b++) bad += NV_ - bfs_count(b * G_);
    long long dup = 0;
    for (int i = 0; i < K_; i++) {
        for (int l1 = 0; l1 < d_; l1++) {
            for (int l2 = l1 + 1; l2 < d_; l2++) {
                if (P_[l1 * K_ + i] == P_[l2 * K_ + i] && S_[l1 * K_ + i] == S_[l2 * K_ + i])
                    dup++;
            }
        }
    }
    return bad + 3 * dup;
}

static void output(void) {
    long long m = (long long)K_ * G_ * d_;
    printf("%d %lld\n", NV_, m);
    for (int i = 0; i < K_; i++) {
        for (int g = 0; g < G_; g++) {
            for (int l = 0; l < d_; l++) {
                int j = P_[l * K_ + i], s = S_[l * K_ + i];
                printf("%d %d\n", i * G_ + g, (K_ + j) * G_ + mul_(g, s));
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    M_ = atoi(argv[5]);
    K2_ = atoi(argv[6]);
    R_ = atoi(argv[7]);
    K_ = atoi(argv[8]);
    if (d_ < 1 || d_ > 16 || D_ < 1 || K_ < 1 || K_ > 16 || M_ < 2 || K2_ < 1 || K2_ > 64) {
        printf("0 0\n");
        return 0;
    }
    R_ = ((R_ % M_) + M_) % M_;
    pw_[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw_[b] = (int)((long long)pw_[b - 1] * R_ % M_);
    if ((long long)pw_[K2_ - 1] * R_ % M_ != 1 % M_) { printf("0 0\n"); return 0; }

    G_ = M_ * K2_;
    NV_ = 2 * K_ * G_;
    int DK = d_ * K_;
    P_ = malloc(sizeof(int) * DK);
    S_ = malloc(sizeof(int) * DK);
    Pinv_ = malloc(sizeof(int) * DK);
    Sinv_ = malloc(sizeof(int) * DK);
    Pb_ = malloc(sizeof(int) * DK);
    Sb_ = malloc(sizeof(int) * DK);
    nb_ = malloc(sizeof(int) * (size_t)NV_ * d_);
    dist_ = malloc(sizeof(int) * NV_);
    que_ = malloc(sizeof(int) * NV_);
    int *perm = malloc(sizeof(int) * K_);
    if (!P_ || !S_ || !Pinv_ || !Sinv_ || !Pb_ || !Sb_ || !nb_ || !dist_ || !que_ || !perm) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) perm[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K_; i++) {
            P_[l * K_ + i] = perm[i];
            S_[l * K_ + i] = rint_(G_);
        }
        fixl(l);
    }
    free(perm);

    clock_t c0 = clock();
    long long cur = evaluate();
    long long bestc = cur;
    memcpy(Pb_, P_, sizeof(int) * DK);
    memcpy(Sb_, S_, sizeof(int) * DK);

    const int RL = 12000;
    const double T0 = 2.0, T1 = 0.1;
    int cyc = 0;
    while (cur != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        if (cyc >= RL) {
            cyc = 0;
            if (cur > bestc) {
                memcpy(P_, Pb_, sizeof(int) * DK);
                memcpy(S_, Sb_, sizeof(int) * DK);
                for (int l = 0; l < d_; l++) fixl(l);
                cur = bestc;
            }
        }
        double T = T0 * pow(T1 / T0, (double)cyc / RL);
        cyc++;

        int l = rint_(d_), i = rint_(K_), i2 = -1, old = 0, kind = 0;
        if (K_ >= 2 && rint_(10) < 3) {
            kind = 1;
            i2 = rint_(K_ - 1);
            if (i2 >= i) i2++;
            int t = P_[l * K_ + i];
            P_[l * K_ + i] = P_[l * K_ + i2];
            P_[l * K_ + i2] = t;
            fixl(l);
        } else {
            old = S_[l * K_ + i];
            int nw = rint_(G_);
            if (nw == old) continue;
            S_[l * K_ + i] = nw;
            fixl(l);
        }

        long long nc = evaluate();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(Pb_, P_, sizeof(int) * DK);
                memcpy(Sb_, S_, sizeof(int) * DK);
            }
        } else {
            if (kind) {
                int t = P_[l * K_ + i];
                P_[l * K_ + i] = P_[l * K_ + i2];
                P_[l * K_ + i2] = t;
                fixl(l);
            } else {
                S_[l * K_ + i] = old;
                fixl(l);
            }
        }
    }

    if (cur == 0) output();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6)
_K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with order m*k2 >= target."""
    k2 = rng.choice(_K2_CHOICES)
    m = max(2, -(-target // k2))
    r = 1
    if k2 > 1 and rng.random() < 0.7:
        cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
    return m, k2, r


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(2.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum (calibration case)
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Ratchet: each C call looks for a valid lift a bit larger than the current best.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    fails = 0

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 3.0 or fails > 6:
            break
        k = pick_k()
        n_best = best[0]
        G_need = n_best // (2 * k) + 1 + rng.randrange(0, 2 + n_best // (40 * k))
        m, k2, r = _sample_group(G_need, rng)
        slice_s = min(remaining - 1.0, 5.0 + 4.0 * rng.random())
        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", m, k2, r, k],
                            timeout=slice_s + 15.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            fails += 1
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
