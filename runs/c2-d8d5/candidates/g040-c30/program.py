import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# A candidate is a lift of a base graph with 2K vertex blocks (A-blocks 0..K-1,
# B-blocks K..2K-1) over the semidirect product G = Z_m x| Z_k2 (element a*k2+b,
# product (a,b)(c,e) = (a + r^b c, b+e)). Layer l pairs A-block i with B-block
# sig[l][i] (a permutation per layer) through voltage S[l][i]: vertex (i,g) is
# joined to (sig, g*s). Every vertex then has degree d_ exactly when no two
# layers repeat the same (i, sig, s).
#
# Left multiplication by G is an automorphism, so the diameter is <= D iff every
# vertex lies within distance D of each of the 2K identity vertices. Reachability
# is therefore a 2K-bit mask per vertex, which makes each evaluation cheap.
# The cost is the number of unreached (vertex, source-block) pairs plus a penalty
# per duplicated dart. Each success is recorded, and the next target must be
# strictly larger.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define KMAX 8
#define PEN 1000LL
#define ITERS 20000
#define STAG 2500

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_;
static int K, G, k2, m_;
static int pw[64];
static int *S, *sig, *nbr;
static u64 *reach, *nreach;
static int cap_v = 0;
static int NV;
static int cap_e = 0;
static int *bestU, *bestV;
static double t_limit;
static clock_t c_start;

static int time_up(void) {
    return (double)(clock() - c_start) / CLOCKS_PER_SEC >= t_limit;
}

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long A = ((long long)a + (long long)pw[b] * c) % m_;
    int B = (b + e) % k2;
    return (int)(A * k2 + B);
}

static void set_block(int l, int i) {
    int j = sig[l * K + i];
    int s = S[l * K + i];
    for (int g = 0; g < G; g++) {
        int va = i * G + g;
        int vb = (K + j) * G + gmul(g, s);
        nbr[(size_t)va * d_ + l] = vb;
        nbr[(size_t)vb * d_ + l] = va;
    }
}

static void set_volt(int l, int i, int s) {
    S[l * K + i] = s;
    set_block(l, i);
}

static void swap_sig(int l, int i1, int i2) {
    int t = sig[l * K + i1];
    sig[l * K + i1] = sig[l * K + i2];
    sig[l * K + i2] = t;
    set_block(l, i1);
    set_block(l, i2);
}

static long long cost_eval(void) {
    int N = NV, full = 2 * K;
    for (int v = 0; v < N; v++) reach[v] = 0;
    for (int b = 0; b < 2 * K; b++) reach[(size_t)b * G] |= 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = reach[v];
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) x |= reach[nb[l]];
            nreach[v] = x;
            changed |= (x != reach[v]);
        }
        u64 *t = reach; reach = nreach; nreach = t;
        if (!changed) break;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) miss += full - __builtin_popcountll(reach[v]);
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (sig[l1 * K + i] == sig[l2 * K + i] && S[l1 * K + i] == S[l2 * K + i]) dup++;
    return miss + PEN * dup;
}

static void random_init(void) {
    int p[KMAX];
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            sig[l * K + i] = p[i];
            S[l * K + i] = rint_(G);
        }
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++) set_block(l, i);
}

static long long anneal(void) {
    long long cost = cost_eval();
    long long best = cost;
    long long since = 0;
    for (long long t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 127) == 0 && time_up()) break;
        double T = 4.0 * pow(0.05, (double)t / (double)ITERS);
        if (K >= 2 && rint_(100) < 25) {
            int l = rint_(d_);
            int i1 = rint_(K);
            int i2 = rint_(K - 1);
            if (i2 >= i1) i2++;
            swap_sig(l, i1, i2);
            long long nc = cost_eval();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else swap_sig(l, i1, i2);
        } else {
            int l = rint_(d_);
            int i = rint_(K);
            int old = S[l * K + i];
            int nw = rint_(G);
            if (nw == old) continue;
            set_volt(l, i, nw);
            long long nc = cost_eval();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else set_volt(l, i, old);
        }
        if (cost < best) { best = cost; since = 0; }
        else if (++since > STAG) break;
    }
    return cost;
}

static void ensure_cap(int want) {
    if (want <= cap_v) return;
    nbr = realloc(nbr, sizeof(int) * (size_t)want * d_);
    reach = realloc(reach, sizeof(u64) * (size_t)want);
    nreach = realloc(nreach, sizeof(u64) * (size_t)want);
    if (!nbr || !reach || !nreach) { printf("0 0\n"); exit(0); }
    cap_v = want;
}

static void save_best(void) {
    int A = K * G;
    int E = A * d_;
    if (E > cap_e) {
        cap_e = E;
        bestU = realloc(bestU, sizeof(int) * (size_t)E);
        bestV = realloc(bestV, sizeof(int) * (size_t)E);
        if (!bestU || !bestV) { printf("0 0\n"); exit(0); }
    }
    int idx = 0;
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++) {
            bestU[idx] = v;
            bestV[idx] = nbr[(size_t)v * d_ + l];
            idx++;
        }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    t_limit = atof(argv[4]);
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;
    if (d_ < 3 || D_ < 3) { printf("0 0\n"); return 0; }

    static const int K2LIST[12] = {1, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12};
    S = malloc(sizeof(int) * (size_t)d_ * KMAX);
    sig = malloc(sizeof(int) * (size_t)d_ * KMAX);
    if (!S || !sig) { printf("0 0\n"); return 0; }

    c_start = clock();
    long long hneed = min_n / 2 + 1;   /* need K*G >= hneed so that 2KG > min_n */
    long long best_nn = 0;
    int best_m = 0;

    while (!time_up()) {
        K = 1 + rint_(KMAX);
        k2 = K2LIST[rint_(12)];
        long long per = (long long)K * k2;
        long long mm = (hneed + per - 1) / per;
        mm += rint_(1 + (int)(mm / 64));
        if (mm < 2) mm = 2;
        if (mm > 2000000) continue;
        m_ = (int)mm;
        G = m_ * k2;
        if (2LL * K * G > 2000000LL) continue;

        int r = 1;
        if (k2 > 1) {
            r = -1;
            for (int tries = 0; tries < 400 && r < 0; tries++) {
                int c = 1 + rint_(m_ - 1);
                if (gcd_(c, m_) == 1 && powmod_(c, k2, m_) == 1 % m_) r = c;
            }
            if (r < 0) continue;
        }
        pw[0] = 1 % m_;
        for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);

        NV = 2 * K * G;
        ensure_cap(NV);
        random_init();
        long long c = anneal();
        if (c == 0) {
            save_best();
            best_nn = NV;
            best_m = K * G * d_;
            hneed = (long long)K * G + 1;
        }
    }

    if (best_nn == 0) { printf("0 0\n"); return 0; }
    printf("%lld %d\n", best_nn, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    if d == 1 or D == 2:
        return best  # K_{d,d} is optimal for bipartite D = 2 and trivial for d = 1

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # even cycle, optimal
        return best

    # Exact construction for D = 3 (calibration case): return immediately.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    # Araujo-Pardo / Lopez record family, degree q + 2 = d.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Bold phase: C annealer over bi-Cayley lifts on semidirect products,
    # with a strictly increasing size target.
    elapsed = time.monotonic() - t0
    budget = 0.85 * time_limit - elapsed - 2.0
    if budget >= 1.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", best[0]],
                stdin_graph=None,
                timeout=budget + 4.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
