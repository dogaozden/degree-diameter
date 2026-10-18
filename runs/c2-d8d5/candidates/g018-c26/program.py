import time

import lib


# ----------------------------------------------------------------------------
# C engine: orbit-reduced annealer for bi-Cayley lifts over Z_m x| Z_k2.
#
# Graph: k base vertices per side, each side a union of k blocks of size G.
# Layer t has a permutation lay[t] (A_i -> B_{lay[t][i]}) and a voltage
# sv[t][i] in the group, so A(i,g) ~ B(lay[t][i], g*sv[t][i]). This is d-regular.
#
# New idea: the group acts by left multiplication, regularly on every block,
# and this action is an automorphism. So the distance profile from A(i,g) is
# the same for every g. Validity therefore needs only 2k BFS runs, one from the
# identity of each block, instead of N. The cost is the total count of unreached
# (block, vertex) pairs, and it is zero exactly when the lift has diameter <= D.
# Dart duplicates (same i, j, voltage) are penalised separately to keep it simple.
#
# The engine searches for a valid lift of a target order. After each success
# it raises the target and keeps going, using random group choices per attempt.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXD 32

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int d_, D_, k_, G_, m_, k2_, N_;
static int pw[64];
static int lay[MAXD][MAXK], lay_inv[MAXD][MAXK], sv[MAXD][MAXK];
static int *nbtab = NULL, *stamp = NULL, *queue_ = NULL;
static int epoch_ = 0;
static int best_N = 0, best_M = 0;
static int *best_eu = NULL, *best_ev = NULL;

static const double T0 = 5.0, T1 = 0.2;
static const long long PEN = 8;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod_(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* (a,b)*(c,d) = (a + r^b c, b + d) in Z_m x| Z_k2, element coded a*k2+b. */
static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, d = y % k2_;
    return ((a + pw[b] * c) % m_) * k2_ + (b + d) % k2_;
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    int t = (pw[nb] * a) % m_;
    return ((m_ - t) % m_) * k2_ + nb;
}

static void setup_group(int k, int m, int k2, int r) {
    k_ = k; m_ = m; k2_ = k2; G_ = m * k2; N_ = 2 * k * G_;
    for (int b = 0; b < k2; b++) pw[b] = powmod_(r, b, m);
}

static void rebuild_inv(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++)
            lay_inv[l][lay[l][i]] = i;
}

static void build_table(void) {
    int N = N_, d = d_, k = k_, G = G_;
    for (int v = 0; v < N; v++) {
        for (int t = 0; t < d; t++) {
            int w;
            if (v < k * G) {
                int i = v / G, g = v % G, j = lay[t][i];
                w = (k + j) * G + gmul(g, sv[t][i]);
            } else {
                int j = v / G - k, h = v % G, i = lay_inv[t][j];
                w = i * G + gmul(h, ginv(sv[t][i]));
            }
            nbtab[v * d + t] = w;
        }
    }
}

/* Sum over the 2k block representatives of unreached vertices. Zero iff diameter <= D. */
static long long eval_cost(void) {
    int N = N_, d = d_, k = k_, G = G_;
    build_table();
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        epoch_++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = epoch_;
        for (int lev = 0; lev < D_ && h < t; lev++) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                const int *row = nbtab + (size_t)v * d;
                for (int q = 0; q < d; q++) {
                    int w = row[q];
                    if (stamp[w] != epoch_) { stamp[w] = epoch_; queue_[t++] = w; }
                }
            }
        }
        cost += N - t;
    }
    return cost;
}

static long long dupcount(void) {
    long long c = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (lay[l1][i] == lay[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long long total_cost(void) {
    return eval_cost() + PEN * dupcount();
}

static void record_best(void) {
    int N = N_, d = d_, k = k_, G = G_;
    if (N <= best_N) return;
    build_table();
    int M = (N * d) / 2;
    int *eu = malloc(sizeof(int) * (size_t)M);
    int *ev = malloc(sizeof(int) * (size_t)M);
    if (!eu || !ev) { free(eu); free(ev); return; }
    int c = 0;
    for (int v = 0; v < k * G; v++)
        for (int t = 0; t < d; t++) {
            eu[c] = v;
            ev[c] = nbtab[v * d + t];
            c++;
        }
    free(best_eu); free(best_ev);
    best_eu = eu; best_ev = ev;
    best_N = N; best_M = c;
}

static void random_init(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < k; i++) sv[l][i] = rint_(G);
    }
    rebuild_inv();
}

static int anneal(double secs) {
    double t_begin = now();
    long long cur = total_cost();
    double T = T0;
    int it = 0;
    static int blay[MAXD][MAXK], bsv[MAXD][MAXK];
    while (1) {
        if (cur == 0) { record_best(); return 1; }
        if ((it & 127) == 0) {
            double el = now() - t_begin;
            if (el >= secs) return 0;
            T = T0 * pow(T1 / T0, el / secs);
        }
        it++;
        memcpy(blay, lay, sizeof lay);
        memcpy(bsv, sv, sizeof sv);
        int d = d_, k = k_, G = G_;
        if (k >= 2 && rdbl() < 0.3) {
            int l = rint_(d);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
        } else {
            int l = rint_(d), i = rint_(k);
            sv[l][i] = rint_(G);
        }
        rebuild_inv();
        long long nc = total_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            memcpy(lay, blay, sizeof lay);
            memcpy(sv, bsv, sizeof sv);
            rebuild_inv();
        }
    }
}

static const int K2OPTS[13] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16};

static void pick_group(int target, int *k, int *m, int *k2, int *r) {
    *k = 1 + rint_(MAXK);
    *k2 = K2OPTS[rint_(13)];
    int per = 2 * (*k) * (*k2);
    int mm = (target + per - 1) / per;
    if (mm < 2) mm = 2;
    mm += rint_(3);
    *m = mm;
    int rr = 1 % mm;
    if (*k2 >= 2 && mm > 2) {
        if (*k2 == 2 && rint_(2) == 0) {
            rr = mm - 1;
        } else {
            for (int t = 0; t < 80; t++) {
                int c = 2 + rint_(mm - 2);
                if (gcd_(c, mm) == 1 && powmod_(c, *k2, mm) == 1 % mm) { rr = c; break; }
            }
        }
    }
    *r = rr;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    int target = argc > 5 ? atoi(argv[5]) : 64;
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (d_ < 2 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    if (target < 4) target = 4;

    double attempt = limit / 12.0;
    if (attempt < 1.0) attempt = 1.0;
    if (attempt > 4.0) attempt = 4.0;

    double end = now() + limit;
    while (1) {
        double rem = end - now();
        if (rem < 0.2) break;
        int k, m, k2, r;
        pick_group(target, &k, &m, &k2, &r);
        setup_group(k, m, k2, r);
        int N = N_;
        nbtab = malloc(sizeof(int) * (size_t)N * d_);
        stamp = calloc((size_t)N, sizeof(int));
        queue_ = malloc(sizeof(int) * (size_t)N);
        if (!nbtab || !stamp || !queue_) {
            free(nbtab); free(stamp); free(queue_);
            nbtab = NULL; stamp = NULL; queue_ = NULL;
            break;
        }
        random_init();
        double secs = rem < attempt ? rem : attempt;
        int ok = anneal(secs);
        free(nbtab); free(stamp); free(queue_);
        nbtab = NULL; stamp = NULL; queue_ = NULL;
        if (ok) {
            int step = N / 200;
            if (step < 2) step = 2;
            target = N + step;
        }
    }

    if (best_N == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_N, best_M);
    for (int i = 0; i < best_M; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
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


def _araujo(d):
    """Araujo-Pardo & Lopez graph of degree d (needs d - 2 a prime power >= 3), or None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: exact constructions, return immediately (calibration case included).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
        ar = _araujo(d)
        if ar is not None:
            consider(*ar)
        return best

    # D >= 4: orbit-reduced C annealer over bi-Cayley lifts, climbing the target order.
    remaining = time_limit - (time.monotonic() - t0) - 6.0
    if remaining >= 2.0 and d >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best[0] + 2],
                            timeout=remaining + 30.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
