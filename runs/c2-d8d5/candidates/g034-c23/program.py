import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealer over Z_M x| Z_K2 with K base vertices per side.
#
# The lift has N = 2*K*G vertices, where G is the group order. Block i on side A
# is vertex i*G + x. Block K+j on side B is vertex (K+j)*G + y. Each of the d
# layers is a perfect matching between the blocks, given by a permutation and
# a group element per block. The lift is G-invariant under left multiplication,
# so the diameter test needs BFS only from the 2K block representatives.
# The cost is the number of unreached (source, vertex) pairs plus duplicate
# darts. A cost-0 state is a valid graph. The annealer moves by changing one
# shift or swapping two targets inside one layer.
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

static int d_, D_, K_, G_, M_, K2_, N_;
static int *pw = NULL, *layer = NULL, *sh = NULL, *nbr = NULL, *stamp = NULL, *qbuf = NULL;
static int curstamp = 0;
static long long last_unr = 0;
static int *be_u = NULL, *be_v = NULL;
static int best_N = 0, best_m = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group Z_M x| Z_K2 with element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    int aa = (a + (pw[b] * c) % M_) % M_;
    return aa * K2_ + (b + e) % K2_;
}

static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    int v = (pw[nb] * a) % M_;
    int ap = (M_ - v) % M_;
    return ap * K2_ + nb;
}

static int sample_group(int Gt) {
    static const int K2s[13] = {1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 8, 10, 12};
    for (int tries = 0; tries < 60; tries++) {
        int k2 = K2s[rint_(13)];
        if (k2 > Gt) k2 = 1;
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) { k2 = 1; m = Gt; }
        if (m < 2) return 0;
        int r = 1 % m;
        if (k2 >= 2 && m >= 3 && rint_(3) != 0) {
            int found = 0;
            for (int t = 0; t < 200 && !found; t++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; found = 1; }
            }
            if (!found) continue;
        }
        M_ = m;
        K2_ = k2;
        G_ = m * k2;
        pw = realloc(pw, sizeof(int) * (size_t)k2);
        pw[0] = 1 % m;
        for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
        return 1;
    }
    return 0;
}

static void set_dart(int l, int i) {
    int j = layer[l * K_ + i], s = sh[l * K_ + i];
    int si = ginv(s);
    int G = G_;
    int *row = nbr + (size_t)l * N_;
    for (int x = 0; x < G; x++) {
        row[i * G + x] = (K_ + j) * G + gmul(x, s);
        row[(K_ + j) * G + x] = i * G + gmul(x, si);
    }
}

static long long eval_cost(void) {
    long long unr = 0;
    if (curstamp >= 1000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)N_);
        curstamp = 0;
    }
    for (int s = 0; s < 2 * K_; s++) {
        curstamp++;
        int h = 0, t = 0;
        int src = s * G_;
        qbuf[t++] = src;
        stamp[src] = curstamp;
        for (int depth = 0; depth < D_ && h < t && t < N_; depth++) {
            int end = t;
            while (h < end) {
                int v = qbuf[h++];
                for (int l = 0; l < d_; l++) {
                    int u = nbr[(size_t)l * N_ + v];
                    if (stamp[u] != curstamp) {
                        stamp[u] = curstamp;
                        qbuf[t++] = u;
                    }
                }
            }
        }
        unr += N_ - t;
    }
    last_unr = unr;
    long long dup = 0;
    for (int i = 0; i < K_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (layer[l1 * K_ + i] == layer[l2 * K_ + i] && sh[l1 * K_ + i] == sh[l2 * K_ + i])
                    dup++;
    return unr + dup;
}

static int run_sa(double seconds, long long max_iters) {
    long long cur = eval_cost();
    if (last_unr == 0) return 1;
    const double T0 = 4.0, T1 = 0.3;
    clock_t c0 = clock();
    double frac = 0.0;
    for (long long it = 0; it < max_iters; it++) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= seconds) break;
            frac = el / seconds;
        }
        double T = T0 * pow(T1 / T0, frac);
        if (K_ >= 2 && rint_(100) < 25) {
            int l = rint_(d_);
            int i1 = rint_(K_), i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int *a = &layer[l * K_ + i1], *b = &layer[l * K_ + i2];
            int tmp = *a; *a = *b; *b = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long long nc = eval_cost();
            if (last_unr == 0) return 1;
            long long dl = nc - cur;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cur = nc;
            } else {
                tmp = *a; *a = *b; *b = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rint_(d_), i = rint_(K_);
            int idx = l * K_ + i;
            int old = sh[idx];
            int nw = rint_(G_);
            if (nw == old) continue;
            sh[idx] = nw;
            set_dart(l, i);
            long long nc = eval_cost();
            if (last_unr == 0) return 1;
            long long dl = nc - cur;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cur = nc;
            } else {
                sh[idx] = old;
                set_dart(l, i);
            }
        }
    }
    return 0;
}

static void record(void) {
    int m = 0;
    int *nu = realloc(be_u, sizeof(int) * (size_t)d_ * N_);
    int *nv = realloc(be_v, sizeof(int) * (size_t)d_ * N_);
    if (!nu || !nv) return;
    be_u = nu;
    be_v = nv;
    for (int v = 0; v < N_; v++) {
        for (int l = 0; l < d_; l++) {
            int u = nbr[(size_t)l * N_ + v];
            if (u <= v) continue;
            int dupl = 0;
            for (int l2 = 0; l2 < l; l2++)
                if (nbr[(size_t)l2 * N_ + v] == u) { dupl = 1; break; }
            if (!dupl) {
                be_u[m] = v;
                be_v[m] = u;
                m++;
            }
        }
    }
    best_N = N_;
    best_m = m;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double limit = atof(argv[4]);
    long long tgt = argc > 5 ? atoll(argv[5]) : 2;
    if (tgt < 2) tgt = 2;
    if (d_ < 1 || D_ < 1) {
        printf("0 0\n");
        return 0;
    }

    clock_t c0 = clock();
    long long trials[9] = {0}, wins[9] = {0};
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        double rem = limit - el;
        if (rem < 0.3) break;

        int k;
        if (rint_(4) == 0) {
            k = 1 + rint_(8);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= 8; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.05 * rdbl();
                if (v > bv) { bv = v; k = kk; }
            }
        }

        long long Gt = (tgt + 2LL * k - 1) / (2LL * k);
        if (best_N > 0) {
            long long g2 = best_N / (2 * k) + 1;
            if (Gt < g2) Gt = g2;
        }
        if (rint_(3) == 0) Gt += rint_(3);
        if (Gt < 2) Gt = 2;
        if (Gt > 200000) break;

        K_ = k;
        if (!sample_group((int)Gt)) continue;
        N_ = 2 * K_ * G_;
        if (N_ <= best_N || N_ > 400000) continue;

        nbr = malloc(sizeof(int) * (size_t)d_ * N_);
        layer = malloc(sizeof(int) * (size_t)d_ * K_);
        sh = malloc(sizeof(int) * (size_t)d_ * K_);
        stamp = calloc((size_t)N_, sizeof(int));
        qbuf = malloc(sizeof(int) * (size_t)N_);
        if (!nbr || !layer || !sh || !stamp || !qbuf) break;

        for (int l = 0; l < d_; l++) {
            int p[16];
            for (int i = 0; i < K_; i++) p[i] = i;
            for (int i = K_ - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            for (int i = 0; i < K_; i++) {
                layer[l * K_ + i] = p[i];
                sh[l * K_ + i] = rint_(G_);
            }
        }
        for (int l = 0; l < d_; l++)
            for (int i = 0; i < K_; i++)
                set_dart(l, i);

        double slice = 2.0 + 4.0 * rdbl();
        if (slice > rem) slice = rem;
        trials[k]++;
        int ok = run_sa(slice, 1LL << 40);
        if (ok) {
            wins[k]++;
            record();
            tgt = best_N + 2;
        } else {
            long long base = best_N + 2;
            long long gap = tgt - base;
            if (gap < 0) gap = 0;
            tgt = base + (gap * 3) / 4;
        }

        free(nbr); nbr = NULL;
        free(layer); layer = NULL;
        free(sh); sh = NULL;
        free(stamp); stamp = NULL;
        free(qbuf); qbuf = NULL;
    }

    if (best_N == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_N, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", be_u[i], be_v[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

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

    # C voltage-lift search. The start target is a fraction of the Moore bound;
    # the C side lowers it after failures, so a too-high start still recovers.
    remaining = time_limit - (time.monotonic() - t0)
    budget = min(remaining - 9.0, remaining * 0.85)
    if budget >= 1.0:
        try:
            moore = lib.moore_bound(d, D)
            start = max(best[0] + 2, int(0.3 * moore))
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", start],
                timeout=budget + 20.0,
            )
            cn, ce = lib.parse_graph_text(out)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
