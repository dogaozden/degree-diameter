import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage) lifts over semidirect products Z_m x| Z_k2.
#
# Base graph: K "A" blocks and K "B" blocks. Each of the d layers is a
# permutation sigma_l of the K blocks plus one voltage per A block. The lift
# joins A(i, g) to B(sigma_l(i), g * s_{l,i}) for every layer l. This gives a
# d-regular bipartite graph on 2*K*G vertices, and left multiplication by G is
# an automorphism. So the diameter is at most D iff every base vertex reaches
# all 2K*G vertices within D steps from its identity element. The cost is the
# total number of unreached (base vertex, vertex) pairs plus a penalty per
# duplicate dart. Simulated annealing moves voltages and within-layer swaps,
# and sometimes repairs a dart incident to an unreached vertex. Each success
# raises the target order and the search moves on to a new random
# (K, group) configuration. The best valid graph is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef unsigned long long u64;

#define MAXK 6
#define PEN 40

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (u64)n); }
static double rndd(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int d_, D_;
static int K_, G_, m_, k2_, NV_;
static int pw_[64];
static int *sig_ = NULL, *vol_ = NULL;
static int *nbr_ = NULL, *queue_ = NULL, *save_ = NULL;
static unsigned char *vis_ = NULL;
static int cap_ = 0;
static long long last_unr = 0;

static int best_n_ = 0;
static int best_m_ = 0;
static int *best_eu = NULL, *best_ev = NULL;

static void emit_best(void) {
    if (best_n_ == 0) { printf("0 0\n"); return; }
    printf("%d %d\n", best_n_, best_m_);
    for (int i = 0; i < best_m_; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
}

static void ensure_cap(int nv) {
    if (nv <= cap_) return;
    int c = nv + nv / 2 + 64;
    int *a = realloc(nbr_, sizeof(int) * (size_t)d_ * (size_t)c);
    int *b = realloc(queue_, sizeof(int) * (size_t)c);
    int *s = realloc(save_, sizeof(int) * (size_t)c);
    unsigned char *v = realloc(vis_, (size_t)2 * MAXK * (size_t)c);
    if (!a || !b || !s || !v) { emit_best(); exit(0); }
    nbr_ = a; queue_ = b; save_ = s; vis_ = v; cap_ = c;
}

static const int K2LIST[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 18, 20, 24};

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* Element (a, b) is coded a*k2 + b; (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2). */
static int gmul(int x, int y) {
    int a1 = x / k2_, b1 = x - a1 * k2_;
    int a2 = y / k2_, b2 = y - a2 * k2_;
    int a = (int)(((long long)a1 + (long long)pw_[b1] * a2) % m_);
    int b = (b1 + b2) % k2_;
    return a * k2_ + b;
}

static void setup_group(int Gt) {
    int nk = (int)(sizeof K2LIST / sizeof K2LIST[0]);
    int k2 = K2LIST[rndi(nk)];
    int m = (Gt + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2 && rndd() < 0.85) {
        for (int t = 0; t < 200; t++) {
            int c = 2 + rndi(m - 2);
            if (gcd_i(c, m) != 1) continue;
            long long p = 1;
            for (int b = 0; b < k2; b++) p = p * c % m;
            if (p == 1 % m) { r = c; break; }
        }
    }
    m_ = m; k2_ = k2; G_ = m * k2;
    pw_[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw_[b] = (int)((long long)pw_[b - 1] * r % m);
}

static void build_layer(int l) {
    int K = K_, G = G_, N = NV_;
    int *nb = nbr_ + (size_t)l * N;
    for (int i = 0; i < K; i++) {
        int j = sig_[l * K + i], s = vol_[l * K + i];
        for (int g = 0; g < G; g++) {
            int x = i * G + g;
            int y = (K + j) * G + gmul(g, s);
            nb[x] = y;
            nb[y] = x;
        }
    }
}

static void random_init(void) {
    int K = K_, G = G_, d = d_;
    for (int l = 0; l < d; l++) {
        int *p = sig_ + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) vol_[l * K + i] = rndi(G);
        build_layer(l);
    }
}

static long long eval_cost(void) {
    int K = K_, N = NV_, G = G_, d = d_;
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig_[l * K + i] == sig_[l2 * K + i] && vol_[l * K + i] == vol_[l2 * K + i]) dup++;
    long long unr = 0;
    for (int u = 0; u < 2 * K; u++) {
        unsigned char *V = vis_ + (size_t)u * N;
        memset(V, 0, (size_t)N);
        int h = 0, t = 0, st = u * G;
        V[st] = 1;
        queue_[t++] = st;
        for (int dep = 0; dep < D_ && h < t; dep++) {
            int end = t;
            while (h < end) {
                int x = queue_[h++];
                for (int l = 0; l < d; l++) {
                    int y = nbr_[(size_t)l * N + x];
                    if (!V[y]) { V[y] = 1; queue_[t++] = y; }
                }
            }
        }
        unr += N - t;
    }
    last_unr = unr;
    return unr + (long long)PEN * dup;
}

static int sample_unreached(void) {
    int N = NV_;
    for (int tries = 0; tries < 8; tries++) {
        int u = rndi(2 * K_);
        unsigned char *V = vis_ + (size_t)u * N;
        int s = rndi(N);
        for (int k = 0; k < N; k++) {
            int x = s + k;
            if (x >= N) x -= N;
            if (!V[x]) return x;
        }
    }
    return -1;
}

static void record_best(void) {
    int K = K_, N = NV_, G = G_, d = d_;
    size_t cnt = (size_t)K * (size_t)G * (size_t)d;
    int *eu = malloc(sizeof(int) * cnt);
    int *ev = malloc(sizeof(int) * cnt);
    if (!eu || !ev) { free(eu); free(ev); return; }
    size_t e = 0;
    for (int x = 0; x < K * G; x++)
        for (int l = 0; l < d; l++) {
            eu[e] = x;
            ev[e] = nbr_[(size_t)l * N + x];
            e++;
        }
    if (N > best_n_) {
        free(best_eu); free(best_ev);
        best_eu = eu; best_ev = ev;
        best_m_ = (int)cnt;
        best_n_ = N;
    } else {
        free(eu); free(ev);
    }
}

/* Anneal one random configuration for up to `slice` seconds. Returns 1 on success. */
static int sa_config(double slice) {
    int K = K_, N = NV_, G = G_, d = d_;
    random_init();
    long long cost = eval_cost();
    double ts = now_sec();
    const double T0 = 8.0, T1 = 0.2;
    while (cost > 0) {
        double el = now_sec() - ts;
        if (el >= slice) break;
        double T = T0 * pow(T1 / T0, el / slice);

        int type = 0, l = rndi(d), a = 0, b = 0, oldv = 0, tgt = 0;
        if (last_unr > 0 && rndd() < 0.5) {
            int x = sample_unreached();
            if (x >= 0) {
                tgt = 1;
                if (x < K * G) {
                    a = x / G;
                } else {
                    int j = x / G - K;
                    a = -1;
                    for (int i = 0; i < K; i++)
                        if (sig_[l * K + i] == j) { a = i; break; }
                    if (a < 0) continue;
                }
            }
        }
        if (!tgt) {
            if (K >= 2 && rndd() < 0.4) {
                type = 1;
                a = rndi(K);
                do { b = rndi(K); } while (b == a);
            } else {
                a = rndi(K);
            }
        }

        memcpy(save_, nbr_ + (size_t)l * N, sizeof(int) * (size_t)N);
        if (type == 0) {
            oldv = vol_[l * K + a];
            vol_[l * K + a] = rndi(G);
        } else {
            int t = sig_[l * K + a];
            sig_[l * K + a] = sig_[l * K + b];
            sig_[l * K + b] = t;
        }
        build_layer(l);
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            if (type == 0) {
                vol_[l * K + a] = oldv;
            } else {
                int t = sig_[l * K + a];
                sig_[l * K + a] = sig_[l * K + b];
                sig_[l * K + b] = t;
            }
            memcpy(nbr_ + (size_t)l * N, save_, sizeof(int) * (size_t)N);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    int Nt = atoi(argv[5]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || limit <= 0) { printf("0 0\n"); return 0; }
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (Nt < 2) Nt = 2;
    sig_ = malloc(sizeof(int) * (size_t)(MAXK * d_ + 8));
    vol_ = malloc(sizeof(int) * (size_t)(MAXK * d_ + 8));
    if (!sig_ || !vol_) { printf("0 0\n"); return 0; }

    double t0 = now_sec();
    while (1) {
        double remain = limit - (now_sec() - t0);
        if (remain < 0.2) break;
        int K = 1 + rndi(MAXK);
        int Gt = (Nt + 2 * K - 1) / (2 * K);
        if (Gt < 2) Gt = 2;
        setup_group(Gt);
        K_ = K;
        NV_ = 2 * K * G_;
        ensure_cap(NV_);
        double slice = remain < 4.0 ? remain : 4.0;
        if (sa_config(slice)) {
            record_best();
            int step = NV_ / 64;
            if (step < 2) step = 2;
            Nt = NV_ + step;
        }
    }
    emit_best();
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

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, always valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3 and pg is not None and lib.is_prime_power(d - 1):
            return best
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
            return best

    # Lift search in C. Budget leaves room for compilation and Python validation.
    c_limit = max(1.0, 0.82 * time_limit - 3.0 - (time.monotonic() - t0))
    if c_limit >= 2.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, int(seed) % (1 << 31), f"{c_limit:.2f}", best[0] + 2],
                timeout=c_limit + 8.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
