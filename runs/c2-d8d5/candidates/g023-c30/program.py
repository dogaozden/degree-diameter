import time

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# A base graph has K vertices on each side. Layer l (one per degree slot,
# d layers in all) joins A_i to B_{perm_l(i)} with a voltage S_{l,i} in the
# group G. Vertices are (block, g) with g in G, and the group acts regularly
# on each block by left multiplication, so the diameter test only needs BFS
# from the 2K base vertices. A simulated annealer in C changes voltages and
# layer permutations until the lift has diameter <= D and no multi-edges. The
# search climbs in base-graph size: after each success it aims for a larger
# block count, trying random K and random groups of matching order.
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

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

#define MAXK 6
#define MAXG 2400
#define PEN 1000LL
#define MAXPW 64

static int d_, D_;
static int K_, G_, M_, K2_, R_;
static int pw_[MAXPW];
static int *MT_ = NULL, *IV_ = NULL;
static int *perm_, *iperm_, *S_;
static int *adj_, *vis_, *qa_;
static int vstamp_ = 0;
static int bestK = 0, bestG = 0, bestM = 0, bestK2 = 0, bestR = 0;
static int *bestPerm, *bestS;
static int candbuf[MAXG];

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod_(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e--) r = r * b % m;
    return (int)r;
}

/* Group Z_m x| Z_k2 with element a*k2+b, (a,b)(c,d) = (a + r^b c, b+d). */
static void setup_group(int m, int k2, int r) {
    M_ = m; K2_ = k2; R_ = r; G_ = m * k2;
    pw_[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw_[t] = (int)((long long)pw_[t - 1] * r % m);
    free(MT_); free(IV_);
    MT_ = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    IV_ = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G_; y++) {
            int c = y / k2, dd = y % k2;
            int p = (int)(((long long)a + (long long)pw_[b] * c) % m);
            MT_[(size_t)x * G_ + y] = p * k2 + (b + dd) % k2;
        }
    }
    for (int s = 0; s < G_; s++) {
        int a = s / k2, b = s % k2;
        int nb = (k2 - b) % k2;
        int c = (int)((m - ((long long)pw_[nb] * a) % m) % m);
        IV_[s] = c * k2 + nb;
    }
}

static void fix_iperm(int l) {
    int K = K_;
    for (int i = 0; i < K; i++) iperm_[l * K + perm_[l * K + i]] = i;
}

/* Vertices: block blk in [0,2K), element x in [0,G). A block i = blk < K, B block j = K + j.
   Edge: A_{i,x} -- B_{j,x*s} where j = perm_l(i), s = S_{l,i}. Returns total
   unreached (ordered, from the 2K base sources) plus PEN * duplicate darts. */
static long long build_and_eval(void) {
    int K = K_, G = G_, d = d_;
    int NN = 2 * K * G;
    for (int i = 0; i < K; i++) {
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < d; l++) {
                int j = perm_[l * K + i];
                int s = S_[l * K + i];
                adj_[(size_t)v * d + l] = (K + j) * G + MT_[x * G + s];
            }
        }
    }
    for (int j = 0; j < K; j++) {
        for (int y = 0; y < G; y++) {
            int v = (K + j) * G + y;
            for (int l = 0; l < d; l++) {
                int i = iperm_[l * K + j];
                int s = S_[l * K + i];
                adj_[(size_t)v * d + l] = i * G + MT_[y * G + IV_[s]];
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm_[l1 * K + i] == perm_[l2 * K + i] && S_[l1 * K + i] == S_[l2 * K + i]) dup++;

    long long total = 0;
    for (int b = 0; b < 2 * K; b++) {
        vstamp_++;
        int src = b * G;
        int head = 0, tail = 0;
        vis_[src] = vstamp_;
        qa_[tail++] = src;
        for (int lev = 0; lev < D_ && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int v = qa_[head++];
                const int *nb = adj_ + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = nb[l];
                    if (vis_[u] != vstamp_) { vis_[u] = vstamp_; qa_[tail++] = u; }
                }
            }
        }
        total += NN - tail;
    }
    return total + PEN * dup;
}

static void init_state(void) {
    int K = K_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int *p = perm_ + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        if (l > 0) {
            for (int i = K - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
        }
        for (int i = 0; i < K; i++) S_[l * K + i] = rint_(G);
        fix_iperm(l);
    }
}

static int attempt(long long iters, double deadline) {
    init_state();
    long long cost = build_and_eval();
    int K = K_, d = d_, G = G_;
    const double T0 = 50.0, T1 = 0.5;
    for (long long it = 0; it < iters && cost > 0; it++) {
        if ((it & 127) == 0 && now_s() >= deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (rdbl() < 0.75) {
            int idx = rint_(d * K);
            int old = S_[idx];
            int nw = rint_(G);
            if (nw == old) continue;
            S_[idx] = nw;
            long long nc = build_and_eval();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else S_[idx] = old;
        } else {
            int l = rint_(d);
            int i1 = rint_(K), i2 = rint_(K);
            if (i1 == i2) continue;
            int *p = perm_ + l * K;
            int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            fix_iperm(l);
            long long nc = build_and_eval();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else {
                t = p[i1]; p[i1] = p[i2]; p[i2] = t;
                fix_iperm(l);
            }
        }
    }
    return cost == 0;
}

static void save_best(void) {
    int K = K_, d = d_;
    bestK = K; bestG = G_; bestM = M_; bestK2 = K2_; bestR = R_;
    memcpy(bestPerm, perm_, sizeof(int) * (size_t)d * K);
    memcpy(bestS, S_, sizeof(int) * (size_t)d * K);
}

static void emit(void) {
    if (bestK == 0) { printf("0 0\n"); return; }
    int K = bestK, d = d_;
    setup_group(bestM, bestK2, bestR);
    K_ = K;
    memcpy(perm_, bestPerm, sizeof(int) * (size_t)d * K);
    memcpy(S_, bestS, sizeof(int) * (size_t)d * K);
    for (int l = 0; l < d; l++) fix_iperm(l);
    int G = G_;
    int NN = 2 * K * G;
    int m = K * G * d;
    printf("%d %d\n", NN, m);
    for (int i = 0; i < K; i++) {
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < d; l++) {
                int j = perm_[l * K + i];
                int s = S_[l * K + i];
                int u = (K + j) * G + MT_[x * G + s];
                printf("%d %d\n", v, u);
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    if (d_ < 1 || d_ > 200 || D_ < 1) { printf("0 0\n"); return 0; }

    int maxNN = 2 * MAXK * MAXG;
    perm_ = malloc(sizeof(int) * (size_t)d_ * MAXK);
    iperm_ = malloc(sizeof(int) * (size_t)d_ * MAXK);
    S_ = malloc(sizeof(int) * (size_t)d_ * MAXK);
    bestPerm = malloc(sizeof(int) * (size_t)d_ * MAXK);
    bestS = malloc(sizeof(int) * (size_t)d_ * MAXK);
    adj_ = malloc(sizeof(int) * (size_t)maxNN * d_);
    vis_ = malloc(sizeof(int) * (size_t)maxNN);
    qa_ = malloc(sizeof(int) * (size_t)maxNN);
    if (!perm_ || !iperm_ || !S_ || !bestPerm || !bestS || !adj_ || !vis_ || !qa_) {
        printf("0 0\n");
        return 0;
    }
    memset(vis_, 0, sizeof(int) * (size_t)maxNN);

    static const int kopt[15] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20};
    double hard = now_s() + limit;
    int best_half = 0;

    while (now_s() < hard - 0.3) {
        int K = 1 + rint_(MAXK);
        int win = 1 + rint_(1 + best_half / 40);
        int B = best_half + win;
        if (B < 2) B = 2;
        if (K > B) K = B;
        int k2 = kopt[rint_(15)];
        int tgtG = (B + K - 1) / K;
        int m = (tgtG + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > MAXG) continue;
        int r = 1;
        if (k2 > 1) {
            int nc = 0;
            for (int t = 1; t < m; t++)
                if (gcd_(t, m) == 1 && powmod_(t, k2, m) == 1 % m) candbuf[nc++] = t;
            if (nc == 0) continue;
            r = candbuf[rint_(nc)];
        }
        K_ = K;
        setup_group(m, k2, r);
        if (K_ * G_ < B) continue;
        double dl = now_s() + 3.0;
        if (dl > hard) dl = hard;
        if (attempt(40000, dl)) {
            if (K_ * G_ > best_half) {
                best_half = K_ * G_;
                save_best();
            }
        }
    }
    emit();
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
            return best

    budget = time_limit - (time.monotonic() - t0) - 8.0
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=None, timeout=budget + 15.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
