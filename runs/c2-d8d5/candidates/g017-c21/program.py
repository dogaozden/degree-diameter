import time

import lib


# ----------------------------------------------------------------------------
# C engine: single-orbit bi-Cayley (bipartite double cover) search.
#
# Group G = Z_M x|_R Z_K (non-abelian), order g. Connection set S of d distinct
# group elements. The graph on vertices (x,0), (x,1) for x in G has edges
# (x,0)-(x s,1) for s in S. Left multiplication is an automorphism, so the
# diameter is checked from only two sources, (e,0) and (e,1). Simulated
# annealing moves one element of S at a time. The search climbs the group
# order: each success raises the lower bound, so the best valid order grows
# over time.
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
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d_, D_;
static int M_, K_, R_, G_;
static int *pw_, *S_, *invS_, *RT_, *RIT_, *vis_, *dist_, *q_, *bestEu_, *bestEv_;
static int stamp_ = 0;
static int best_G_ = 0;

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void setup_group(int M, int K, int R) {
    M_ = M; K_ = K; R_ = R; G_ = M * K;
    pw_[0] = 1 % M;
    for (int b = 1; b < K; b++) pw_[b] = (int)((long long)pw_[b - 1] * R % M);
}

/* Element (a,b) is coded a*K+b; (a,b)(c,e) = (a + R^b c, b + e). */
static int mulg(int x, int y) {
    int a = x / K_, b = x % K_, c = y / K_, e = y % K_;
    int t = (int)((a + (long long)pw_[b] * c) % M_);
    return t * K_ + (b + e) % K_;
}

static int invg(int x) {
    int a = x / K_, b = x % K_;
    int nb = (K_ - b) % K_;
    int t = (int)((long long)pw_[nb] * a % M_);
    t = (M_ - t) % M_;
    return t * K_ + nb;
}

/* Random non-abelian semidirect group of order G: Z_M x| Z_K with R of order dividing K. */
static int find_group(int G, int *oM, int *oK, int *oR) {
    int cnt = 0, bM = 0, bK = 0, bR = 0;
    for (int K = 2; 3 * K <= G; K++) {
        if (G % K) continue;
        int M = G / K;
        for (int r = 2; r < M; r++) {
            if (gcd_i(r, M) != 1) continue;
            if (powmod(r, K, M) != 1 % M) continue;
            cnt++;
            if (rint_(cnt) == 0) { bM = M; bK = K; bR = r; }
        }
    }
    if (cnt == 0) return 0;
    *oM = bM; *oK = bK; *oR = bR;
    return 1;
}

static void set_row(int i) {
    invS_[i] = invg(S_[i]);
    for (int g = 0; g < G_; g++) {
        RT_[i * G_ + g] = mulg(g, S_[i]);
        RIT_[i * G_ + g] = mulg(g, invS_[i]);
    }
}

/* Number of nodes reached from src within D_ steps. Node g is (g,0), node G_+g is (g,1). */
static int bfs_reach(int src) {
    stamp_++;
    int h = 0, t = 0;
    q_[t++] = src;
    vis_[src] = stamp_;
    dist_[src] = 0;
    while (h < t) {
        int u = q_[h++];
        int du = dist_[u];
        if (du >= D_) continue;
        if (u < G_) {
            for (int i = 0; i < d_; i++) {
                int v = G_ + RT_[i * G_ + u];
                if (vis_[v] != stamp_) { vis_[v] = stamp_; dist_[v] = du + 1; q_[t++] = v; }
            }
        } else {
            int g = u - G_;
            for (int i = 0; i < d_; i++) {
                int v = RIT_[i * G_ + g];
                if (vis_[v] != stamp_) { vis_[v] = stamp_; dist_[v] = du + 1; q_[t++] = v; }
            }
        }
    }
    return t;
}

/* Unreached (source, target) pairs from the two sources (e,0) and (e,1). Zero means valid. */
static long long cost_of(void) {
    long long N = 2LL * G_;
    return (N - bfs_reach(0)) + (N - bfs_reach(G_));
}

static long long anneal(double seconds) {
    for (int i = 0; i < d_; i++) {
        int t, dup;
        do {
            t = rint_(G_);
            dup = 0;
            for (int j = 0; j < i; j++) if (S_[j] == t) { dup = 1; break; }
        } while (dup);
        S_[i] = t;
    }
    for (int i = 0; i < d_; i++) set_row(i);
    long long cost = cost_of();
    if (cost == 0) return 0;

    const double T0 = 10.0, T1 = 0.2;
    double T = T0;
    double t_start = cpu_now();
    long long it = 0;
    for (;;) {
        if ((it & 31) == 0) {
            double el = cpu_now() - t_start;
            if (el >= seconds) break;
            T = T0 * pow(T1 / T0, el / seconds);
        }
        it++;
        int i = rint_(d_);
        int t, dup;
        do {
            t = rint_(G_);
            dup = 0;
            for (int j = 0; j < d_; j++) if (S_[j] == t) { dup = 1; break; }
        } while (dup);
        int old = S_[i];
        S_[i] = t;
        set_row(i);
        long long nc = cost_of();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) return 0;
        } else {
            S_[i] = old;
            set_row(i);
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }
    if (lo < d_ + 1) lo = d_ + 1;
    if (hi > 200000) hi = 200000;
    if (hi < lo) { printf("0 0\n"); return 0; }

    pw_ = malloc(sizeof(int) * (size_t)(hi + 1));
    S_ = malloc(sizeof(int) * (size_t)d_);
    invS_ = malloc(sizeof(int) * (size_t)d_);
    RT_ = malloc(sizeof(int) * (size_t)d_ * (size_t)hi);
    RIT_ = malloc(sizeof(int) * (size_t)d_ * (size_t)hi);
    vis_ = calloc((size_t)(2 * hi), sizeof(int));
    dist_ = malloc(sizeof(int) * (size_t)(2 * hi));
    q_ = malloc(sizeof(int) * (size_t)(2 * hi));
    bestEu_ = malloc(sizeof(int) * (size_t)d_ * (size_t)hi);
    bestEv_ = malloc(sizeof(int) * (size_t)d_ * (size_t)hi);
    if (!pw_ || !S_ || !invS_ || !RT_ || !RIT_ || !vis_ || !dist_ || !q_ || !bestEu_ || !bestEv_) {
        printf("0 0\n");
        return 0;
    }

    double start = cpu_now();
    int cur_lo = lo;
    int window = 30;
    int fails = 0;
    while (1) {
        double rem = budget - (cpu_now() - start);
        if (rem < 0.2 || cur_lo > hi) break;
        int top = cur_lo + window;
        if (top > hi) top = hi;
        int G = cur_lo + rint_(top - cur_lo + 1);
        int M, K, R;
        if (G <= d_ || !find_group(G, &M, &K, &R)) {
            continue;
        }
        setup_group(M, K, R);
        double slice = 2.5 + 0.25 * fails;
        if (slice > 8.0) slice = 8.0;
        if (slice > rem) slice = rem;
        long long c = anneal(slice);
        if (c == 0) {
            best_G_ = G;
            for (int g = 0; g < G; g++) {
                for (int i = 0; i < d_; i++) {
                    int idx = g * d_ + i;
                    bestEu_[idx] = g;
                    bestEv_[idx] = G + RT_[i * G + g];
                }
            }
            cur_lo = G + 1;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (best_G_ == 0) { printf("0 0\n"); return 0; }
    int n = 2 * best_G_, m = best_G_ * d_;
    printf("%d %d\n", n, m);
    for (int idx = 0; idx < m; idx++) printf("%d %d\n", bestEu_[idx], bestEv_[idx]);
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

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
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
                return best  # exact Moore graph
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass

    # Main search: bi-Cayley double covers over non-abelian groups, climbing in order.
    moore_half = lib.moore_bound(d, D) // 2
    hi = min(moore_half, 6000)
    lo = max(d + 1, best[0] // 2 + 1)

    elapsed = time.monotonic() - t0
    budget = 0.85 * time_limit - elapsed - 3.0
    if budget >= 1.0 and lo <= hi:
        try:
            out = lib.run_c(C_SOURCE, [d, D, int(seed) & 0x3FFFFFFF, f"{budget:.2f}", lo, hi],
                            stdin_graph=None, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
