import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts of Z_m x| Z_k2.
#
# A lift has 2k blocks of G = m*k2 vertices (k on side A, k on side B). Vertex
# (block, g) is block*G + g. Layer l pairs A-block i with B-block layers[l][i]
# through the voltage s = S[l][i]: a(i,g) ~ b(j, g*s). Each layer is a
# permutation, so every vertex has exactly d neighbours.
#
# Left multiplication by a group element is an automorphism of the lift, so
# every block is vertex-transitive. The diameter is therefore at most D iff a
# BFS of depth D from the identity of each of the 2k blocks reaches all N
# vertices. The cost is the total number of unreached vertices over those 2k
# BFS runs, plus a penalty for duplicate darts. Zero means a valid graph.
#
# The engine ratchets: each valid lift becomes the new lower bound, and it
# searches for a group and voltages that give a strictly larger lift.
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

static int d_, D_;
static int k_, k2_, m_, G_, N_;
static int pw_[16];
static int *ea_, *eb_, *gi_;
static int *layers_, *S_, *bl_, *bs_, *Sinv_, *invL_, *nb_, *dist_, *queue_;
static int best_n = 0, best_k = 0, best_G = 0, found = 0;
static int *best_nb = NULL;

static clock_t c0;
static double limit_;
static double elapsed(void) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long long powmod_(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group element x = a*k2 + b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = ea_[x], b = eb_[x], c = ea_[y], e = eb_[y];
    int aa = (int)(((long long)a + (long long)pw_[b] * c) % m_);
    int ee = b + e;
    if (ee >= k2_) ee -= k2_;
    return aa * k2_ + ee;
}

static int ginv_calc(int x) {
    int a = ea_[x], b = eb_[x];
    int nbb = (k2_ - b) % k2_;
    long long t = (-(long long)pw_[nbb] * a) % m_;
    if (t < 0) t += m_;
    return (int)t * k2_ + nbb;
}

/* Random r with r^k2 = 1 mod m and gcd(r, m) = 1. Falls back to r = 1 (direct product). */
static int pick_r(int m, int k2) {
    if (k2 == 1 || m < 3) return 1;
    if (k2 % 2 == 0 && rint_(3) == 0) return m - 1;
    for (int t = 0; t < 200; t++) {
        int c = 2 + rint_(m - 2);
        if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) return c;
    }
    return 1;
}

static void build_nb(void) {
    const int k = k_, G = G_, d = d_;
    for (int q = 0; q < k * d; q++) Sinv_[q] = gi_[S_[q]];
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            invL_[l * k + layers_[l * k + i]] = i;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int q = l * k + i;
                nb_[v * d + l] = (k + layers_[q]) * G + gmul(g, S_[q]);
            }
        }
    for (int j = 0; j < k; j++)
        for (int h = 0; h < G; h++) {
            int v = (k + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = invL_[l * k + j];
                int q = l * k + i;
                nb_[v * d + l] = i * G + gmul(h, Sinv_[q]);
            }
        }
}

/* Two darts from the same A-block to the same B-block with the same voltage give a double edge. */
static int count_dups(void) {
    int dups = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++) {
                int q1 = l1 * k_ + i, q2 = l2 * k_ + i;
                if (layers_[q1] == layers_[q2] && S_[q1] == S_[q2]) dups++;
            }
    return dups;
}

static int bfs_reach(int src) {
    const int N = N_, d = d_, D = D_;
    for (int v = 0; v < N; v++) dist_[v] = -1;
    int h = 0, t = 0, cnt = 1;
    dist_[src] = 0;
    queue_[t++] = src;
    while (h < t) {
        int v = queue_[h++];
        int dv = dist_[v];
        if (dv >= D) continue;
        for (int l = 0; l < d; l++) {
            int u = nb_[v * d + l];
            if (dist_[u] < 0) {
                dist_[u] = dv + 1;
                queue_[t++] = u;
                cnt++;
            }
        }
    }
    return cnt;
}

static long long eval_cost(void) {
    build_nb();
    long long cost = 40LL * count_dups();
    for (int b = 0; b < 2 * k_; b++) cost += N_ - bfs_reach(b * G_);
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    limit_ = atof(argv[4]);
    int lb = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 2 || D_ < 2 || lb < 0) {
        printf("0 0\n");
        return 0;
    }
    best_n = lb;
    c0 = clock();

    static const int K2OPTS[9] = {1, 1, 2, 2, 3, 4, 5, 6, 8};
    const int d = d_;
    const double T0 = 4.0, T1 = 0.25;
    const int ITERS = 60000, PATIENCE = 6000;

    while (elapsed() < limit_) {
        int k = rint_(5) + 1;
        int k2 = K2OPTS[rint_(9)];
        int extra = rint_(3);
        int need = best_n / (2 * k) + 1;          /* ensures 2*k*G > best_n */
        int m = (need + k2 - 1) / k2 + extra;
        if (m < 2) m = 2;
        int r = pick_r(m, k2);
        int G = m * k2;
        int N = 2 * k * G;
        int K = k * d;

        k_ = k; k2_ = k2; m_ = m; G_ = G; N_ = N;
        pw_[0] = 1 % m;
        for (int t = 1; t < k2; t++) pw_[t] = (int)((long long)pw_[t - 1] * r % m);

        ea_ = malloc(sizeof(int) * G);
        eb_ = malloc(sizeof(int) * G);
        gi_ = malloc(sizeof(int) * G);
        for (int x = 0; x < G; x++) { ea_[x] = x / k2; eb_[x] = x % k2; }
        for (int x = 0; x < G; x++) gi_[x] = ginv_calc(x);

        layers_ = malloc(sizeof(int) * K);
        S_ = malloc(sizeof(int) * K);
        bl_ = malloc(sizeof(int) * K);
        bs_ = malloc(sizeof(int) * K);
        Sinv_ = malloc(sizeof(int) * K);
        invL_ = malloc(sizeof(int) * K);
        nb_ = malloc(sizeof(int) * (size_t)N * d);
        dist_ = malloc(sizeof(int) * N);
        queue_ = malloc(sizeof(int) * N);

        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) layers_[l * k + i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = layers_[l * k + i];
                layers_[l * k + i] = layers_[l * k + j];
                layers_[l * k + j] = t;
            }
            for (int i = 0; i < k; i++) S_[l * k + i] = rint_(G);
        }

        long long cost = eval_cost();
        int success = (cost == 0);
        long long bestc = cost;
        int last_imp = 0;

        for (int it = 0; !success && it < ITERS; it++) {
            if ((it & 127) == 0 && elapsed() >= limit_) break;
            if (it - last_imp > PATIENCE) break;
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            memcpy(bl_, layers_, sizeof(int) * K);
            memcpy(bs_, S_, sizeof(int) * K);
            if (k >= 2 && rint_(4) == 0) {
                int l = rint_(d);
                int i1 = rint_(k);
                int i2 = rint_(k - 1);
                if (i2 >= i1) i2++;
                int t = layers_[l * k + i1];
                layers_[l * k + i1] = layers_[l * k + i2];
                layers_[l * k + i2] = t;
            } else {
                S_[rint_(K)] = rint_(G);
            }
            long long nc = eval_cost();
            if (nc == 0) {
                success = 1;
                break;
            }
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
                if (cost < bestc) { bestc = cost; last_imp = it; }
            } else {
                memcpy(layers_, bl_, sizeof(int) * K);
                memcpy(S_, bs_, sizeof(int) * K);
            }
        }

        if (success) {
            free(best_nb);
            best_nb = malloc(sizeof(int) * (size_t)N * d);
            memcpy(best_nb, nb_, sizeof(int) * (size_t)N * d);
            best_n = N;
            best_k = k;
            best_G = G;
            found = 1;
        }

        free(ea_); free(eb_); free(gi_);
        free(layers_); free(S_); free(bl_); free(bs_);
        free(Sinv_); free(invL_); free(nb_); free(dist_); free(queue_);
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int A = best_k * best_G;
    printf("%d %d\n", 2 * A, A * d);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, best_nb[v * d + l]);
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
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]  # C_{2D}: bipartite, diameter D
        if lib.is_valid(n, cyc, d, D):
            return n, cyc

    best = lib.haar_graph(d, range(d))  # K_{d,d}
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = None
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Lift annealer in C, ratcheting up from the best known order.
    budget = time_limit - (time.monotonic() - t0) - 4.0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                            timeout=budget + 15.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
