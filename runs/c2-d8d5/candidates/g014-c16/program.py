import time

import lib


# ----------------------------------------------------------------------------
# New construction: cyclic voltage lifts of small bipartite base multigraphs.
#
# A candidate is K base vertices per side and d "layers". Layer l joins A-vertex
# i to B-vertex sig[l][i] with voltage volt[l][i] in Z_M, so the lift has vertices
# A(i,g), B(j,h) for g,h in Z_M and edges A(i,g)-B(sig[l][i], g+volt[l][i]).
# Every layer is a perfect matching of the lift, so the lift is d-regular.
#
# Translation by Z_M is an automorphism, so the diameter check only needs BFS from
# the 2K block representatives (vertex with g = 0). A simulated annealer then
# changes voltages and layer permutations to reach zero far pairs. The C program
# grows the lift by bandit-chosen K, with M increased to exceed the best size so far.
# Duplicate darts are only penalised, since they do not change distances.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 16
#define MAXN 24000
#define PATIENCE 8000
#define MAXIT 30000

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K, M, N;
static int sig[MAXD][MAXK], sinv[MAXD][MAXK], volt[MAXD][MAXK];
static int bsig[MAXD][MAXK], bvolt[MAXD][MAXK];
static int bestK = 0, bestM = 0, best_n = 0;
static int mark[MAXN], dd[MAXN], dq[MAXN];
static int stampc = 0;

static void recompute_inv(int l) {
    for (int i = 0; i < K; i++) sinv[l][sig[l][i]] = i;
}

/* Number of vertices within distance D_ of src (BFS in the implicit lift). */
static int bfs_within(int src) {
    int h = 0, t = 0, cnt = 0;
    stampc++;
    mark[src] = stampc; dd[src] = 0; dq[t++] = src;
    while (h < t) {
        int v = dq[h++];
        cnt++;
        int dv = dd[v];
        if (dv >= D_) continue;
        int p = v / M, g = v - p * M;
        if (p < K) {
            for (int l = 0; l < d_; l++) {
                int x = g + volt[l][p];
                if (x >= M) x -= M;
                int u = (K + sig[l][p]) * M + x;
                if (mark[u] != stampc) { mark[u] = stampc; dd[u] = dv + 1; dq[t++] = u; }
            }
        } else {
            int j = p - K;
            for (int l = 0; l < d_; l++) {
                int i = sinv[l][j];
                int x = g - volt[l][i];
                if (x < 0) x += M;
                int u = i * M + x;
                if (mark[u] != stampc) { mark[u] = stampc; dd[u] = dv + 1; dq[t++] = u; }
            }
        }
    }
    return cnt;
}

/* Sum over the 2K representatives of the number of far vertices. Zero iff valid. */
static long long far_cost(void) {
    long long s = 0;
    for (int p = 0; p < 2 * K; p++) s += N - bfs_within(p * M);
    return s;
}

static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (sig[l1][i] == sig[l2][i] && volt[l1][i] == volt[l2][i]) c++;
    return c;
}

static long long full_cost(void) { return far_cost() + 2LL * dup_count(); }

static void random_init(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) sig[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rint_(i + 1);
            int t = sig[l][i]; sig[l][i] = sig[l][r]; sig[l][r] = t;
        }
        recompute_inv(l);
        for (int i = 0; i < K; i++) volt[l][i] = rint_(M);
    }
}

/* Simulated annealing from a random start. Returns 1 if the lift is valid. */
static int attempt(int maxIters, double T0, double T1, clock_t deadline) {
    random_init();
    long long cost = full_cost();
    long long bestc = cost;
    int last = 0;
    for (int t = 0; t < maxIters && cost > 0; t++) {
        if ((t & 127) == 0 && clock() >= deadline) break;
        if (t - last > PATIENCE) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)maxIters);
        int l = rint_(d_), i = rint_(K);
        if (K >= 2 && rdbl() < 0.4) {
            int i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = tmp;
            recompute_inv(l);
            long long nc = full_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = tmp;
                recompute_inv(l);
            }
        } else {
            int old = volt[l][i];
            int nv = rint_(M);
            if (nv == old) continue;
            volt[l][i] = nv;
            long long nc = full_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                volt[l][i] = old;
            }
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return cost == 0;
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    if (d_ < 2 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }

    clock_t c0 = clock();
    clock_t deadline = c0 + (clock_t)(limit * (double)CLOCKS_PER_SEC);

    static const int Kc[9] = {1, 2, 3, 4, 5, 6, 8, 10, 12};
    int trials[9] = {0}, wins[9] = {0};

    while (clock() < deadline) {
        int ci;
        if (rdbl() < 0.25) {
            ci = rint_(9);
        } else {
            double bs = -1.0;
            ci = 0;
            for (int c = 0; c < 9; c++) {
                double s = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.05 * rdbl();
                if (s > bs) { bs = s; ci = c; }
            }
        }
        K = Kc[ci];
        M = best_n / (2 * K) + 1;
        if (M < 2) M = 2;
        N = 2 * K * M;
        trials[ci]++;
        if (N > MAXN) continue;
        if (attempt(MAXIT, 3.0, 0.2, deadline)) {
            wins[ci]++;
            if (N > best_n) {
                best_n = N;
                bestK = K;
                bestM = M;
                memcpy(bsig, sig, sizeof(sig));
                memcpy(bvolt, volt, sizeof(volt));
            }
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }

    K = bestK; M = bestM; N = 2 * K * M;
    memcpy(sig, bsig, sizeof(sig));
    memcpy(volt, bvolt, sizeof(volt));
    int cap = K * M * d_;
    long long *keys = malloc(sizeof(long long) * (size_t)cap);
    if (!keys) { printf("0 0\n"); return 0; }
    int ne = 0;
    for (int p = 0; p < K; p++)
        for (int g = 0; g < M; g++)
            for (int l = 0; l < d_; l++) {
                int a = p * M + g;
                int b = (K + sig[l][p]) * M + (g + volt[l][p]) % M;
                keys[ne++] = (long long)a * N + b;  /* a < b always */
            }
    qsort(keys, (size_t)ne, sizeof(long long), cmp_ll);
    int nu = 0;
    for (int i = 0; i < ne; i++) {
        if (nu == 0 || keys[i] != keys[nu - 1]) keys[nu++] = keys[i];
    }
    printf("%d %d\n", N, nu);
    for (int i = 0; i < nu; i++)
        printf("%lld %lld\n", keys[i] / N, keys[i] % N);
    free(keys);
    return 0;
}
"""


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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2, safe fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    budget = min(time_limit - 8.0, 0.85 * time_limit) - (time.monotonic() - t0)
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, int(seed) % (1 << 40), f"{budget:.2f}"],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
