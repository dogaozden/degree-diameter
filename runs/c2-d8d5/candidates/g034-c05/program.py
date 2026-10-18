import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# A graph on 2KG vertices: left blocks 0..K-1 and right blocks K..2K-1, each
# block a copy of a group G = Z_m x| Z_k2. Layer l (0..d-1) joins left block i
# to right block sig[l][i] through voltage sv[l][i]:
#     (i, g) ~ (K + sig[l][i], g * sv[l][i]).
# Each layer is a perfect matching on blocks, so every vertex has degree exactly d.
# Cost = ordered pairs at distance > D (bitset ball expansion) + PEN * duplicate darts.
# A zero-cost state is a valid graph. The search tries random base sizes K and
# groups, and adapts its target size: it grows after success and backs off after failure.
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
static int K_ = 1, G_ = 1, N_ = 2, W_ = 1;
static int *mulT = NULL, *invT = NULL, *pw = NULL;
static int *sig = NULL, *sinv = NULL, *sv = NULL, *nb = NULL;
static u64 *bufA = NULL, *bufB = NULL;
static int bestN = 0, bestM = 0;
static int *bestE = NULL;
static const long long PEN = 1000;
static clock_t cstart;

static double elapsed(void) { return (double)(clock() - cstart) / CLOCKS_PER_SEC; }

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void build_group(int m, int k2, int r) {
    G_ = m * k2;
    free(mulT); free(invT); free(pw);
    mulT = malloc(sizeof(int) * (size_t)G_ * G_);
    invT = malloc(sizeof(int) * (size_t)G_);
    pw = malloc(sizeof(int) * (size_t)k2);
    for (int b = 0; b < k2; b++) pw[b] = powmod_(r, b, m);
    for (int x = 0; x < G_; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G_; y++) {
            int c = y / k2, e = y % k2;
            long long aa = ((long long)a + (long long)pw[b] * c) % m;
            mulT[(size_t)x * G_ + y] = (int)(aa * k2 + (b + e) % k2);
        }
    }
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            if (mulT[(size_t)x * G_ + y] == 0) { invT[x] = y; break; }
}

static void build_nb(void) {
    int K = K_, G = G_, d = d_;
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = sig[l * K + i];
                int s = sv[l * K + i];
                nb[v * d + l] = (K + j) * G + mulT[g * G + s];
            }
        }
    for (int j = 0; j < K; j++)
        for (int h = 0; h < G; h++) {
            int v = (K + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = sinv[l * K + j];
                int s = sv[l * K + i];
                nb[v * d + l] = i * G + mulT[h * G + invT[s]];
            }
        }
}

static int dup_count(void) {
    int c = 0, K = K_, d = d_;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (sig[l1 * K + i] == sig[l2 * K + i] && sv[l1 * K + i] == sv[l2 * K + i]) c++;
    return c;
}

static long long total_cost(void) {
    build_nb();
    int N = N_, W = W_, D = D_, d = d_;
    u64 *cur = bufA, *alt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * W;
            u64 *r = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int l = 0; l < d; l++) {
                u64 *q = cur + (size_t)nb[v * d + l] * W;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt + PEN * (long long)dup_count();
}

static void save_graph(void) {
    build_nb();
    int K = K_, G = G_, d = d_;
    int M = K * G * d;
    int *e = malloc(sizeof(int) * 2 * (size_t)M);
    int c = 0;
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) {
            e[2 * c] = v;
            e[2 * c + 1] = nb[v * d + l];
            c++;
        }
    free(bestE);
    bestE = e;
    bestM = M;
    bestN = N_;
}

static void random_init(void) {
    int K = K_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) sig[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig[l * K + i];
            sig[l * K + i] = sig[l * K + j];
            sig[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) sinv[l * K + sig[l * K + i]] = i;
        for (int i = 0; i < K; i++) sv[l * K + i] = rint_(G);
    }
}

static void swap_sig(int l, int i1, int i2) {
    int K = K_;
    int a = sig[l * K + i1], b = sig[l * K + i2];
    sig[l * K + i1] = b;
    sig[l * K + i2] = a;
    sinv[l * K + b] = i1;
    sinv[l * K + a] = i2;
}

static int anneal(double t_start, double slice) {
    long long cost = total_cost();
    if (cost == 0) { save_graph(); return 1; }
    double c0 = (double)cost;
    double T0 = 0.02 * c0 + 20.0, T1 = 1.0;
    int K = K_, d = d_, G = G_;
    while (1) {
        double frac = (elapsed() - t_start) / slice;
        if (frac >= 1.0) break;
        double T = T0 * pow(T1 / T0, frac);
        if (K >= 2 && rint_(2) == 1) {
            int l = rint_(d), i1 = rint_(K), i2 = rint_(K);
            if (i1 == i2) continue;
            swap_sig(l, i1, i2);
            long long nc = total_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else swap_sig(l, i1, i2);
        } else {
            int idx = rint_(d * K);
            int old = sv[idx];
            int nw = rint_(G);
            if (nw == old) continue;
            sv[idx] = nw;
            long long nc = total_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else sv[idx] = old;
        }
        if (cost == 0) { save_graph(); return 1; }
    }
    return 0;
}

static const int K2_CHOICES[11] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};

static int try_config(int tgt, int k) {
    int d = d_;
    int G0 = (tgt + 2 * k - 1) / (2 * k);
    if (G0 < d + 1) G0 = d + 1;
    int k2 = K2_CHOICES[rint_(11)];
    int m = (G0 + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1) {
        int found = 0;
        if (m >= 3)
            for (int t = 0; t < 200 && !found; t++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) { r = c; found = 1; }
            }
        if (!found) { k2 = 1; m = G0; r = 1; }
    }
    long long G = (long long)m * k2;
    if (G > 1200) return 0;
    K_ = k;
    build_group(m, k2, r);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    cstart = clock();
    if (d_ < 3 || D_ < 2 || d_ > 64) { printf("0 0\n"); return 0; }

    int step = 2;
    while (1) {
        double rem = limit - elapsed();
        if (rem < 0.5) break;
        int base = bestN > 0 ? bestN : 2 * d_;
        int tgt = base + step;
        int k = 1 + rint_(5);
        if (!try_config(tgt, k)) continue;

        N_ = 2 * K_ * G_;
        W_ = (N_ + 63) / 64;
        free(bufA); free(bufB); free(sig); free(sinv); free(sv); free(nb);
        bufA = malloc(sizeof(u64) * (size_t)N_ * W_);
        bufB = malloc(sizeof(u64) * (size_t)N_ * W_);
        sig = malloc(sizeof(int) * (size_t)d_ * K_);
        sinv = malloc(sizeof(int) * (size_t)d_ * K_);
        sv = malloc(sizeof(int) * (size_t)d_ * K_);
        nb = malloc(sizeof(int) * (size_t)N_ * d_);
        if (!bufA || !bufB || !sig || !sinv || !sv || !nb) break;

        random_init();
        double slice = rem < 6.0 ? rem : 6.0;
        int ok = anneal(elapsed(), slice);
        if (ok) {
            step = step * 2 > 256 ? 256 : step * 2;
        } else {
            step = step / 2 < 2 ? 2 : step / 2;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum for this case: return immediately

    # Bold step: C search over bi-Cayley lifts of varying base size and group.
    remaining = time_limit - (time.monotonic() - t0)
    budget = remaining - 12.0  # margin for compilation, parsing and validation
    if d >= 3 and D >= 2 and budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=None, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
