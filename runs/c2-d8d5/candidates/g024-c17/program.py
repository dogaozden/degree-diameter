import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (voltage) lift search over semidirect products
# Z_m x|_r Z_k2, with k base vertices per side. Each attempt draws a random
# group of order about (best + 2)/(2k), then anneals layer permutations and
# voltages to make the lift d-regular with diameter <= D. Every success is
# kept and the search keeps trying larger groups until the time limit.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, N_, m_, k2_;
static int pw[16];
static int *lay, *S, *nbr;
static u32 *bufA, *bufB;
static int *bu, *bv, bm_ = 0, best_n = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod_(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int pc32(u32 x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

/* group element index x = a*k2 + b, a in Z_m, b in Z_k2; (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int ra = (int)(((long long)a + (long long)pw[b] * c) % m_);
    int rb = (b + e) % k2_;
    return ra * k2_ + rb;
}
static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = ((long long)pw[nb] * a) % m_;
    int na = (int)((m_ - t) % m_);
    return na * k2_ + nb;
}

/* Layer l maps left block i to right block lay[l*k+i] with voltage S[l*k+i]. */
static void set_dart(int l, int i) {
    int k = k_, G = G_, N = N_;
    int j = lay[l * k + i];
    int s = S[l * k + i];
    int si = ginv(s);
    int *nl = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        int v = i * G + g;
        int w = (k + j) * G + g;
        nl[v] = (k + j) * G + gmul(g, s);
        nl[w] = i * G + gmul(g, si);
    }
}

static long long dup_count(void) {
    long long c = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (lay[l * k_ + i] == lay[l2 * k_ + i] && S[l * k_ + i] == S[l2 * k_ + i]) c++;
    return c;
}

/* Number of (source block, vertex) pairs at distance > D_. Sources are the identities of the 2k blocks. */
static long long unreached(void) {
    int N = N_, k = k_, d = d_;
    u32 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u32) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G_] = 1u << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u32 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u32 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += pc32(cur[v]);
    return (long long)2 * k * N - cnt;
}

static const long long PEN = 1000;

static int anneal(int iters, int patience, double deadline) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int p[8];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k; i++) {
            lay[l * k + i] = p[i];
            S[l * k + i] = rint_(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);

    long long cost = unreached() + PEN * dup_count();
    long long c0 = cost > 1 ? cost : 1;
    long long bestc = cost;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 63) == 0 && (double)clock() / CLOCKS_PER_SEC > deadline) break;
        double temp = 0.01 * (double)c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rdbl() < 0.2) {
            int l = rint_(d), i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int a = l * k + i1, b = l * k + i2;
            int tmp = lay[a]; lay[a] = lay[b]; lay[b] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long long nc = unreached() + PEN * dup_count();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                tmp = lay[a]; lay[a] = lay[b]; lay[b] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
        } else {
            int l = rint_(d), i = rint_(k);
            int idx = l * k + i;
            int old = S[idx];
            int nw = rint_(G);
            if (nw == old) continue;
            S[idx] = nw;
            set_dart(l, i);
            long long nc = unreached() + PEN * dup_count();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                S[idx] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return cost == 0;
}

static void save_graph(void) {
    int N = N_, k = k_, d = d_;
    int cnt = k * G_ * d;
    free(bu); free(bv);
    bu = malloc(sizeof(int) * (size_t)cnt);
    bv = malloc(sizeof(int) * (size_t)cnt);
    int e = 0;
    for (int v = 0; v < k * G_; v++)
        for (int l = 0; l < d; l++) {
            bu[e] = v;
            bv[e] = nbr[(size_t)l * N + v];
            e++;
        }
    bm_ = e;
    best_n = N;
}

static void pick_group(int target, int *mo, int *ko, int *ro) {
    static const int K2s[] = {1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 9, 10, 12};
    int k2 = K2s[rint_(13)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2 && rdbl() < 0.8) {
        for (int t = 0; t < 400; t++) {
            int c = 2 + rint_(m - 2);
            if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    *mo = m; *ko = k2; *ro = r;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int need = atoi(argv[5]);
    int kmax = atoi(argv[6]);
    if (kmax < 1) kmax = 1;
    if (kmax > 4) kmax = 4;
    if (d_ < 1 || D_ < 1 || d_ > 1000) { printf("0 0\n"); return 0; }
    best_n = need;

    clock_t c0 = clock();
    double dl = (double)c0 / CLOCKS_PER_SEC + limit;
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;

        int cur = best_n;
        int k = 1 + rint_(kmax);
        int half = cur / (2 * k);
        int target = half + 1 + rint_(1 + half / 16);
        int m, k2, r;
        pick_group(target, &m, &k2, &r);
        int G = m * k2;
        if (2 * k * G <= cur) continue;

        /* set up the group for this attempt */
        m_ = m; k2_ = k2;
        for (int t = 0; t < k2; t++) pw[t] = (int)powmod_(r, t, m);
        G_ = G; k_ = k; N_ = 2 * k * G;

        lay = malloc(sizeof(int) * (size_t)d_ * k);
        S = malloc(sizeof(int) * (size_t)d_ * k);
        nbr = malloc(sizeof(int) * (size_t)d_ * N_);
        bufA = malloc(sizeof(u32) * (size_t)N_);
        bufB = malloc(sizeof(u32) * (size_t)N_);
        if (!lay || !S || !nbr || !bufA || !bufB) {
            free(lay); free(S); free(nbr); free(bufA); free(bufB);
            break;
        }

        int iters = 3000 + 10 * N_;
        int patience = iters / 4 + 500;
        int ok = anneal(iters, patience, dl);
        if (ok) save_graph();

        free(lay); free(S); free(nbr); free(bufA); free(bufB);
    }

    if (bm_ == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, bm_);
    for (int i = 0; i < bm_; i++) printf("%d %d\n", bu[i], bv[i]);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main search: C voltage-lift annealer over semidirect products.
    margin = max(3.0, 0.1 * time_limit)
    c_limit = time_limit - (time.monotonic() - t0) - margin
    if c_limit >= 2.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), f"{c_limit:.2f}", best[0], 4],
                stdin_graph=None,
                timeout=max(2.0, time_limit - (time.monotonic() - t0) - 1.5),
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
