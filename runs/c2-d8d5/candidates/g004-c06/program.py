import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef uint32_t u32;

#define KMAX 8
#define TRIAL_IT 20000
#define STALL_IT 6000
#define NMAX_SAFE 400000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static const int KLIST[] = {1, 2, 2, 3, 3, 4, 4, 5, 6, 8};
static const int K2LIST[] = {1, 1, 1, 2, 2, 2, 3, 4, 4, 5, 6, 6, 8, 8, 10, 12, 14, 16, 18, 20, 24, 30, 36};
#define NKL ((int)(sizeof(KLIST) / sizeof(KLIST[0])))
#define NK2 ((int)(sizeof(K2LIST) / sizeof(K2LIST[0])))

/* Bi-Cayley lift over G = Z_M x| Z_K2 with K blocks per side.
   Vertex id = block * G + element; A blocks 0..K-1, B blocks K..2K-1.
   Layer l, block i: A_{i,g} ~ B_{perm[l][i], g*volt[l][i]}.
   The group acts by left multiplication, so only the 2K block
   representatives need to reach everything within D_ steps. */

static int d_, D_;
static int K_, K2_, M_, G_, N_, R_;
static int pw[64];
static int *ga = NULL, *gb = NULL;
static int gcap = 0;
static int *perm = NULL, *volt = NULL;
static int *nb = NULL;
static u32 *rA = NULL, *rB = NULL;
static int ncap = 0;
static int have_best = 0;
static int bK, bK2, bM, bR, bN;
static int *bperm = NULL, *bvolt = NULL;

static void finish(void);

static void ensure_cap(int N) {
    if (N <= ncap) return;
    int c = N + N / 2 + 64;
    int *nn = realloc(nb, sizeof(int) * (size_t)c * (size_t)d_);
    u32 *a = realloc(rA, sizeof(u32) * (size_t)c);
    u32 *b = realloc(rB, sizeof(u32) * (size_t)c);
    if (!nn || !a || !b) { printf("0 0\n"); exit(0); }
    nb = nn; rA = a; rB = b; ncap = c;
}

static void ensure_g(int G) {
    if (G <= gcap) return;
    int c = G + 64;
    int *x = realloc(ga, sizeof(int) * (size_t)c);
    int *y = realloc(gb, sizeof(int) * (size_t)c);
    if (!x || !y) { printf("0 0\n"); exit(0); }
    ga = x; gb = y; gcap = c;
}

static void set_config(int k, int k2, int M, int r) {
    K_ = k; K2_ = k2; M_ = M; G_ = M * k2; N_ = 2 * k * G_; R_ = r;
    pw[0] = 1 % M;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % M);
    ensure_g(G_);
    for (int x = 0; x < G_; x++) { ga[x] = x / k2; gb[x] = x % k2; }
}

static inline int gmul(int x, int y) {
    long long t = (long long)ga[x] + (long long)pw[gb[x]] * ga[y];
    int aa = (int)(t % M_);
    int bb = gb[x] + gb[y];
    if (bb >= K2_) bb -= K2_;
    return aa * K2_ + bb;
}

static inline int ginv(int x) {
    int b = gb[x];
    int nbk = b ? K2_ - b : 0;
    long long t = ((long long)pw[nbk] * ga[x]) % M_;
    int ap = (int)((M_ - t) % M_);
    return ap * K2_ + nbk;
}

static long long pmod(long long b, long long e, long long m) {
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

static void sample_config(int T, int *ok, int *ok2, int *oM, int *oR) {
    for (int att = 0; att < 100; att++) {
        int k = KLIST[rint_(NKL)];
        int k2 = K2LIST[rint_(NK2)];
        long long need = ((long long)T + 2LL * k - 1) / (2LL * k);
        long long m = (need + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (2LL * k * m * k2 > NMAX_SAFE) continue;
        int M = (int)m;
        int R = 1;
        if (k2 > 1) {
            int cnt = 0, chosen = 1;
            for (int r = 2; r < M; r++) {
                if (gcd_i(r, M) != 1) continue;
                if (pmod(r, k2, M) != 1 % M) continue;
                cnt++;
                if (rint_(cnt) == 0) chosen = r;
            }
            if (cnt > 0) R = (rint_(10) < 9) ? chosen : 1;
        }
        *ok = k; *ok2 = k2; *oM = M; *oR = R;
        return;
    }
    *ok = 1; *ok2 = 1; *oM = 2; *oR = 1;
}

static void set_dart(int l, int i) {
    const int K = K_, G = G_, d = d_;
    int j = perm[l * KMAX + i];
    int s = volt[l * KMAX + i];
    int si = ginv(s);
    for (int g = 0; g < G; g++)
        nb[(size_t)(i * G + g) * d + l] = (K + j) * G + gmul(g, s);
    for (int x = 0; x < G; x++)
        nb[(size_t)((K + j) * G + x) * d + l] = i * G + gmul(x, si);
}

static void build_all(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++)
            set_dart(l, i);
}

/* Number of (representative, vertex) pairs at distance > D_. Zero means valid. */
static long long cost_eval(void) {
    const int N = N_, d = d_, full = 2 * K_;
    u32 *cur = rA, *alt = rB;
    memset(cur, 0, sizeof(u32) * (size_t)N);
    for (int b = 0; b < full; b++) cur[(size_t)b * G_] = 1u << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u32 x = cur[v];
            const int *q = nb + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[q[l]];
            alt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u32 *tmp = cur; cur = alt; alt = tmp;
        if (!changed) break;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) miss += full - __builtin_popcount(cur[v]);
    return miss;
}

static void save_best(void) {
    have_best = 1;
    bK = K_; bK2 = K2_; bM = M_; bR = R_; bN = N_;
    memcpy(bperm, perm, sizeof(int) * (size_t)d_ * KMAX);
    memcpy(bvolt, volt, sizeof(int) * (size_t)d_ * KMAX);
}

static void finish(void) {
    if (!have_best) { printf("0 0\n"); return; }
    set_config(bK, bK2, bM, bR);
    if (N_ > ncap) { printf("0 0\n"); return; }
    memcpy(perm, bperm, sizeof(int) * (size_t)d_ * KMAX);
    memcpy(volt, bvolt, sizeof(int) * (size_t)d_ * KMAX);
    build_all();
    const int d = d_;
    const int KG = K_ * G_;
    int *eu = malloc(sizeof(int) * (size_t)KG * (size_t)d);
    int *ev = malloc(sizeof(int) * (size_t)KG * (size_t)d);
    if (!eu || !ev) { printf("0 0\n"); return; }
    long long m = 0;
    for (int v = 0; v < KG; v++) {
        const int *q = nb + (size_t)v * d;
        for (int l = 0; l < d; l++) {
            int dup = 0;
            for (int l2 = 0; l2 < l; l2++) if (q[l2] == q[l]) { dup = 1; break; }
            if (!dup) { eu[m] = v; ev[m] = q[l]; m++; }
        }
    }
    printf("%d %lld\n", N_, m);
    for (long long i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
    fflush(stdout);
    free(eu);
    free(ev);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    double limit = atof(argv[4]);
    int T = argc > 5 ? atoi(argv[5]) : 2;
    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }
    if (T < 2) T = 2;

    perm = malloc(sizeof(int) * (size_t)d_ * KMAX);
    volt = malloc(sizeof(int) * (size_t)d_ * KMAX);
    bperm = malloc(sizeof(int) * (size_t)d_ * KMAX);
    bvolt = malloc(sizeof(int) * (size_t)d_ * KMAX);
    if (!perm || !volt || !bperm || !bvolt) { printf("0 0\n"); return 0; }

    clock_t c0 = clock();
    int target = T;
    int fails = 0;

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;

        int k, k2, M, R;
        sample_config(target, &k, &k2, &M, &R);
        set_config(k, k2, M, R);
        if (N_ > NMAX_SAFE) break;
        ensure_cap(N_);

        for (int l = 0; l < d_; l++) {
            for (int i = 0; i < K_; i++) perm[l * KMAX + i] = i;
            for (int i = K_ - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = perm[l * KMAX + i];
                perm[l * KMAX + i] = perm[l * KMAX + j];
                perm[l * KMAX + j] = t;
            }
            for (int i = 0; i < K_; i++) volt[l * KMAX + i] = rint_(G_);
        }
        build_all();

        long long cost = cost_eval();
        double Th0 = 0.05 * (double)(cost > 0 ? cost : 1);
        if (Th0 < 1.0) Th0 = 1.0;
        const double Th1 = 0.3;
        long long best_c = cost;
        int last_imp = 0;

        for (int it = 0; it < TRIAL_IT && cost > 0; it++) {
            if ((it & 127) == 0) {
                el = (double)(clock() - c0) / CLOCKS_PER_SEC;
                if (el >= limit) break;
            }
            if (it - last_imp > STALL_IT) break;
            double temp = Th0 * pow(Th1 / Th0, (double)it / TRIAL_IT);

            if (K_ >= 2 && rint_(100) < 35) {
                int l = rint_(d_);
                int i1 = rint_(K_);
                int i2 = rint_(K_ - 1);
                if (i2 >= i1) i2++;
                int *p = perm + l * KMAX;
                int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
                long long c2 = cost_eval();
                if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                } else {
                    t = p[i1]; p[i1] = p[i2]; p[i2] = t;
                    set_dart(l, i1);
                    set_dart(l, i2);
                }
            } else {
                int l = rint_(d_);
                int i = rint_(K_);
                int idx = l * KMAX + i;
                int old = volt[idx];
                int nw = rint_(G_);
                if (nw == old) continue;
                volt[idx] = nw;
                set_dart(l, i);
                long long c2 = cost_eval();
                if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                } else {
                    volt[idx] = old;
                    set_dart(l, i);
                }
            }
            if (cost < best_c) { best_c = cost; last_imp = it; }
        }

        if (cost == 0) {
            save_best();
            fails = 0;
            int n = N_;
            int step = n / 100;
            if (step < 2) step = 2;
            target = n + step;
        } else {
            fails++;
            if (fails >= 6 && have_best) {
                target = bN + 2;
                fails = 0;
            }
        }
    }

    finish();
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

    # Exact construction for D = 3 (calibration case): return immediately.
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

    # Main search: C bi-Cayley lift annealer over semidirect-product groups.
    elapsed = time.monotonic() - t0
    budget = time_limit - elapsed - max(5.0, 0.15 * time_limit)
    if budget >= 2.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", best[0] + 2],
                stdin_graph=None,
                timeout=budget + 8.0,
            )
            cn, ce = lib.parse_graph_text(out)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
