"""Voltage-lift search for bipartite graphs with max degree d and diameter D.

The construction is a bi-Cayley lift: k base vertices per side, d layers, and
each layer is a perfect matching between the two sides' base vertices with a
voltage in a group Z_m x| Z_k2. The lifted graph has 2*k*G vertices, is
d-regular and bipartite. The C engine anneals layer permutations and voltages
against a bitset reachability cost, using only identity-vertex seeds, which is
exact by group transitivity within blocks. Each run samples a new base size k
and group, so the search explores many non-cyclic groups.
"""
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

#define PEN 30
#define PAT 8000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d_, D_, k_, G_, m_, k2_, N_;
static int pw_buf[64];
static int *ea_ = NULL, *eb_ = NULL;
static int *lay_ = NULL, *sv_ = NULL;
static int *nbr_ = NULL, *bk_ = NULL;
static u32 *ra_ = NULL, *rb_ = NULL, *lastr_ = NULL;
static int capN_ = 0, capG_ = 0, capKD_ = 0;
static int *bestnbr_ = NULL;
static int capBest_ = 0;
static int best_n = 0, best_k = 0, best_G = 0, best_N = 0;

static void emit(void) {
    if (best_n == 0) { printf("0 0\n"); return; }
    int A = best_k * best_G;
    printf("%d %d\n", best_N, A * d_);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, bestnbr_[(size_t)l * best_N + v]);
}

static void ensure(int N, int G, int K) {
    if (N > capN_) {
        int nc = N + N / 2 + 64;
        int *p1 = realloc(nbr_, sizeof(int) * (size_t)nc * d_);
        int *p2 = realloc(bk_, sizeof(int) * (size_t)nc * d_);
        u32 *p3 = realloc(ra_, sizeof(u32) * (size_t)nc);
        u32 *p4 = realloc(rb_, sizeof(u32) * (size_t)nc);
        if (!p1 || !p2 || !p3 || !p4) { emit(); exit(0); }
        nbr_ = p1; bk_ = p2; ra_ = p3; rb_ = p4; capN_ = nc;
    }
    if (G > capG_) {
        int nc = G + G / 2 + 64;
        int *p1 = realloc(ea_, sizeof(int) * (size_t)nc);
        int *p2 = realloc(eb_, sizeof(int) * (size_t)nc);
        if (!p1 || !p2) { emit(); exit(0); }
        ea_ = p1; eb_ = p2; capG_ = nc;
    }
    if (K > capKD_) {
        int nc = K + 64;
        int *p1 = realloc(lay_, sizeof(int) * (size_t)nc);
        int *p2 = realloc(sv_, sizeof(int) * (size_t)nc);
        if (!p1 || !p2) { emit(); exit(0); }
        lay_ = p1; sv_ = p2; capKD_ = nc;
    }
}

static long long gcd_ll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long mod) {
    long long r = 1 % mod;
    b %= mod; if (b < 0) b += mod;
    while (e > 0) {
        if (e & 1) r = r * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x| Z_k2, element a*k2+b, (a,b)(c,d) = (a + r^b c, b+d). */
static int gmul(int x, int y) {
    long long a = ea_[x], b = eb_[x], c = ea_[y], d = eb_[y];
    long long na = (a + (long long)pw_buf[b] * c) % m_;
    long long nb = (b + d) % k2_;
    return (int)(na * k2_ + nb);
}

static void setup_group(int m, int k2, int r) {
    m_ = m; k2_ = k2; G_ = m * k2;
    pw_buf[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw_buf[b] = (int)((long long)pw_buf[b - 1] * r % m);
    for (int x = 0; x < G_; x++) { ea_[x] = x / k2; eb_[x] = x % k2; }
}

/* Vertex index = block*G + x. A-blocks 0..k-1, B-blocks k..2k-1.
   Layer l, A-block i goes to B-block lay[l*k+i] with voltage sv[l*k+i]:
   (i,x) ~ (j, x*s). */
static void rebuild(void) {
    int k = k_, G = G_, N = N_, d = d_;
    for (int l = 0; l < d; l++) {
        int *row = nbr_ + (size_t)l * N;
        for (int i = 0; i < k; i++) {
            int p = l * k + i, j = lay_[p], s = sv_[p];
            for (int x = 0; x < G; x++) {
                int v = i * G + x;
                int w = (k + j) * G + gmul(x, s);
                row[v] = w;
                row[w] = v;
            }
        }
    }
}

static long long evalcost(void) {
    int k = k_, G = G_, N = N_, d = d_, K2 = 2 * k_;
    u32 full = (K2 >= 32) ? 0xffffffffu : ((1u << K2) - 1u);
    u32 *cur = ra_, *nxt = rb_;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < K2; b++) cur[b * G] |= 1u << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u32 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr_[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u32 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) cost += __builtin_popcount(full & ~cur[v]);
    int K = k * d, dup = 0;
    for (int p = 0; p < K; p++) {
        for (int q = 0; q < p; q++) {
            if ((q % k) == (p % k) && lay_[q] == lay_[p] && sv_[q] == sv_[p]) { dup++; break; }
        }
    }
    cost += (long long)PEN * dup;
    lastr_ = cur;
    return cost;
}

static long long anneal(long long iters, double T0, double T1, double tend) {
    int k = k_, d = d_, G = G_, N = N_;
    u32 full = (2 * k >= 32) ? 0xffffffffu : ((1u << (2 * k)) - 1u);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) lay_[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = lay_[l * k + i]; lay_[l * k + i] = lay_[l * k + j]; lay_[l * k + j] = t;
        }
    }
    for (int p = 0; p < d * k; p++) sv_[p] = rint_(G);
    rebuild();
    long long cost = evalcost();
    long long bestc = cost, last = 0;
    size_t bytes = sizeof(int) * (size_t)N * (size_t)d;
    for (long long it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && cpu_s() >= tend) break;
        if (it - last > PAT) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        memcpy(bk_, nbr_, bytes);
        int swapped = 0, sp1 = -1, sp2 = -1, p = -1, old_s = 0;
        if (k >= 2 && rint_(100) < 25) {
            int l = rint_(d);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            sp1 = l * k + i1; sp2 = l * k + i2;
            int t = lay_[sp1]; lay_[sp1] = lay_[sp2]; lay_[sp2] = t;
            swapped = 1;
        } else {
            int chosen = 0;
            if (rint_(100) < 40) {
                for (int t = 0; t < 40 && !chosen; t++) {
                    int v = rint_(N);
                    if (lastr_[v] != full) {
                        int b = v / G, l = rint_(d), i = -1;
                        if (b < k) i = b;
                        else {
                            for (int q = 0; q < k; q++) if (lay_[l * k + q] == b - k) { i = q; break; }
                            if (i < 0) continue;
                        }
                        p = l * k + i;
                        chosen = 1;
                    }
                }
            }
            if (!chosen) { int l = rint_(d); int i = rint_(k); p = l * k + i; }
            old_s = sv_[p];
            sv_[p] = rint_(G);
        }
        rebuild();
        long long c2 = evalcost();
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = it; }
        } else {
            if (swapped) { int t = lay_[sp1]; lay_[sp1] = lay_[sp2]; lay_[sp2] = t; }
            else sv_[p] = old_s;
            memcpy(nbr_, bk_, bytes);
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);

    int a0 = 0, b0 = 0;
    if (scanf("%d %d", &a0, &b0) != 2) { a0 = 0; b0 = 0; }

    if (d_ < 2 || D_ < 2) { printf("0 0\n"); return 0; }

    static const int KS[] = {1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9};
    static const int K2L[] = {1, 1, 2, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
    int NKS = (int)(sizeof(KS) / sizeof(KS[0]));
    int NK2 = (int)(sizeof(K2L) / sizeof(K2L[0]));

    while (cpu_s() < limit) {
        int kk = KS[rint_(NKS)];
        int Gmin = best_n / (2 * kk) + 1;
        if (Gmin < 2) Gmin = 2;
        int Gt = Gmin + rint_(1 + Gmin / 50);
        int k2 = K2L[rint_(NK2)];
        if (k2 > Gt) k2 = 1;
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1 && m >= 3 && rint_(100) < 70) {
            for (int t = 0; t < 200; t++) {
                int c = 2 + rint_(m - 2);
                if (gcd_ll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        if (powmod(r, k2, m) != 1 % m) r = 1;
        int G = m * k2;
        int N = 2 * kk * G;
        ensure(N, G, d_ * kk);
        k_ = kk;
        N_ = N;
        setup_group(m, k2, r);
        long long cost = anneal(40000, 15.0, 0.8, limit);
        if (cost == 0 && N > best_n) {
            size_t need = (size_t)N * (size_t)d_;
            if (need > (size_t)capBest_) {
                int *p = realloc(bestnbr_, sizeof(int) * need);
                if (!p) { emit(); return 0; }
                bestnbr_ = p;
                capBest_ = (int)need;
            }
            memcpy(bestnbr_, nbr_, sizeof(int) * need);
            best_n = N;
            best_N = N;
            best_k = kk;
            best_G = G;
        }
    }
    emit();
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
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2, order 2d

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 1 or D == 2:
        return best  # K_{d,d} is optimal for D = 2

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best  # exact projective-plane incidence graph

    # Main search: C voltage-lift annealer over varied groups and base sizes.
    budget = min(0.82 * time_limit, time_limit - 9.0,
                 time_limit - (time.monotonic() - t0) - 6.0)
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed % (1 << 31), f"{budget:.2f}"],
                            stdin_graph=None, timeout=budget + 20.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
