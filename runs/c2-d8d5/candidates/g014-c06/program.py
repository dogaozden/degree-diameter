import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealer over metacyclic-times-cyclic groups.
#
# A lift has kb blocks on each side. Each side-A block i is joined to side-B
# block pi_l(i) in every layer l, with voltage s_{l,i}: (i,x) ~ (pi_l(i), x*s).
# Left multiplication by any group element is an automorphism, so every block
# is vertex-transitive. The diameter test therefore needs only one BFS per
# block (2*kb BFS runs), and the cost is the number of unreached pairs.
# Groups: Z_m x|_r Z_k times Z_j, coded as ((a*k+b)*j + c), with a multiplication table.
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

static long lpow(long b, long e, long m) {
    long r = 1 % m;
    b %= m; if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long lgcd(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static int d_, D_, kb, G, N;
static int *MUL, *INV;
static int *pi_, *S_, *nbr, *qbuf;
static unsigned int *seen;
static unsigned int sgen;
static clock_t c0;
static double time_lim;

static double elapsed(void) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static void build_group(int m, int k, int r, int j) {
    G = m * k * j;
    MUL = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    int *rp = malloc(sizeof(int) * (size_t)k);
    for (int b = 0; b < k; b++) rp[b] = (int)lpow(r, b, m);
    for (int x = 0; x < G; x++) {
        int c1 = x % j; int t1 = x / j; int b1 = t1 % k; int a1 = t1 / k;
        for (int y = 0; y < G; y++) {
            int c2 = y % j; int t2 = y / j; int b2 = t2 % k; int a2 = t2 / k;
            int a = (int)(((long)a1 + (long)rp[b1] * a2) % m);
            int b = (b1 + b2) % k;
            int c = (c1 + c2) % j;
            MUL[(size_t)x * G + y] = (a * k + b) * j + c;
        }
    }
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            if (MUL[(size_t)x * G + y] == 0) { INV[x] = y; break; }
        }
    }
    free(rp);
}

static void free_group(void) {
    free(MUL); free(INV);
    MUL = NULL; INV = NULL;
}

static void set_dart(int l, int i) {
    int idx = l * kb + i;
    int j = pi_[idx], s = S_[idx], si = INV[s];
    int aBase = i * G, bBase = (kb + j) * G;
    for (int x = 0; x < G; x++)
        nbr[(size_t)(aBase + x) * d_ + l] = bBase + MUL[(size_t)x * G + s];
    for (int y = 0; y < G; y++)
        nbr[(size_t)(bBase + y) * d_ + l] = aBase + MUL[(size_t)y * G + si];
}

/* Sum over block representatives of unreached vertices within distance D_. Zero iff valid. */
static long long cost_eval(void) {
    long long tot = 0;
    int nb = 2 * kb;
    for (int b = 0; b < nb; b++) {
        int src = b * G;
        sgen++;
        if (sgen == 0) { memset(seen, 0, sizeof(unsigned int) * (size_t)N); sgen = 1; }
        int head = 0, tail = 0;
        qbuf[tail++] = src;
        seen[src] = sgen;
        for (int dep = 0; dep < D_ && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                const int *row = nbr + (size_t)v * d_;
                for (int l = 0; l < d_; l++) {
                    int u = row[l];
                    if (seen[u] != sgen) { seen[u] = sgen; qbuf[tail++] = u; }
                }
            }
            if (tail == N) break;
        }
        tot += N - tail;
    }
    return tot;
}

static void random_lift(void) {
    for (int l = 0; l < d_; l++) {
        int *p = pi_ + (size_t)l * kb;
        for (int i = 0; i < kb; i++) p[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < kb; i++) S_[(size_t)l * kb + i] = rint_(G);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < kb; i++) set_dart(l, i);
}

/* Returns 1 if a zero-cost (valid) lift was reached, else 0. */
static int anneal(int iters) {
    random_lift();
    long long cost = cost_eval();
    if (cost == 0) return 1;
    double T0 = 2.0 + 0.02 * (double)cost, T1 = 0.5;
    for (int t = 0; t < iters; t++) {
        if ((t & 127) == 0 && elapsed() > time_lim) return 0;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        if (kb >= 2 && rint_(10) < 3) {
            int l = rint_(d_);
            int i1 = rint_(kb);
            int i2 = rint_(kb - 1);
            if (i2 >= i1) i2++;
            int *p = pi_ + (size_t)l * kb;
            int tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
        } else {
            int l = rint_(d_), i = rint_(kb);
            int idx = l * kb + i;
            int old = S_[idx], nw = rint_(G);
            if (nw == old) continue;
            S_[idx] = nw;
            set_dart(l, i);
            long long nc = cost_eval();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                S_[idx] = old;
                set_dart(l, i);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* Extract the simple graph from the A side (each edge once). Returns edge count. */
static int extract(int *eu, int *ev) {
    int cnt = 0;
    int A = kb * G;
    int *tmp = malloc(sizeof(int) * (size_t)d_);
    for (int u = 0; u < A; u++) {
        for (int l = 0; l < d_; l++) tmp[l] = nbr[(size_t)u * d_ + l];
        for (int a = 1; a < d_; a++) {
            int x = tmp[a], b = a - 1;
            while (b >= 0 && tmp[b] > x) { tmp[b + 1] = tmp[b]; b--; }
            tmp[b + 1] = x;
        }
        for (int l = 0; l < d_; l++) {
            if (l > 0 && tmp[l] == tmp[l - 1]) continue;
            eu[cnt] = u; ev[cnt] = tmp[l]; cnt++;
        }
    }
    free(tmp);
    return cnt;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 8; w++) rnd();
    time_lim = atof(argv[4]);
    int maxkb = argc > 5 ? atoi(argv[5]) : 4;
    if (maxkb < 1) maxkb = 1;
    if (maxkb > 8) maxkb = 8;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    (void)n0; (void)m0;

    if (d_ < 1 || D_ < 1) { printf("0 0\n"); return 0; }

    c0 = clock();
    int best_n = 0, best_m = 0;
    int *bestU = NULL, *bestV = NULL;
    int fails = 0;
    static const int jch[5] = {1, 1, 1, 2, 3};

    while (elapsed() < time_lim) {
        kb = 1 + rint_(maxkb);
        long glo = best_n / (2L * kb) + 1;
        if (glo < 2) glo = 2;
        long span = 2 + fails / 6;
        if (span > 200) span = 200;
        long ghi = glo + span;
        if (ghi > 2000) ghi = 2000;
        if (glo > ghi) break;

        int m = 0, k = 1, r = 1, j = 1, ok = 0;
        for (int tries = 0; tries < 300 && !ok; tries++) {
            j = jch[rint_(5)];
            k = 1 + rint_(12);
            long gk = (long)k * j;
            long mlo = (glo + gk - 1) / gk, mhi = ghi / gk;
            if (mlo < 2) mlo = 2;
            if (mlo > mhi) continue;
            m = (int)(mlo + rint_((int)(mhi - mlo + 1)));
            r = 1;
            if (k > 1) {
                for (int rt = 0; rt < 80; rt++) {
                    long c = 2 + rint_(m > 2 ? m - 2 : 1);
                    if (lgcd(c, m) == 1 && lpow(c, k, m) == 1) { r = (int)c; break; }
                }
            }
            ok = 1;
        }
        if (!ok) { fails++; continue; }

        build_group(m, k, r, j);
        N = 2 * kb * G;
        pi_ = malloc(sizeof(int) * (size_t)kb * (size_t)d_);
        S_ = malloc(sizeof(int) * (size_t)kb * (size_t)d_);
        nbr = malloc(sizeof(int) * (size_t)N * (size_t)d_);
        qbuf = malloc(sizeof(int) * (size_t)N);
        seen = calloc((size_t)N, sizeof(unsigned int));
        sgen = 0;

        int found = anneal(15000);
        if (found) {
            int cap = (N / 2) * d_ + 1;
            int *eu = malloc(sizeof(int) * (size_t)cap);
            int *ev = malloc(sizeof(int) * (size_t)cap);
            int cnt = extract(eu, ev);
            if (N > best_n) {
                free(bestU); free(bestV);
                bestU = eu; bestV = ev;
                best_n = N; best_m = cnt;
            } else {
                free(eu); free(ev);
            }
            fails = 0;
        } else {
            fails++;
        }

        free_group();
        free(pi_); free(S_); free(nbr); free(qbuf); free(seen);
        pi_ = S_ = nbr = qbuf = NULL;
        seen = NULL;
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: exact projective-plane construction for D = 3, C search otherwise.
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
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Voltage-lift search in C, with a safety margin for compile time and output.
    budget = time_limit - (time.monotonic() - t0) - 8.0
    if budget >= 3.0:
        try:
            seed_arg = int(seed) & 0x7FFFFFFF
            out = lib.run_c(C_SOURCE, [d, D, seed_arg, f"{budget:.2f}", 4],
                            stdin_graph=None, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
