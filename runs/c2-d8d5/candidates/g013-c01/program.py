"""Bi-Cayley voltage-lift annealing in C, with exact small constructions as seeds and fallbacks."""
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley (voltage lift) annealing for bipartite degree-diameter graphs.
 * Vertices: A(i,x) = i*N + x (i < k), B(j,y) = (k+j)*N + y, group G of order N.
 * Layer t (t < d) joins A(i,x) to B(sig[t][i], x * w[t][i]) for all x.
 * Left multiplication by G is an automorphism, so the diameter test only needs
 * BFS from one representative per block (2k BFS runs).
 * Usage: prog d D seed time_limit [base_n]   (stdin ignored)
 * stdout: "n m" then edge lines, or "0 0" if nothing beats base_n.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXG 4096
#define MAXV 40000

static int d, D;
static int k, N;
static int gm, gK, gr;
static int rp[MAXG];
static int sig[MAXD][MAXK];
static int w[MAXD][MAXK];
static int winv[MAXD][MAXK];
static int NB[MAXV * MAXD];
static int mark[MAXV];
static int qbuf[MAXV];
static int stamp = 0;

static int best_ok = 0;
static int bk, bN, bm, bK, br;
static int bsig[MAXD][MAXK];
static int bw[MAXD][MAXK];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Group Z_m x|_r Z_K, element (a,b) = a*K + b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(int m, int K, int r) {
    gm = m; gK = K; gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < K; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gK, b = x % gK, c = y / gK, e = y % gK;
    long aa = ((long)a + (long)rp[b] * c) % gm;
    return (int)aa * gK + (b + e) % gK;
}

static int ginv(int g) {
    int a = g / gK, b = g % gK, nb = (gK - b) % gK;
    long ap = (gm - ((long)rp[nb] * a) % gm) % gm;
    return (int)ap * gK + nb;
}

/* Random semidirect group of order Nn (uniform over candidate (m, r) pairs). */
static void pick_group(int Nn, int *om, int *oK, int *orr) {
    long cnt = 0;
    int bmm = 1, bKK = Nn, brr = 0;
    for (int m = 1; m <= Nn; m++) {
        if (Nn % m) continue;
        int K = Nn / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bmm = 1; bKK = K; brr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, K, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bmm = m; bKK = K; brr = r; }
        }
    }
    *om = bmm; *oK = bKK; *orr = brr;
}

static void set_dart(int t, int i) {
    int j = sig[t][i];
    int wv = w[t][i], wi = winv[t][i];
    for (int x = 0; x < N; x++) {
        int v = i * N + x;
        NB[v * d + t] = (k + j) * N + gmul(x, wv);
    }
    for (int y = 0; y < N; y++) {
        int v = (k + j) * N + y;
        NB[v * d + t] = i * N + gmul(y, wi);
    }
}

/* Block i must have d distinct (sigma, voltage) pairs so the lift is simple. */
static int ok_block(int i) {
    for (int t = 0; t < d; t++)
        for (int s = t + 1; s < d; s++)
            if (sig[t][i] == sig[s][i] && w[t][i] == w[s][i]) return 0;
    return 1;
}

static void swap_sig(int t, int a, int b) {
    int tmp = sig[t][a];
    sig[t][a] = sig[t][b];
    sig[t][b] = tmp;
}

static int init_state(void) {
    for (int tries = 0; tries < 200; tries++) {
        for (int t = 0; t < d; t++) {
            int p[MAXK];
            for (int i = 0; i < k; i++) p[i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = p[i]; p[i] = p[j]; p[j] = s;
            }
            for (int i = 0; i < k; i++) sig[t][i] = p[i];
        }
        for (int t = 0; t < d; t++)
            for (int i = 0; i < k; i++) {
                int g = rndint(N);
                w[t][i] = g;
                winv[t][i] = ginv(g);
            }
        int good = 1;
        for (int i = 0; i < k && good; i++)
            if (!ok_block(i)) good = 0;
        if (good) {
            for (int t = 0; t < d; t++)
                for (int i = 0; i < k; i++) set_dart(t, i);
            return 1;
        }
    }
    return 0;
}

/* Sum over the 2k block representatives of vertices not within distance D. */
static long eval_cost(void) {
    long total = 0;
    long n = 2L * k * N;
    for (int rep = 0; rep < 2 * k; rep++) {
        stamp++;
        int src = rep * N;
        int lo = 0, hi = 1;
        qbuf[0] = src;
        mark[src] = stamp;
        for (int lev = 0; lev < D && lo < hi; lev++) {
            int nhi = hi;
            for (int q = lo; q < hi; q++) {
                const int *nb = NB + (size_t)qbuf[q] * d;
                for (int t = 0; t < d; t++) {
                    int u = nb[t];
                    if (mark[u] != stamp) {
                        mark[u] = stamp;
                        qbuf[nhi++] = u;
                    }
                }
            }
            lo = hi;
            hi = nhi;
        }
        total += n - hi;
    }
    return total;
}

/* Simulated annealing over permutations and voltages. Returns 1 if cost reaches 0. */
static int anneal(double until) {
    if (!init_state()) return 0;
    long cost = eval_cost();
    double t_start = now();
    double span = until - t_start;
    if (span <= 0) return 0;
    const double T0 = 6.0, T1 = 0.2;
    double T = T0;
    long it = 0;
    while (cost > 0) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn >= until) break;
            double f = (tn - t_start) / span;
            if (f > 1.0) f = 1.0;
            T = T0 * pow(T1 / T0, f);
        }
        it++;
        int t = rndint(d), i = rndint(k);
        if (rnd01() < 0.6) {
            int g = rndint(N);
            if (g == w[t][i]) continue;
            int old = w[t][i], oldi = winv[t][i];
            w[t][i] = g;
            winv[t][i] = ginv(g);
            if (!ok_block(i)) {
                w[t][i] = old;
                winv[t][i] = oldi;
                continue;
            }
            set_dart(t, i);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                w[t][i] = old;
                winv[t][i] = oldi;
                set_dart(t, i);
            }
        } else {
            int i2 = rndint(k);
            if (i2 == i) continue;
            swap_sig(t, i, i2);
            if (!ok_block(i) || !ok_block(i2)) {
                swap_sig(t, i, i2);
                continue;
            }
            set_dart(t, i);
            set_dart(t, i2);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                swap_sig(t, i, i2);
                set_dart(t, i);
                set_dart(t, i2);
            }
        }
    }
    return cost == 0;
}

static void save_best(void) {
    bk = k; bN = N; bm = gm; bK = gK; br = gr;
    memcpy(bsig, sig, sizeof sig);
    memcpy(bw, w, sizeof w);
    best_ok = 1;
}

static void print_best(void) {
    if (!best_ok) {
        printf("0 0\n");
        return;
    }
    set_group(bm, bK, br);
    k = bk; N = bN;
    memcpy(sig, bsig, sizeof sig);
    memcpy(w, bw, sizeof w);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < k; i++) winv[t][i] = ginv(w[t][i]);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < k; i++) set_dart(t, i);
    if (eval_cost() != 0) {
        printf("0 0\n");
        return;
    }
    long n = 2L * k * N;
    long m = (long)k * N * d;
    printf("%ld %ld\n", n, m);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < k; i++) {
            int j = sig[t][i];
            for (int x = 0; x < N; x++)
                printf("%d %d\n", i * N + x, (k + j) * N + gmul(x, w[t][i]));
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [base_n]\n");
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long base_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    double t_end = t0 + limit * 0.93 - 0.2;
    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    long best_n = base_n;
    while (now() < t_end) {
        int kk = 2 + rndint(7);
        long Nlo = best_n / (2L * kk) + 1 + rndint(3);
        if (Nlo < 2) Nlo = 2;
        if (Nlo > MAXG) continue;
        if (2L * kk * Nlo > moore || 2L * kk * Nlo > MAXV) continue;
        int m, K, r;
        pick_group((int)Nlo, &m, &K, &r);
        set_group(m, K, r);
        k = kk;
        N = (int)Nlo;
        double rem = t_end - now();
        if (rem <= 0) break;
        double tb = rem < 6.0 ? rem : 6.0;
        if (anneal(now() + tb)) {
            long n = 2L * k * N;
            if (n > best_n) {
                best_n = n;
                save_best();
            }
        }
    }
    print_best();
    return 0;
}
'''


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
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3:
        if lib.is_prime_power(d - 1):
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except (ValueError, RuntimeError):
                pass

    # Main search: bi-Cayley lifts over semidirect groups, annealed in C.
    elapsed = time.monotonic() - t0
    budget = 0.85 * time_limit - elapsed - 1.0
    if budget >= 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, int(seed) % 2147483647, round(budget, 2), best[0]],
                             stdin_graph=None, timeout=budget + 6)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
