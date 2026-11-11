"""Bold variant: voltage lifts of small cubic-type base graphs over metacyclic groups.

Construction: the base graph has K vertices on each side and d darts per A-vertex.
Dart (t, i) joins A_i to B_{pi_t(i)} with voltage g[t][i] in a group G of order N.
The lift has 2*K*N vertices. Left multiplication by G is an automorphism, so every
pair is covered by BFS from the K A-base vertices and the K B-base vertices (2K runs).

Search: simulated annealing over voltages (and base permutations when K > 1), with
cost = total number of (source, vertex) pairs at distance > D. Cost 0 means valid.
The target order 2*K*N ascends from a lower bound. Each order gets a round-robin of
(K, group) combinations with doubling time quanta. The search stops after 3 failed
orders. The largest order found is printed, and Python re-checks it with lib.is_valid.
Python keeps the known start, or K_{d,d}, as a fallback.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXH 512
#define MAXV 1024
#define MAXCOMBO 4096

static int d, D;
static int K, N;              /* base half-size and group order; total vertices 2*K*N */
static int GM, GL, GR;        /* current group Z_m x|_r Z_l, element (a,b) coded a*l+b */
static int MT[MAXH * MAXH];   /* multiplication table */
static int INV[MAXH];

static int pi_[MAXD][MAXK], pinv_[MAXD][MAXK];
static int g_[MAXD][MAXK], gi_[MAXD][MAXK];

static int have = 0;
static int sK, sM, sL, sR;
static int sPi[MAXD][MAXK], sG[MAXD][MAXK];

static int cK[MAXCOMBO], cM[MAXCOMBO], cL[MAXCOMBO], cR[MAXCOMBO];
static int ncombo = 0;

static int stamp_arr[MAXV], qv[MAXV], dv[MAXV];
static int stamp_cur = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
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

/* ------------------------------------------------------------ groups */

static void build_group(int m, int l, int r) {
    int n = m * l;
    N = n; GM = m; GL = l; GR = r;
    int rp[MAXH];
    rp[0] = 1 % m;
    for (int b = 1; b < l; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < n; x++) {
        int a = x / l, b = x % l;
        for (int y = 0; y < n; y++) {
            int c = y / l, e = y % l;
            MT[x * n + y] = ((a + rp[b] * c) % m) * l + (b + e) % l;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

static void add_combo(int k, int m, int l, int r) {
    if (ncombo < MAXCOMBO) {
        cK[ncombo] = k; cM[ncombo] = m; cL[ncombo] = l; cR[ncombo] = r;
        ncombo++;
    }
}

static void add_groups(int k, int n) {
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int l = n / m;
        if (m == 1) { add_combo(k, 1, l, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, l, m) != 1 % m) continue;
            add_combo(k, m, l, r);
        }
    }
}

/* ------------------------------------------------------------ lift */

static void recompute_pinv(int t) {
    for (int i = 0; i < K; i++) pinv_[t][pi_[t][i]] = i;
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) {
            g_[t][i] = rndint(N);
            gi_[t][i] = INV[g_[t][i]];
        }
        for (int i = 0; i < K; i++) pi_[t][i] = i;
        if (t > 0) {
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = pi_[t][i]; pi_[t][i] = pi_[t][j]; pi_[t][j] = tmp;
            }
        }
        recompute_pinv(t);
    }
}

/* Vertices: A_{i,x} = i*N + x, B_{j,y} = K*N + j*N + y.
 * A_{i,x} ~ B_{pi_t(i), x*g[t][i]};  B_{j,y} ~ A_{pinv_t(j), y*g[t][i]^-1}. */
static int nbr(int v, int *out) {
    int kn = K * N;
    if (v < kn) {
        int i = v / N, x = v % N;
        for (int t = 0; t < d; t++) {
            int j = pi_[t][i];
            out[t] = kn + j * N + MT[x * N + g_[t][i]];
        }
    } else {
        int w = v - kn;
        int j = w / N, y = w % N;
        for (int t = 0; t < d; t++) {
            int i = pinv_[t][j];
            out[t] = i * N + MT[y * N + gi_[t][i]];
        }
    }
    return d;
}

static int bfs_reach(int src) {
    int head = 0, tail = 0;
    int out[MAXD];
    stamp_cur++;
    stamp_arr[src] = stamp_cur;
    qv[tail] = src; dv[tail] = 0; tail++;
    while (head < tail) {
        int v = qv[head], dd = dv[head];
        head++;
        if (dd >= D) continue;
        nbr(v, out);
        for (int t = 0; t < d; t++) {
            int u = out[t];
            if (stamp_arr[u] != stamp_cur) {
                stamp_arr[u] = stamp_cur;
                qv[tail] = u; dv[tail] = dd + 1; tail++;
            }
        }
    }
    return tail;
}

/* Number of (source, vertex) pairs at distance > D, summed over the 2K base sources. */
static int evalf(void) {
    int VV = 2 * K * N, tot = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = (s < K) ? s * N : K * N + (s - K) * N;
        tot += VV - bfs_reach(src);
    }
    return tot;
}

/* ------------------------------------------------------------ search */

static void store_state(void) {
    have = 1;
    sK = K; sM = GM; sL = GL; sR = GR;
    memcpy(sPi, pi_, sizeof pi_);
    memcpy(sG, g_, sizeof g_);
}

static int run_sa(int c, double end) {
    build_group(cM[c], cL[c], cR[c]);
    K = cK[c];
    random_state();
    int f = evalf();
    if (f == 0) { store_state(); return 1; }
    double st = now();
    double span = end - st;
    if (span <= 0) return 0;
    double T = 1.0;
    for (long it = 0;; it++) {
        if ((it & 63) == 0) {
            double tn = now();
            if (tn >= end) break;
            double frac = (tn - st) / span;
            T = 2.0 * (1.0 - frac) + 0.1;
        }
        int do_perm = (K > 1) && (rndu() < 0.08);
        if (!do_perm) {
            int t = rndint(d), i = rndint(K);
            int old = g_[t][i], oldi = gi_[t][i];
            int nv = rndint(N);
            g_[t][i] = nv; gi_[t][i] = INV[nv];
            int f2 = evalf();
            if (f2 <= f || rndu() < exp(-(double)(f2 - f) / T)) f = f2;
            else { g_[t][i] = old; gi_[t][i] = oldi; }
        } else {
            int t = rndint(d), a = rndint(K), b = rndint(K);
            if (a == b) continue;
            int pa = pi_[t][a], pb = pi_[t][b];
            pi_[t][a] = pb; pi_[t][b] = pa;
            recompute_pinv(t);
            int f2 = evalf();
            if (f2 <= f || rndu() < exp(-(double)(f2 - f) / T)) f = f2;
            else {
                pi_[t][a] = pa; pi_[t][b] = pb;
                recompute_pinv(t);
            }
        }
        if (f == 0) { store_state(); return 1; }
    }
    return 0;
}

/* Try to find a valid lift with 2*half vertices. */
static int try_half(int half, double dl) {
    ncombo = 0;
    for (int k = 1; k <= MAXK; k++) {
        if (half % k) continue;
        int n = half / k;
        if (n < 3) continue;
        add_groups(k, n);
    }
    if (ncombo == 0) return 0;
    double q = 0.01;
    while (now() < dl) {
        for (int c = 0; c < ncombo && now() < dl; c++) {
            double e = now() + q;
            if (e > dl) e = dl;
            if (run_sa(c, e)) return 1;
        }
        q *= 2.0;
    }
    return 0;
}

/* ------------------------------------------------------------ output */

static void emit(void) {
    if (!have) { printf("0 0\n"); return; }
    build_group(sM, sL, sR);
    K = sK;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) {
            pi_[t][i] = sPi[t][i];
            g_[t][i] = sG[t][i];
            gi_[t][i] = INV[g_[t][i]];
        }
        recompute_pinv(t);
    }
    int kn = K * N;
    static int eu[MAXD * MAXH], ev[MAXD * MAXH];
    int ne = 0, out[MAXD];
    for (int v = 0; v < kn; v++) {
        nbr(v, out);
        for (int t = 0; t < d; t++) {
            int dup = 0;
            for (int s = 0; s < t; s++)
                if (out[s] == out[t]) { dup = 1; break; }
            if (!dup) { eu[ne] = v; ev[ne] = out[t]; ne++; }
        }
    }
    printf("%d %d\n", 2 * kn, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", eu[e], ev[e]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    double tend = now() + budget * 0.9;
    long moore = moore_bound();
    long half_max = moore / 2;
    if (half_max > MAXH - 1) half_max = MAXH - 1;
    long half = (long)(0.45 * (double)moore) / 2;
    if (half < d + 1) half = d + 1;
    if (half > half_max) half = half_max;

    int fails = 0;
    for (; half <= half_max && now() < tend; half++) {
        double rem = tend - now();
        double dl = now() + fmax(0.5, 0.25 * rem);
        if (dl > tend) dl = tend;
        if (try_half((int)half, dl)) {
            fails = 0;
        } else if (++fails >= 3) {
            break;
        }
    }
    emit();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
