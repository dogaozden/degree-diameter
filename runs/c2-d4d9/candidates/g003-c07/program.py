"""Program: base-graph voltage lifts over semidirect products, found by annealing.

This replaces the bi-Cayley hill-climb over PSL(2,q)/SL(2,q). The new construction:
  * Base graph: t A-vertices and t B-vertices (t in 1..3), joined by d permutations
    sigma_0..sigma_{d-1} of {0..t-1}. Dart (i,k) goes from A_i to B_{sigma_k(i)} and
    carries a voltage g_{ik} in a group G.
  * Group G = Z_m x|_r Z_k, of order M = m*k, with (a,b)(c,e) = (a + r^b c, b + e).
    Non-abelian groups are sampled at random and the trivial action (r = 1) is the fallback.
  * Lift: A_{i,x} -- B_{sigma_k(i), x*g_{ik}}. This is d-regular and bipartite, with 2tM
    vertices. Left multiplication by G is an automorphism, so diameter <= D iff BFS from
    the 2t base vertices (identity lifts) reaches every vertex within D steps.
  * C search: simulated annealing over voltages and permutations, with cost equal to the
    number of (source, vertex) pairs not reached within D steps.
  * Ladder: target sizes grow by about 1% each time a configuration succeeds. The engine
    keeps the largest valid lift found, and prints K_{d,d} if none is found.

Python checks the output with lib.is_valid and falls back to the known start or K_{d,d}.
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

#define MAXT 3
#define MAXDEG 8
#define MAXM 10000
#define MAXV (2 * MAXT * MAXM)

static int d, D, t;
static long moore;
static double t_stop;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int GMm, GK, GR, M;
static int pw[MAXM];
static int ginvt[MAXM];

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

static long gcdl(long a, long b) {
    while (b) {
        long c = a % b;
        a = b;
        b = c;
    }
    return a;
}

/* element (a,b) coded as a*K+b; (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, e = y % GK;
    int aa = (int)(((long)a + (long)pw[b] * c) % GMm);
    int bb = (b + e) % GK;
    return aa * GK + bb;
}

static void set_group(int m, int k, int r) {
    GMm = m;
    GK = k;
    GR = r;
    M = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < M; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int ia = (int)((m - ((long)pw[nb] * a) % m) % m);
        ginvt[x] = ia * k + nb;
    }
}

static void choose_group(int Mv) {
    int m = Mv;
    for (int att = 0; att < 200; att++) {
        int mm = 2 + rndint(Mv - 1);
        if (Mv % mm == 0) {
            m = mm;
            break;
        }
    }
    int k = Mv / m;
    int r = 1;
    if (k > 1) {
        for (int att = 0; att < 300; att++) {
            int rr = 1 + rndint(m - 1);
            if (gcdl(rr, m) == 1 && powmod(rr, k, m) == 1 % m) {
                r = rr;
                break;
            }
        }
    }
    set_group(m, k, r);
}

/* ------------------------------------------------------------ configuration */

static int sg[MAXDEG][MAXT];          /* sg[k][i] = sigma_k(i) */
static int ig[MAXDEG][MAXT];          /* ig[k][j] = sigma_k^{-1}(j) */
static int gv[MAXT][MAXDEG];          /* voltage of dart (i,k) */
static int Rm[MAXT][MAXDEG][MAXM];    /* Rm[i][k][x] = x * g_{ik} */
static int Qm[MAXT][MAXDEG][MAXM];    /* Qm[i][k][x] = x * g_{ik}^{-1} */

static void set_RQ(int i, int k) {
    int g = gv[i][k], gi = ginvt[g];
    for (int x = 0; x < M; x++) {
        Rm[i][k][x] = gmul(x, g);
        Qm[i][k][x] = gmul(x, gi);
    }
}

static void set_all_RQ(void) {
    for (int i = 0; i < t; i++)
        for (int k = 0; k < d; k++) set_RQ(i, k);
}

static void set_inv(int k) {
    for (int i = 0; i < t; i++) ig[k][sg[k][i]] = i;
}

static int row_ok(int i) {
    for (int k = 0; k < d; k++)
        for (int l = 0; l < k; l++)
            if (sg[k][i] == sg[l][i] && gv[i][k] == gv[i][l]) return 0;
    return 1;
}

static int init_config(void) {
    if (t * M < d) return 0;
    for (int k = 0; k < d; k++) {
        int perm[MAXT];
        for (int i = 0; i < t; i++) perm[i] = i;
        for (int i = t - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[r];
            perm[r] = tmp;
        }
        for (int i = 0; i < t; i++) sg[k][i] = perm[i];
        set_inv(k);
    }
    for (int i = 0; i < t; i++) {
        int tries = 0;
        do {
            for (int k = 0; k < d; k++) gv[i][k] = rndint(M);
            if (++tries > 100000) return 0;
        } while (!row_ok(i));
    }
    set_all_RQ();
    return 1;
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
    int tm = t * M;
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < tm) {
                int i = v / M, x = v - i * M;
                for (int k = 0; k < d; k++) {
                    int j = sg[k][i];
                    int u = tm + j * M + Rm[i][k][x];
                    if (stamp[u] != tick) {
                        stamp[u] = tick;
                        qv[tail++] = u;
                    }
                }
            } else {
                int w = v - tm;
                int j = w / M, y = w - j * M;
                for (int k = 0; k < d; k++) {
                    int i = ig[k][j];
                    int u = i * M + Qm[i][k][y];
                    if (stamp[u] != tick) {
                        stamp[u] = tick;
                        qv[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Pairs (source, vertex) not within D steps; 0 means diameter <= D. */
static long cost_all(void) {
    int tm = t * M, V = 2 * tm;
    long c = 0;
    for (int s = 0; s < 2 * t; s++) {
        int src = (s < t) ? s * M : tm + (s - t) * M;   /* identity lift */
        c += (long)(V - ball(src, D));
    }
    return c;
}

/* ------------------------------------------------------------ annealing */

static int anneal(double until) {
    if (!init_config()) return 0;
    long cur = cost_all();
    double start = now();
    double span = until - start;
    if (span <= 0) return 0;
    double temp = 3.0;
    long it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0) {
            double tn = now();
            if (tn > until) return 0;
            double frac = (tn - start) / span;
            temp = 3.0 * pow(0.03, frac);
        }
        if (t == 1 || rndint(2) == 0) {
            int i = rndint(t), k = rndint(d);
            int old = gv[i][k];
            int nw = rndint(M);
            if (nw == old) continue;
            gv[i][k] = nw;
            if (!row_ok(i)) {
                gv[i][k] = old;
                continue;
            }
            set_RQ(i, k);
            long nc = cost_all();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) {
                cur = nc;
            } else {
                gv[i][k] = old;
                set_RQ(i, k);
            }
        } else {
            int k = rndint(d);
            int i1 = rndint(t), i2 = rndint(t - 1);
            if (i2 >= i1) i2++;
            int tmp = sg[k][i1];
            sg[k][i1] = sg[k][i2];
            sg[k][i2] = tmp;
            if (!row_ok(i1) || !row_ok(i2)) {
                tmp = sg[k][i1];
                sg[k][i1] = sg[k][i2];
                sg[k][i2] = tmp;
                continue;
            }
            set_inv(k);
            long nc = cost_all();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) {
                cur = nc;
            } else {
                tmp = sg[k][i1];
                sg[k][i1] = sg[k][i2];
                sg[k][i2] = tmp;
                set_inv(k);
            }
        }
    }
    return 1;
}

/* ------------------------------------------------------------ best snapshot */

static int bt = 0, bM = 0, bm = 0, bk = 0, br = 0, bV = 0;
static int bsg[MAXDEG][MAXT];
static int bgv[MAXT][MAXDEG];

static void snapshot(void) {
    bt = t;
    bM = M;
    bm = GMm;
    bk = GK;
    br = GR;
    bV = 2 * t * M;
    memcpy(bsg, sg, sizeof sg);
    memcpy(bgv, gv, sizeof gv);
}

static void print_best(void) {
    set_group(bm, bk, br);
    t = bt;
    int tm = bt * M;
    printf("%d %d\n", 2 * tm, tm * d);
    for (int i = 0; i < bt; i++)
        for (int x = 0; x < M; x++)
            for (int k = 0; k < d; k++) {
                int j = bsg[k][i];
                int y = gmul(x, bgv[i][k]);
                printf("%d %d\n", i * M + x, tm + j * M + y);
            }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_stop = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) {
        print_complete();
        return 0;
    }
    moore = moore_bound();

    long T = 16;
    while (now() < t_stop && T <= moore) {
        int ok = 0;
        for (int att = 0; att < 4 && !ok; att++) {
            double rem = t_stop - now();
            if (rem < 0.05) break;
            double cap = (att < 3) ? 0.12 * rem : 0.6 * rem;
            int tt = 1 + rndint(MAXT);
            long lo = (T + 2L * tt - 1) / (2L * tt);
            long hi = (long)((double)T * 1.06) / (2L * tt) + 1;
            if (hi < lo) hi = lo;
            long Mc = lo + (long)(rnd() % (uint64_t)(hi - lo + 1));
            if (Mc < 2 || Mc > MAXM) continue;
            if (2L * tt * Mc > moore) continue;
            if ((long)tt * Mc < d) continue;
            t = tt;
            choose_group((int)Mc);
            if (anneal(now() + cap)) {
                ok = 1;
                snapshot();
            }
        }
        if (!ok) break;
        T = bV + (bV / 100 > 2 ? bV / 100 : 2);
    }

    if (bV == 0) {
        print_complete();
        return 0;
    }
    print_best();
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
