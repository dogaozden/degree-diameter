"""Program: bi-Cayley search over groups, combining both parents.

Construction:
  * Group G of order N (metacyclic Z_m x|_r Z_k, or PSL(2,q)/SL(2,q) for prime q).
    Group ops are computed on the fly, so no N x N table is stored.
  * Bi-Cayley graph: A_x ~ B_{x*s_k} for k < d. This is d-regular, bipartite, with 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D iff BFS from A_e and from B_e
    reach all 2N vertices within D steps.
  * Search: simulated annealing over the connection set, with cost = number of unreached
    (source, vertex) pairs. Time-sliced portfolio in ascending order of group order N.
    Each success raises the bar, so later candidates must be larger.
  * Target window (from ref vertices): matrix groups from ~0.25*ref/2 to ~1.6*ref/2 and
    metacyclic groups just above ref/2 (ref/2 is the record half-order, so N > ref/2 beats the record).

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
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

#define MAXG 12200
#define MAXV (2 * MAXG)
#define MAXDEG 8
#define MAXCAND 1024

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

/* ------------------------------------------------------------------ group */

static int gtype = 0;            /* 0 = metacyclic, 1 = matrix */
static int N = 0, e_id = 0;
static int M_ = 1, K_ = 1;       /* metacyclic: Z_M x|_r Z_K */
static int pw[MAXG];             /* pw[b] = r^b mod M_ */
static int qf = 2, isPSL = 0;    /* matrix group parameters */
static int gm[MAXG][4];          /* canonical matrices [a b; c e] */
static int *idxt = NULL;
static int idx_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qf;
    int k = ((a * q + b) * q + c) * q + e;
    if (!isPSL) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int mat_lookup(int a, int b, int c, int e) {
    return idxt[canon_key(a, b, c, e)];
}

static int build_meta(int m, int k, int r) {
    if (m < 2 || k < 1 || (long)m * k > MAXG) return 0;
    gtype = 0;
    M_ = m;
    K_ = k;
    N = m * k;
    e_id = 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    return N;
}

static int build_matrix(int qq, int psl) {
    qf = qq;
    isPSL = psl;
    gtype = 1;
    int ks = qq * qq * qq * qq;
    if (ks > idx_cap) {
        free(idxt);
        idxt = malloc(sizeof(int) * (size_t)ks);
        if (!idxt) { idx_cap = 0; return 0; }
        idx_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxt[i] = -1;
    int cnt = 0;
    for (int a = 0; a < qq; a++)
        for (int b = 0; b < qq; b++)
            for (int c = 0; c < qq; c++)
                for (int e = 0; e < qq; e++) {
                    if ((((a * e - b * c) % qq) + qq) % qq != 1) continue;
                    int own = ((a * qq + b) * qq + c) * qq + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXG) return 0;
                    gm[cnt][0] = a; gm[cnt][1] = b; gm[cnt][2] = c; gm[cnt][3] = e;
                    idxt[own] = cnt;
                    cnt++;
                }
    N = cnt;
    e_id = mat_lookup(1, 0, 0, 1);
    return N;
}

static int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / K_, b = x % K_, c = y / K_, dd = y % K_;
        int aa = (a + pw[b] * c) % M_;
        int bb = (b + dd) % K_;
        return aa * K_ + bb;
    }
    const int q = qf;
    const int *X = gm[x], *Y = gm[y];
    int a = X[0], b = X[1], c = X[2], e = X[3];
    int a2 = Y[0], b2 = Y[1], c2 = Y[2], e2 = Y[3];
    return mat_lookup((a * a2 + b * c2) % q, (a * b2 + b * e2) % q,
                      (c * a2 + e * c2) % q, (c * b2 + e * e2) % q);
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / K_, b = x % K_;
        int nb = (K_ - b) % K_;
        int ca = (M_ - (int)((long)pw[nb] * a % M_)) % M_;
        return ca * K_ + nb;
    }
    const int q = qf;
    const int *X = gm[x];
    return mat_lookup(X[3] % q, (q - X[1]) % q, (q - X[2]) % q, X[0] % q);
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXG];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXG];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = ginv(s);
    for (int x = 0; x < N; x++) {
        Rr[k][x] = gmul(x, s);
        Ri[k][x] = gmul(x, si);
    }
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src, int dmax) {
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
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + Rr[k][v];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs; 0 means diameter <= D. */
static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

/* Simulated annealing over the connection set. Returns 1 with S valid, 0 on timeout. */
static int anneal(double until, double cycle) {
    randomize_S();
    long cur = cost_now();
    if (cur == 0) return 1;
    const double T0 = 1.5, T1 = 0.05;
    double Tc = T0;
    double cs = now();
    long it = 0;
    for (;;) {
        if ((++it & 15) == 0) {
            double t = now();
            if (t > until) return 0;
            double f = (t - cs) / cycle;
            if (f >= 1.0) {
                randomize_S();
                cur = cost_now();
                if (cur == 0) return 1;
                cs = t;
                f = 0.0;
            }
            Tc = T0 * pow(T1 / T0, f);
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / Tc)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            S[k] = old;
            set_col(k);
        }
    }
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int type, m, k, r, q, psl, N; } Cand;
static Cand cands[MAXCAND];
static int ncand = 0;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    return x->type - y->type;
}

static void gen_matrix(long lo, long hi, long moore) {
    static const int qs[] = {3, 5, 7, 11, 13, 17, 19, 23};
    for (unsigned i = 0; i < sizeof qs / sizeof qs[0]; i++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[i];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lo || o > hi || o > MAXG || 2 * o > moore) continue;
            if (ncand >= MAXCAND) return;
            Cand c;
            c.type = 1; c.m = 0; c.k = 0; c.r = 0;
            c.q = (int)q; c.psl = psl; c.N = (int)o;
            cands[ncand++] = c;
        }
    }
}

static void gen_meta(long lo, long hi, long moore) {
    for (long Nv = lo; Nv <= hi && ncand < MAXCAND; Nv++) {
        if (2 * Nv > moore || Nv > MAXG) break;
        int got = 0;
        for (long k = 2; k <= Nv / 3 && got < 2 && ncand < MAXCAND; k++) {
            if (Nv % k) continue;
            long m = Nv / k;
            if (m < 3) continue;
            for (long r = m - 1; r >= 2; r--) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1) continue;
                Cand c;
                c.type = 0; c.m = (int)m; c.k = (int)k; c.r = (int)r;
                c.q = 0; c.psl = 0; c.N = (int)Nv;
                cands[ncand++] = c;
                got++;
                break;
            }
        }
    }
}

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [ref_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long ref = argc > 5 ? atol(argv[5]) : 4970;
    if (ref <= 0) ref = 4970;

    double t0 = now();
    double usable = limit - 0.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    double recHalf = (double)ref / 2.0;
    long lo = (long)(0.25 * recHalf);
    long hi = (long)(1.6 * recHalf);
    if (2 * hi > moore) hi = moore / 2;
    if (hi > MAXG) hi = MAXG;
    if (lo < d + 2) lo = d + 2;
    if (lo < 3) lo = 3;
    if (hi < lo) { print_complete(); return 0; }

    gen_matrix(lo, hi, moore);

    long mlo = (long)(0.95 * recHalf);
    if (mlo < lo) mlo = lo;
    long mhi = mlo + 400;
    if (mhi > hi) mhi = hi;
    if (mhi >= mlo) gen_meta(mlo, mhi, moore);

    qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);

    long bestN = 0;
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    for (int i = 0; i < ncand; i++) {
        Cand *c = &cands[i];
        if ((long)c->N <= bestN) continue;
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        double frac = (c->type == 1) ? 0.15 : 0.08;
        double slice = remaining * frac;
        if (slice < 0.5 && remaining > 0.5) slice = 0.5;
        if (slice > remaining) slice = remaining;
        if (!apply_cand(c)) continue;
        if (N <= d + 1) continue;
        if (2L * N > moore) continue;
        if (anneal(now() + slice, slice / 3.0)) {
            have = 1;
            bestN = N;
            best = *c;
            memcpy(bS, S, sizeof(int) * (size_t)d);
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(S, bS, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    if (cost_now() != 0) { print_complete(); return 0; }

    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
    return 0;
}
'''

REF_VERTICES = {(4, 9): 4970}


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
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best   # Moore graph already: nothing to search for

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best

    ref = REF_VERTICES.get((d, D), max(8, moore // 4))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                         timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
