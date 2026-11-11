"""Program: bi-Cayley graphs over non-abelian groups, searched by simulated annealing.

Changes from the parent:
  * Group orders are chosen by bisection, not a coarse grid. For each order N in
    (lo, hi] the C engine looks up a metacyclic factorization Z_m x|_r Z_k with
    m*k = N, so every feasible order is reachable. It bisects toward the largest
    order where annealing reaches cost 0. Explicit PSL(2,q) orders in range are
    tried first, since they are few.
  * The multiplication table is also stored transposed, so the column lookups in
    set_col (x -> x*s, x -> x*s^-1) read contiguous memory. This is the main cost
    of each annealing move, and the change speeds up every evaluation.

Safety: the C engine always prints a valid graph (K_{d,d} if nothing is found). Python
checks the output with lib.is_valid and falls back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley annealing search: bisection over group orders, metacyclic and PSL(2,q).
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * Output: "n m" then m lines "u v": bipartite, every degree d, diameter <= D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3500
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define CYC 20000L

typedef struct { int type, m, k, r, q, psl, N; } Cand;

static int d, D;
static double t_end;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int pw_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------------ groups */

static uint16_t mt[(long)MAXN * MAXN];    /* mt[x*N+y]  = x*y */
static uint16_t mtT[(long)MAXN * MAXN];   /* mtT[y*N+x] = x*y (transpose, contiguous columns) */
static int inv_[MAXN];
static int N, e_id;
static int pwv[MAXN];
static int keyidx[130321];                /* 19^4 */
static int elem[MAXN][4];

static void fill_transpose(void) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            mtT[(long)y * N + x] = mt[(long)x * N + y];
}

static int build_meta(int m, int k, int r) {
    long NN = (long)m * k;
    if (NN > MAXN || NN < 2) return 0;
    N = (int)NN;
    pwv[0] = 1 % m;
    for (int b = 1; b < k; b++) pwv[b] = (pwv[b - 1] * r) % m;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pwv[b] * c) % m;
            int bb = (b + dd) % k;
            mt[(long)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    fill_transpose();
    e_id = 0;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int ia = (m - (pwv[nb] * a) % m) % m;
        inv_[x] = ia * k + nb;
    }
    return 1;
}

static int build_matrix(int q, int psl) {
    int q4 = q * q * q * q;
    for (int i = 0; i < q4; i++) keyidx[i] = -1;
    N = 0;
    for (int p0 = 0; p0 < q; p0++)
    for (int p1 = 0; p1 < q; p1++)
    for (int p2 = 0; p2 < q; p2++)
    for (int p3 = 0; p3 < q; p3++) {
        if ((((p0 * p3 - p1 * p2) % q) + q) % q != 1) continue;
        int key = ((p0 * q + p1) * q + p2) * q + p3;
        if (keyidx[key] != -1) continue;
        if (N >= MAXN) return 0;
        elem[N][0] = p0; elem[N][1] = p1; elem[N][2] = p2; elem[N][3] = p3;
        keyidx[key] = N;
        if (psl) {
            int n0 = (q - p0) % q, n1 = (q - p1) % q;
            int n2 = (q - p2) % q, n3 = (q - p3) % q;
            keyidx[((n0 * q + n1) * q + n2) * q + n3] = N;
        }
        N++;
    }
    e_id = keyidx[((1 * q + 0) * q + 0) * q + 1];
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int a = elem[x][0], b = elem[x][1], c = elem[x][2], e = elem[x][3];
            int a2 = elem[y][0], b2 = elem[y][1], c2 = elem[y][2], e2 = elem[y][3];
            int c00 = (a * a2 + b * c2) % q;
            int c01 = (a * b2 + b * e2) % q;
            int c10 = (c * a2 + e * c2) % q;
            int c11 = (c * b2 + e * e2) % q;
            mt[(long)x * N + y] = (uint16_t)keyidx[((c00 * q + c01) * q + c10) * q + c11];
        }
    fill_transpose();
    for (int x = 0; x < N; x++) {
        inv_[x] = -1;
        for (int y = 0; y < N; y++)
            if (mt[(long)x * N + y] == e_id) { inv_[x] = y; break; }
    }
    return 1;
}

static int build_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

/* Pick a random metacyclic factorization of order Nv (m*k = Nv, k >= 3, r^k = 1 mod m).
 * Returns 1 and fills *c if one exists. */
static int find_meta(long Nv, Cand *c) {
    int cnt = 0;
    Cand pick = {0, 0, 0, 0, 0, 0, 0};
    for (long m = 3; m <= Nv / 3; m++) {
        if (Nv % m) continue;
        long k = Nv / m;
        if (k < 3) continue;
        for (int r = 2; r < (int)m; r++) {
            if (gcd_i(r, (int)m) != 1) continue;
            if (pw_mod(r, k, m) != 1) continue;
            cnt++;
            if (rndint(cnt) == 0) {
                pick.type = 0;
                pick.m = (int)m;
                pick.k = (int)k;
                pick.r = r;
                pick.N = (int)Nv;
            }
        }
    }
    if (cnt == 0) return 0;
    *c = pick;
    return 1;
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = inv_[s];
    const uint16_t *cs = mtT + (long)s * N;    /* cs[x] = x*s */
    const uint16_t *ci = mtT + (long)si * N;   /* ci[x] = x*s^{-1} */
    for (int x = 0; x < N; x++) {
        Rr[k][x] = cs[x];
        Ri[k][x] = ci[x];
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

static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

/* ------------------------------------------------------------------ annealing */

static double T0 = 4.0, T1 = 0.3;
static int bestS[MAXDEG];

/* Returns 1 with a valid S in S[] (cost 0), or 0 on timeout. */
static int anneal(double until) {
    randomize_S();
    long cur = cost_now(), best = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)d);
    while (best > 0) {
        for (long it = 0; it < CYC; it++) {
            if ((it & 127) == 0 && now() > until) return 0;
            double T = T0 * pow(T1 / T0, (double)it / (double)CYC);
            int k = rndint(d);
            int x = rndint(N);
            if (in_S(x, d)) continue;
            int old = S[k];
            S[k] = x;
            set_col(k);
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nc;
                if (cur < best) {
                    best = cur;
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                }
                if (best == 0) return 1;
            } else {
                S[k] = old;
                set_col(k);
            }
        }
        /* restart the cycle from the best state found so far */
        memcpy(S, bestS, sizeof(int) * (size_t)d);
        for (int k = 0; k < d; k++) set_col(k);
        cur = best;
    }
    return 1;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static int cmp_cand_desc(const void *a, const void *b) {
    int x = ((const Cand *)a)->N, y = ((const Cand *)b)->N;
    return (x < y) - (x > y);
}

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long hi = moore / 2;             /* 2N <= Moore bound */
    if (hi > MAXN) hi = MAXN;
    long lo = hi * 6 / 10;
    if (lo < 2) lo = 2;
    if (hi < lo) { print_complete(); return 0; }

    int have_best = 0;
    long bestN = 0;
    Cand bestC = {0, 0, 0, 0, 0, 0, 0};
    static int bestFound[MAXDEG];

    /* Phase 1: explicit PSL(2,q) groups in range, largest first; the first success is the
     * largest explicit one, so stop there. */
    static Cand ex[16];
    int nex = 0;
    static const int qs[6] = {5, 7, 11, 13, 17, 19};
    for (int qi = 0; qi < 6; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long ord = q * (q * q - 1);
            if (psl) ord /= 2;
            if (ord >= lo && ord <= hi && nex < 16) {
                ex[nex] = (Cand){1, 0, 0, 0, (int)q, psl, (int)ord};
                nex++;
            }
        }
    qsort(ex, (size_t)nex, sizeof(Cand), cmp_cand_desc);
    for (int i = 0; i < nex; i++) {
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        double slice = remaining * 0.25;
        if (slice > 3.0) slice = 3.0;
        if (slice < 0.5) slice = 0.5;
        if (slice > remaining) slice = remaining;
        if (!build_cand(&ex[i])) continue;
        if (anneal(now() + slice)) {
            have_best = 1;
            bestN = N;
            bestC = ex[i];
            memcpy(bestFound, S, sizeof(int) * (size_t)d);
            break;
        }
    }

    /* Phase 2: bisection over metacyclic orders. Invariant: a is a known-feasible order
     * (or lo-1), and the answer is < b. */
    long a = have_best ? bestN : lo - 1;
    long b = hi + 1;
    while (b - a > 1) {
        double remaining = t_end - now();
        if (remaining < 0.4) break;
        long mid = (a + b) / 2;
        Cand c = {0, 0, 0, 0, 0, 0, 0};
        long Nf = -1;
        for (long x = mid; x > a; x--) {
            if (find_meta(x, &c)) { Nf = x; break; }
        }
        if (Nf < 0) { b = mid; continue; }   /* no factorization in (a, mid] */
        double slice = remaining * 0.3;
        if (slice > 4.0) slice = 4.0;
        if (slice < 0.5) slice = 0.5;
        if (slice > remaining) slice = remaining;
        if (!build_cand(&c)) { b = Nf; continue; }
        if (anneal(now() + slice)) {
            have_best = 1;
            bestN = N;
            bestC = c;
            memcpy(bestFound, S, sizeof(int) * (size_t)d);
            a = Nf;
        } else {
            b = Nf;
        }
    }

    if (!have_best) {
        print_complete();
        return 0;
    }
    build_cand(&bestC);
    memcpy(S, bestFound, sizeof(int) * (size_t)d);
    for (int k = 0; k < d; k++) set_col(k);
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", x, N + Rr[k][x]);
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
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
