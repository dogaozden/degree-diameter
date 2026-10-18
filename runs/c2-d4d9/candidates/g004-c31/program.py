"""Program: bi-Cayley graphs over non-abelian groups, searched by simulated annealing.

Changes from the parent:
  * The candidate sweep is now a bracketing search over the sorted candidate orders instead
    of an ascending sweep with equal slices. Success is roughly monotone in group order, so
    the search first finds a feasible order (probing upward from the smallest), then
    bisects between the largest feasible order and the smallest failing one. Time is
    concentrated on the boundary sizes that decide the score, instead of being spent on
    many easy small groups and short failing slices on large ones.
  * Candidate groups are metacyclic Z_m x|_r Z_k (r^k = 1 mod m, gcd(r,m) = 1, k >= 3),
    sampled on a grid of orders in [0.6*M/2, M/2] (M = Moore bound), plus SL(2,q)/PSL(2,q)
    with orders in the same range. The full multiplication table is precomputed, so each
    evaluation is pure table lookups.
  * Each group is searched by simulated annealing (cost = unreached (source, vertex) pairs
    from A_e and B_e), with restarts from the best state in each cycle.
  * Bi-Cayley graph: A_x ~ B_{x s_k}. It is d-regular and bipartite, and the two-BFS check is
    exact by left-multiplication symmetry.

Safety: the C engine always prints a valid graph (K_{d,d} if nothing is found). Python
checks the output with lib.is_valid and falls back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley annealing search over metacyclic groups and PSL/SL(2,q).
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

static uint16_t mt[(long)MAXN * MAXN];   /* mt[x*N+y] = x*y */
static int inv_[MAXN];
static int N, e_id;
static int pwv[MAXN];
static int keyidx[130321];                /* 19^4 */
static int elem[MAXN][4];

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

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = inv_[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = mt[(long)x * N + s];
        Ri[k][x] = mt[(long)x * N + si];
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

static int cmp_cand(const void *a, const void *b) {
    int x = ((const Cand *)a)->N, y = ((const Cand *)b)->N;
    return (x > y) - (x < y);
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

    /* candidate groups */
    static Cand cs[160];
    int nc = 0;
    static const int qs[6] = {5, 7, 11, 13, 17, 19};
    for (int qi = 0; qi < 6; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long ord = q * (q * q - 1);
            if (psl) ord /= 2;
            if (ord >= lo && ord <= hi && nc < 160) {
                cs[nc] = (Cand){1, 0, 0, 0, (int)q, psl, (int)ord};
                nc++;
            }
        }
    long step = (hi - lo) / 30;
    if (step < 1) step = 1;
    for (long Nv = lo; Nv <= hi && nc < 160; Nv += step) {
        int cnt = 0, pm = 0, pk = 0, pr = 0;
        for (long m = 3; m <= Nv / 3; m++) {
            if (Nv % m) continue;
            long k = Nv / m;
            if (k < 3) continue;
            for (int r = 2; r < (int)m; r++) {
                if (gcd_i(r, (int)m) != 1) continue;
                if (pw_mod(r, k, m) != 1) continue;
                cnt++;
                if (rndint(cnt) == 0) { pm = (int)m; pk = (int)k; pr = r; }
            }
        }
        if (cnt > 0) {
            cs[nc] = (Cand){0, pm, pk, pr, 0, 0, (int)Nv};
            nc++;
        }
    }
    qsort(cs, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Bracketing search over the sorted candidates.
     * lo_ok: largest index known to succeed (-1 = none yet).
     * hi_bad: smallest index known to fail (nc = none yet).
     * Before any success, probe upward from the smallest order; afterwards bisect. */
    int lo_ok = -1, hi_bad = nc, probe = 0;
    int bestIdx = -1;
    static int bestFound[MAXDEG];
    while (hi_bad - lo_ok > 1) {
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        int mid = (lo_ok < 0) ? probe : (lo_ok + hi_bad) / 2;
        if (mid < 0 || mid >= hi_bad) break;
        double slice = remaining * 0.4;
        if (slice < 0.5) slice = 0.5;
        if (slice > 12.0) slice = 12.0;
        if (slice > remaining) slice = remaining;
        if (!build_cand(&cs[mid])) {
            if (lo_ok < 0) probe = mid + 1; else hi_bad = mid;
            continue;
        }
        if (anneal(now() + slice)) {
            lo_ok = mid;
            bestIdx = mid;
            memcpy(bestFound, S, sizeof(int) * (size_t)d);
        } else {
            if (lo_ok < 0) probe = mid + 1; else hi_bad = mid;
        }
    }

    if (bestIdx < 0) {
        print_complete();
        return 0;
    }
    build_cand(&cs[bestIdx]);
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 10)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
