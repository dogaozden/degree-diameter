"""Program: bi-Cayley search over metacyclic groups and PSL/SL(2,q), with a
symmetry-reduced tabu search.

Construction:
  * Group G of order N (full multiplication table, N <= 3200). The bi-Cayley graph
    joins A_x to B_{x*s_k} for k < d. It is d-regular and bipartite with 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D iff BFS from A_e and from
    B_e both reach all 2N vertices within D steps.

New in this version:
  * Normalisation: replacing S by {s_0^{-1} s} with A_x relabelled to A_{x s_0} gives an
    isomorphic graph, so S[0] = e can be fixed. This removes one free coordinate.
  * Tabu search with sampled neighbourhoods: each move samples SAMPLES random
    (coordinate, element) replacements, applies the best non-tabu one, and forbids
    reverting for TENURE moves. Restarts happen after STALL_LIMIT non-improving moves.
  * Ascending-N target schedule: candidates just at or above the record half-order are
    tried first. Fallback candidates (matrix groups and metacyclic groups just below the
    record) come first in each round, with a larger slice. Slices double per round.
  * Record half-order itself (N = 2485, giving 4970 vertices) is now a candidate.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 160
#define SAMPLES 48
#define TENURE 25
#define STALL_LIMIT 1500

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

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++) {
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    N = n;
    alloc_group(N);
    static int pw[MAXN];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return N;
}

/* PSL(2,q) or SL(2,q), q prime. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > idxm_cap) {
        free(idxm);
        idxm = malloc(sizeof(int) * (size_t)ks);
        idxm_cap = ks;
    }
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXN) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    N = cnt;
    alloc_group(N);
    for (int x = 0; x < N; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        for (int y = 0; y < N; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[(size_t)x * N + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return N;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int tier;   /* 0 = fallback (try first), 1 = target */
    int q, psl, m, k, r, N;
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static int add_meta(int Nval, Cand *arr, int cnt, int tier, int maxcnt) {
    for (int k = 2; k <= Nval / 3 && cnt < maxcnt; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && cnt < maxcnt; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.tier = tier;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            arr[cnt++] = c;
            got++;
        }
    }
    return cnt;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->tier != y->tier) return x->tier - y->tier;
    if (x->tier == 0) return y->N - x->N;   /* fallbacks: largest first */
    return x->N - y->N;                     /* targets: smallest first */
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];          /* S[0] = identity always (normalisation) */
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + s];
        Ri[k][x] = (int)T[(size_t)x * N + si];
    }
}

static void set_all_cols(void) {
    for (int k = 0; k < d; k++) set_col(k);
}

static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
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

/* Number of (source, target) pairs at distance > D from A_e and from B_e. */
static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

static void randomize_S(void) {
    S[0] = e_id;
    for (int k = 1; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    set_all_cols();
}

/* ------------------------------------------------------------------ tabu search */

static long tabu_until[MAXDEG][MAXN];
static int bestS[MAXDEG];

/* Sampled tabu search over S[1..d-1]. Returns 1 with S set to a valid set if found. */
static int tabu_search(double until) {
    randomize_S();
    long cur = cost_now();
    long bestc = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)d);
    memset(tabu_until, 0, sizeof tabu_until);
    long it = 1, stall = 0;
    while (cur > 0) {
        if (now() > until) break;
        ++it;
        int bk = -1, bx = -1;
        long bc = LONG_MAX;
        for (int t = 0; t < SAMPLES; t++) {
            int k = 1 + rndint(d - 1);
            int x = rndint(N);
            if (in_S(x, d) || tabu_until[k][x] > it) continue;
            int old = S[k];
            S[k] = x;
            set_col(k);
            long c = cost_now();
            S[k] = old;
            set_col(k);
            if (c < bc || (c == bc && (rnd() & 1))) { bc = c; bk = k; bx = x; }
        }
        if (bk < 0) continue;
        int old = S[bk];
        tabu_until[bk][old] = it + TENURE;
        S[bk] = bx;
        set_col(bk);
        cur = bc;
        if (cur < bestc) {
            bestc = cur;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            stall = 0;
        } else if (++stall > STALL_LIMIT) {
            randomize_S();
            cur = cost_now();
            stall = 0;
        }
    }
    if (bestc == 0) {
        memcpy(S, bestS, sizeof(int) * (size_t)d);
        set_all_cols();
        return 1;
    }
    return 0;
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
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long bestN = d;

    int recHalf = (int)(ref / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;

    static Cand all[MAXCAND];
    int na = 0;

    /* 1. matrix groups: fallbacks below the record half, targets at or above it */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXN || na >= MAXCAND) continue;
            int tier = -1;
            if (o >= lowN && o < recHalf) tier = 0;
            else if (o >= recHalf && o <= hiN) tier = 1;
            if (tier < 0) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.tier = tier;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            all[na++] = c;
        }
    }

    /* 2. metacyclic fallbacks just below the record half */
    for (int Nv = recHalf - 1; Nv >= recHalf - 6 && Nv >= lowN; Nv--)
        na = add_meta(Nv, all, na, 0, MAXCAND);

    /* 3. metacyclic targets from the record half upward, smallest N first */
    for (int Nv = recHalf; Nv <= hiN && na < MAXCAND; Nv++)
        na = add_meta(Nv, all, na, 1, MAXCAND);

    qsort(all, (size_t)na, sizeof(Cand), cmp_cand);

    /* Round-robin schedule: slices double each round. Fallbacks get 3x the slice. */
    double budget = t_end - now();
    int nb = na > 0 ? na : 1;
    double base = budget / (6.0 * nb);
    if (base < 0.6) base = 0.6;

    int have = 0;
    int stop = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int finalS[MAXDEG];

    for (int round = 0; round < 16 && !stop; round++) {
        for (int i = 0; i < na && !stop; i++) {
            double remaining = t_end - now();
            if (remaining < 0.3) { stop = 1; break; }
            Cand *c = &all[i];
            if ((long)c->N <= bestN) continue;
            if (2L * c->N > moore) continue;
            if (!apply_cand(c)) continue;
            double mult = (c->tier == 0) ? 3.0 : 1.0;
            double slice = base * mult * (double)(1L << round);
            if (slice > remaining) slice = remaining;
            if (tabu_search(now() + slice)) {
                have = 1;
                bestN = N;
                best = *c;
                memcpy(finalS, S, sizeof(int) * (size_t)d);
            }
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    memcpy(S, finalS, sizeof(int) * (size_t)d);
    set_all_cols();
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
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing can beat it, skip the search
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget > 0.5:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
