"""Program: bi-Cayley search over metacyclic groups and SL/PSL/PGL(2,q).

Construction:
  * Group G of order N, given by a full multiplication table (N <= 5000).
  * Bi-Cayley graph: A_x is joined to B_{x*s_k} for k < d. This is d-regular, bipartite,
    and has 2N vertices.
  * Left multiplication by any h in G is an automorphism, so diameter <= D holds iff
    BFS from A_e and from B_e both reach all 2N vertices within D steps.

New in this version:
  * Matrix family extended to PGL(2,q) (projective normalisation, order q^3-q), SL(2,q)
    (order q^3-q) and PSL(2,q), so orders above the old window (up to 5000) are reachable.
    For d=4, D=9 this includes SL(2,17) and PGL(2,17) of order 4896 and PSL(2,19) of order 3420.
  * Tiered candidate order: tier A holds candidates at or below the record half-order
    (cheap secure fallback, largest first). Tier B holds candidates that beat the record
    (ascending order, so the smallest improvement is tried first).
  * Iterated local search: when a climb stalls, it kicks back from the best configuration
    seen in that run, and only restarts randomly after repeated failed kicks.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph, falling back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 5000
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 80

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

/* SL(2,q) (mode 0), PSL(2,q) (mode 1), PGL(2,q) (mode 2), q prime.
   Every mode has a canonical representative per group element. */
static int qg, psl_g;
static int gmat[MAXN][4];
static int *idxm = NULL;
static int idxm_cap = 0;

/* PGL: scale the matrix so its first nonzero entry is 1. */
static int norm_pgl(int a, int b, int c, int e) {
    int v[4] = {a, b, c, e};
    int f = 0;
    for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
    if (!f) return -1;
    long iv = powmod_l(f, qg - 2, qg);
    for (int i = 0; i < 4; i++) v[i] = (int)((long)v[i] * iv % qg);
    return ((v[0] * qg + v[1]) * qg + v[2]) * qg + v[3];
}

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    if (psl_g == 2) return norm_pgl(a, b, c, e);
    int k = ((a * q + b) * q + c) * q + e;
    if (psl_g == 0) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int mode) {
    qg = q;
    psl_g = mode;
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
                    int det = (((a * e - b * c) % q) + q) % q;
                    if (mode == 2) {
                        if (det == 0) continue;
                    } else {
                        if (det != 1) continue;
                    }
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
    int q, psl, m, k, r, N;
    double key; /* sort key: smaller is tried first */
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static int cand_cmp(const void *a, const void *b) {
    double x = ((const Cand *)a)->key, y = ((const Cand *)b)->key;
    return (x < y) ? -1 : (x > y);
}

static void add_meta(int Nval, Cand *arr, int *cnt, int cap) {
    for (int k = 2; k <= Nval / 3 && *cnt < cap; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < cap; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rr[k][x] = (int)T[(size_t)x * N + s];
        Ri[k][x] = (int)T[(size_t)x * N + si];
    }
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

static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

static void randomize_S(void) {
    for (int k = 0; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
}

/* Annealed local search with iterated kicks: after a stall, return to the best
   configuration of this run and change 1-2 generators. Full random restarts happen
   only after many unsuccessful kicks. */
static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    int cS[MAXDEG];
    memcpy(cS, S, sizeof(int) * (size_t)d);
    int kicks = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > 3000) {
            if (kicks >= 25) {
                randomize_S();
                cur = cost_now();
                best_c = cur;
                memcpy(cS, S, sizeof(int) * (size_t)d);
                kicks = 0;
                stall = 0;
                continue;
            }
            memcpy(S, cS, sizeof(int) * (size_t)d);
            int nk = 1 + rndint(2);
            for (int j = 0; j < nk; j++) {
                int k = rndint(d);
                int x;
                do x = rndint(N); while (in_S(x, d));
                S[k] = x;
            }
            for (int k = 0; k < d; k++) set_col(k);
            cur = cost_now();
            kicks++;
            stall = 0;
            continue;
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
        }
        if (cur < best_c) {
            best_c = cur;
            stall = 0;
            kicks = 0;
            memcpy(cS, S, sizeof(int) * (size_t)d);
        } else {
            stall++;
        }
    }
    return 1;
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long bestN = d;

    int recHalf = (int)(ref / 2);
    int recN = recHalf + 1;   /* smallest N whose 2N beats the record vertex count */
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;

    static Cand lo[MAXCAND], hi[MAXCAND], all[3 * MAXCAND + 8];
    int nl = 0, nh = 0, na = 0;

    /* Matrix groups: SL, PSL and PGL(2,q) for prime q, in the admissible window. */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int mode = 0; mode < 3; mode++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (mode == 1) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = mode;
            c.N = (int)o;
            if (o <= recHalf) {
                if (nl < MAXCAND) lo[nl++] = c;
            } else {
                if (nh < MAXCAND) hi[nh++] = c;
            }
        }
    }

    /* Tier A: metacyclic groups at or below the record half-order, largest first. */
    for (int Nv = recHalf; Nv >= lowN && nl < 16; Nv--) add_meta(Nv, lo, &nl, 16);
    /* Tier B: metacyclic groups beating the record, smallest first. */
    for (int Nv = recN; Nv <= hiN && nh < 60; Nv++) add_meta(Nv, hi, &nh, 60);

    for (int i = 0; i < nl; i++) {
        lo[i].key = -(double)lo[i].N;
        all[na++] = lo[i];
    }
    for (int i = 0; i < nh; i++) {
        hi[i].key = 1e6 + (double)hi[i].N;
        all[na++] = hi[i];
    }
    qsort(all, (size_t)na, sizeof(Cand), cand_cmp);

    double budget0 = t_end - now();
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    /* Iterative deepening: each round gives every still-improving candidate a slice,
       and the slice doubles per round. */
    double base_slice = budget0 * 0.015;
    if (base_slice < 0.3) base_slice = 0.3;
    for (int round = 0; round < 8; round++) {
        for (int i = 0; i < na; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &all[i];
            if ((long)c->N <= bestN) continue;
            if (2L * c->N > moore) continue;
            if (!apply_cand(c)) continue;
            double slice = base_slice * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestN = N;
                best = *c;
                memcpy(bS, S, sizeof(int) * (size_t)d);
            }
        }
        if (t_end - now() < 0.2) break;
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
