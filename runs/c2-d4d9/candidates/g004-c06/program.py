"""Program: bi-Cayley graphs over metacyclic semidirect products and PSL/SL(2,q).

Construction (bi-Cayley, bipartite, d-regular): parts A and B, each indexed by a finite
group G of order N. Vertex A_x is joined to B_{x s_k} for k < d. Left multiplication by
any h in G is an automorphism, so the diameter is <= D iff BFS from A_e and from B_e
both reach all 2N vertices within D steps.

New in this version (not in the parent):
  * Groups are not limited to PSL/SL(2,q). The engine also uses metacyclic semidirect
    products Z_M x|_R Z_K (R^K = 1 mod M, gcd(R, M) = 1, R != 1), with closed-form
    multiplication. This gives a dense family of group orders, so we can search
    orders just above 2N = 4970 (N = 2485).
  * Normalisation: right-multiplying S by g gives an isomorphic graph, so s_0 is fixed
    to the identity. This shrinks the search space by a factor of N.
  * Ladder search: candidate groups are sorted by order ascending (random tie-break).
    Each group gets a short time slice of simulated-annealing hill climbing. A success
    raises the bar, and only larger groups are tried after that.

Safety: the C engine always prints a valid graph (K_{d,d} if nothing is found). Python
checks it with lib.is_valid and keeps the best valid graph, falling back to the known
start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over semidirect products Z_M x| Z_K and PSL/SL(2,q).
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * Output: "n m" then m lines "u v": bipartite, every degree d, diameter <= D.
 * Vertices: A_x = x, B_y = N + y. Edges: A_x -- B_{x*s_k}.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3600
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 400000

static int d, D;
static double t_begin, t_stop;

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

/* ------------------------------------------------------------------ groups */

static int gtype = 0;          /* 0: semidirect Z_GM x| Z_GK, 1: matrix PSL/SL(2,Q) */
static int GM, GK, GR;
static int pw[MAXN];           /* pw[b] = GR^b mod GM */
static int Q, PSL;
static int mat[MAXN][4];
static int *midx = NULL;
static int midx_cap = 0;
static int N = 0, E_ID = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int build_sd(int M, int K, int R) {
    if (M * K > MAXN) return 0;
    gtype = 0;
    GM = M; GK = K; GR = R;
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (pw[b - 1] * R) % M;
    N = M * K;
    E_ID = 0;
    return N;
}

static int mat_key(int a, int b, int c, int e) {
    int k = ((a * Q + b) * Q + c) * Q + e;
    if (!PSL) return k;
    int na = (Q - a) % Q, nb = (Q - b) % Q, nc = (Q - c) % Q, ne = (Q - e) % Q;
    int kn = ((na * Q + nb) * Q + nc) * Q + ne;
    return k < kn ? k : kn;
}

static int mat_lookup(int a, int b, int c, int e) { return midx[mat_key(a, b, c, e)]; }

static int build_matrix(int q, int psl) {
    gtype = 1;
    Q = q; PSL = psl;
    int ks = q * q * q * q;
    if (ks > midx_cap) {
        free(midx);
        midx = malloc(sizeof(int) * (size_t)ks);
        midx_cap = ks;
    }
    for (int i = 0; i < ks; i++) midx[i] = -1;
    N = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (mat_key(a, b, c, e) != own) continue;
                    if (N >= MAXN) return 0;
                    mat[N][0] = a; mat[N][1] = b; mat[N][2] = c; mat[N][3] = e;
                    midx[own] = N;
                    N++;
                }
    E_ID = mat_lookup(1, 0, 0, 1);
    return N;
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
        return ((a + pw[b] * c) % GM) * GK + (b + e) % GK;
    }
    const int *p = mat[x], *r = mat[y];
    return mat_lookup((p[0] * r[0] + p[1] * r[2]) % Q,
                      (p[0] * r[1] + p[1] * r[3]) % Q,
                      (p[2] * r[0] + p[3] * r[2]) % Q,
                      (p[2] * r[1] + p[3] * r[3]) % Q);
}

static inline int ginv(int x) {
    if (gtype == 0) {
        int a = x / GK, b = x % GK;
        int nb = (GK - b) % GK;
        return ((GM - (pw[nb] * a) % GM) % GM) * GK + nb;
    }
    const int *p = mat[x];
    return mat_lookup(p[3], (Q - p[1]) % Q, (Q - p[2]) % Q, p[0]);
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int type, a, b, c, n; unsigned key; } Cand;
static Cand cand_arr[MAXCAND];
static int ncand = 0;

static void add_cand(int type, int a, int b, int c, int n) {
    if (ncand >= MAXCAND) return;
    cand_arr[ncand].type = type;
    cand_arr[ncand].a = a;
    cand_arr[ncand].b = b;
    cand_arr[ncand].c = c;
    cand_arr[ncand].n = n;
    cand_arr[ncand].key = (unsigned)rnd();
    ncand++;
}

static int cmp_cand(const void *p, const void *q) {
    const Cand *x = p, *y = q;
    if (x->n != y->n) return x->n < y->n ? -1 : 1;
    return (x->key > y->key) - (x->key < y->key);
}

static void gen_candidates(long lo, long hi) {
    ncand = 0;
    static const int qs[] = {5, 7, 11, 13, 17, 19, 23};
    for (unsigned i = 0; i < sizeof qs / sizeof qs[0]; i++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[i];
            long ord = q * (q * q - 1);
            if (psl) ord /= 2;
            if (ord >= lo && ord <= hi && ord <= MAXN)
                add_cand(1, (int)q, psl, 0, (int)ord);
        }
    }
    for (long M = 3; M <= hi / 2; M++) {
        long Klo = (lo + M - 1) / M;
        if (Klo < 2) Klo = 2;
        long Khi = hi / M;
        for (long K = Klo; K <= Khi; K++) {
            long n = M * K;
            if (n < lo || n > hi) continue;
            for (long R = 2; R < M; R++) {
                if (gcd_i((int)R, (int)M) != 1) continue;
                if (powmod_i((int)R, (int)K, (int)M) != 1 % (int)M) continue;
                add_cand(0, (int)M, (int)K, (int)R, (int)n);
            }
        }
    }
}

static int build_from(const Cand *c) {
    if (c->type == 0) return build_sd(c->a, c->b, c->c);
    return build_matrix(c->a, c->b);
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];   /* Ri[k][y] = y * s_k^{-1} */

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

/* Right-multiplying S by g gives an isomorphic graph, so s_0 is fixed to the identity. */
static void randomize_S(void) {
    S[0] = E_ID;
    for (int k = 1; k < d; k++) {
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
    return (long)(2 * N - ball(E_ID, D)) + (long)(2 * N - ball(N + E_ID, D));
}

/* Simulated-annealing hill climb over s_1..s_{d-1}. Returns 1 with S valid. */
static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 31) == 0 && now() > until) return 0;
        if (stall > 4000) {
            randomize_S();
            cur = cost_now();
            best = cur;
            stall = 0;
            continue;
        }
        int k = 1 + rndint(d - 1);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / 0.6)) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
        }
        if (cur < best) { best = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

static int attempt(const Cand *c, double until) {
    int n = build_from(c);
    if (n <= 0) return 0;
    return climb(until);
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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
    t_begin = now();
    t_stop = t_begin + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long half = moore / 2;             /* largest allowed group order N */
    long lo = half / 5;
    if (lo < 3) lo = 3;
    long hi = half;
    if (hi > MAXN) hi = MAXN;
    if (hi < lo) { print_complete(); return 0; }

    gen_candidates(lo, hi);
    qsort(cand_arr, (size_t)ncand, sizeof(Cand), cmp_cand);

    long best_N = 0;
    Cand bestc;
    int bestS[MAXDEG];
    for (int i = 0; i < ncand; i++) {
        Cand *c = &cand_arr[i];
        if (c->n <= best_N) continue;
        double rem = t_stop - now();
        if (rem < 0.2) break;
        double slice = rem * 0.08;
        if (slice > 3.0) slice = 3.0;
        if (slice < 0.4) slice = 0.4;
        if (slice > rem) slice = rem;
        if (attempt(c, now() + slice)) {
            best_N = c->n;
            bestc = *c;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            if (2 * best_N >= moore) break;   /* Moore bound reached */
        }
    }

    if (best_N == 0) {
        print_complete();
        return 0;
    }
    build_from(&bestc);
    memcpy(S, bestS, sizeof(int) * (size_t)d);
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
