"""Program: bi-Cayley search over metacyclic groups Z_m x|_r Z_k and PSL/SL(2,q).

Construction (unchanged from the parent):
  * Group G of order N. Bi-Cayley graph: A_x ~ B_{x*s_k} for k < d. d-regular, bipartite, 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D iff BFS from A_e and from B_e reach
    all 2N vertices within D steps.

New in this version:
  * Normalised connection set: s_0 = e is fixed. Relabelling B_y -> B_{y s_0} maps any valid
    graph to one with s_0 = e, so the search space loses one generator and no solutions are lost.
  * Tabu local search instead of a random walk. Each step samples MOVES single-generator
    replacements, takes the best admissible one (tabu on recently removed elements, with
    aspiration), and restarts after a long stall.
  * Least-tried-first scheduler. Every eligible candidate (order above the current best) gets
    a slice that doubles with its own attempt count, so hard hi-window groups are not starved
    by early candidates.
  * Candidate pool: for each order, up to 3 metacyclic groups from different divisors k, with
    the first non-trivial r. Lower-than-record orders descend first, then matrix groups, then
    orders above the record ascend.

Safety: the C engine prints K_{d,d} if it finds nothing. Python checks every output with
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

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MOVES 16
#define STALL_LIMIT 3000
#define LO_CAP 60
#define HI_CAP 120
#define MAT_CAP 16
#define LIST_MAX (LO_CAP + HI_CAP + MAT_CAP + 8)

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
    int q, psl, m, k, r, N;
} Cand;

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    return ok && N >= d + 2;
}

/* Up to 3 metacyclic groups of order Nv, one per divisor k, with the first nontrivial r. */
static void add_meta(int Nv, Cand *arr, int *cnt, int cap) {
    int taken = 0;
    for (int k = 2; k <= Nv / 3 && taken < 3 && *cnt < cap; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        for (int r = 2; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nv;
            arr[(*cnt)++] = c;
            taken++;
            break;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXN];        /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXN];        /* Ri[k][y] = y * s_k^{-1} */
static long tabu_until[MAXDEG][MAXN];

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

/* Normalised start: s_0 = e (WLOG by relabelling B), other generators random and distinct. */
static void randomize_S(void) {
    S[0] = e_id;
    for (int k = 1; k < d; k++) {
        int x;
        do x = rndint(N); while (in_S(x, k));
        S[k] = x;
    }
    for (int k = 0; k < d; k++) set_col(k);
    memset(tabu_until, 0, sizeof tabu_until);
}

/* Tabu search: each step evaluates MOVES random single-generator replacements and takes the
   best admissible one. Re-adding an element removed recently is tabu unless it beats the best. */
static int tabu_climb(double until) {
    randomize_S();
    long cur = cost_now();
    long best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        it++;
        if ((it & 3) == 0 && now() > until) return 0;
        if (stall > STALL_LIMIT) {
            randomize_S();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        long mv_cost = -1;
        int mk = -1, mx = -1, mold = -1;
        for (int mv = 0; mv < MOVES; mv++) {
            int k = 1 + rndint(d - 1);
            int x = -1;
            for (int t = 0; t < 30; t++) {
                int cand = rndint(N);
                if (!in_S(cand, d)) { x = cand; break; }
            }
            if (x < 0) continue;
            int old = S[k];
            S[k] = x;
            set_col(k);
            long nc = cost_now();
            S[k] = old;
            set_col(k);
            int taboo = tabu_until[k][x] > it;
            if (taboo && nc >= best_c) continue;
            if (mv_cost < 0 || nc < mv_cost || (nc == mv_cost && rndint(2))) {
                mv_cost = nc;
                mk = k;
                mx = x;
                mold = old;
            }
        }
        if (mk < 0) { stall++; continue; }
        S[mk] = mx;
        set_col(mk);
        tabu_until[mk][mold] = it + 4 + rndint(8);
        cur = mv_cost;
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
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
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    int recHalf = (int)(ref / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = recHalf + 1;   /* smallest order that beats the record vertex count */

    static Cand lo[LO_CAP], mat[MAT_CAP], hi[HI_CAP], all[LIST_MAX];
    static int tries[LIST_MAX];
    int nl = 0, nm = 0, nh = 0, na = 0;

    /* lower-than-record orders, descending (cheap wins first) */
    for (int Nv = recHalf; Nv >= lowN && nl < LO_CAP; Nv--) add_meta(Nv, lo, &nl, LO_CAP);

    /* matrix groups in the window */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            if (nm >= MAT_CAP) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            mat[nm++] = c;
        }
    }

    /* orders beating the record, ascending (hard, last) */
    for (int Nv = recN; Nv <= hiN && nh < HI_CAP; Nv++) add_meta(Nv, hi, &nh, HI_CAP);

    for (int i = 0; i < nl; i++) all[na++] = lo[i];
    for (int i = 0; i < nm; i++) all[na++] = mat[i];
    for (int i = 0; i < nh; i++) all[na++] = hi[i];

    /* least-tried-first scheduler: slice doubles with each candidate's own attempt count */
    long bestN = d;
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);
    static int bS[MAXDEG];

    double budget0 = t_end - now();
    double base = budget0 * 0.015;
    if (base < 0.2) base = 0.2;

    for (;;) {
        double remaining = t_end - now();
        if (remaining < 0.1) break;
        int pick = -1;
        for (int i = 0; i < na; i++) {
            if ((long)all[i].N <= bestN) continue;
            if (2L * all[i].N > moore) continue;
            if (pick < 0 || tries[i] < tries[pick]) pick = i;
        }
        if (pick < 0) break;
        int tcount = tries[pick]++;
        if (!apply_cand(&all[pick])) { tries[pick] += 1000; continue; }
        int sh = tcount < 6 ? tcount : 6;
        double slice = base * (double)(1 << sh);
        if (slice > remaining) slice = remaining;
        if (tabu_climb(now() + slice)) {
            have = 1;
            bestN = N;
            best = all[pick];
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
    # Leave a margin for compile, I/O and validation.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # a Moore graph is already optimal
    if budget > 0.2:
        ref = REF_VERTICES.get((d, D), max(best[0], 2 * d))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 5.0)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
