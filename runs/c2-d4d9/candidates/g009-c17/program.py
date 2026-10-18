"""Program: bi-Cayley search over metacyclic groups Z_m x| Z_k, plus PSL/SL(2,q).

Construction:
  * Group G of order N (full multiplication table, N <= 3200).
  * Bi-Cayley graph: A_x is joined to B_{x*s_k} for k < d. d-regular, bipartite, 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D holds iff BFS from A_e and
    from B_e both reach all 2N vertices within D steps. The cost is the number of
    unreached vertices.

New in this version:
  * Greedy seeding: connection elements are added one at a time, each chosen from random
    samples to minimise the partial-ball cost (the ball is computed over the first j
    columns only).
  * Simulated annealing with a time-based temperature schedule replaces the fixed
    2% random-acceptance rule.
  * Iterated local search: each candidate keeps its best connection set between rounds,
    and restarts perturb that set by one or two elements instead of starting from scratch.
  * Scheduling: a few metacyclic groups just below the record secure a fallback, then
    groups from N = record/2 + 1 upward get round-robin time slices that double each round.

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

#define MAXN 3200
#define MAXV (2 * MAXN)
#define MAXDEG 8
#define MAXCAND 48
#define NOCOST (1L << 60)

static int d, D, dcur;
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
    int S[MAXDEG];      /* best connection set kept between rounds */
    long bestcost;      /* best cost reached on this group */
    int seeded;         /* S holds a usable state */
    int dead;
} Cand;

static Cand cs[MAXCAND];
static int ncs = 0;

static void push_cand(Cand c) {
    if (ncs >= MAXCAND) return;
    c.bestcost = NOCOST;
    c.seeded = 0;
    c.dead = 0;
    memset(c.S, 0, sizeof c.S);
    cs[ncs++] = c;
}

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static int add_meta(int Nval, int maxadd) {
    int added = 0;
    for (int k = 2; k <= Nval / 3 && added < maxadd && ncs < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && added < maxadd && ncs < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            push_cand(c);
            got++;
            added++;
        }
    }
    return added;
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

/* true if x equals one of S[0..m-1] */
static int in_S(int x, int m) {
    for (int k = 0; k < m; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Ball from src within dmax steps, using the first dcur columns only. */
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
                for (int k = 0; k < dcur; k++) {
                    int u = N + Rr[k][v];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < dcur; k++) {
                    int u = Ri[k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of (A,A), (A,B), (B,B) pairs not covered within D; 0 iff valid. */
static long cost_now(void) {
    return (long)(2 * N - ball(e_id, D)) + (long)(2 * N - ball(N + e_id, D));
}

/* ------------------------------------------------------------------ greedy seeding (new) */

/* Choose S[0..d-1] one element at a time. Each new element is the best of `samples`
   random candidates, judged by the cost of the partial graph with the columns so far. */
static void greedy_seed(int samples) {
    for (int j = 0; j < d; j++) {
        long bc = NOCOST;
        int bx = -1;
        for (int t = 0; t < samples; t++) {
            int x = rndint(N);
            if (in_S(x, j)) continue;
            S[j] = x;
            set_col(j);
            dcur = j + 1;
            long c = cost_now();
            if (c < bc) { bc = c; bx = x; }
        }
        if (bx < 0) {
            do bx = rndint(N); while (in_S(bx, j));
        }
        S[j] = bx;
        set_col(j);
    }
    dcur = d;
}

/* ------------------------------------------------------------------ annealing (new schedule) */

static int gS[MAXDEG];
static long gbest = NOCOST;

/* Simulated annealing over single-element replacements. Temperature falls linearly
   from T0 to about 0.02 over the interval. Keeps the global best in gS / gbest. */
static long anneal(double until, double T0) {
    dcur = d;
    long cur = cost_now();
    if (cur < gbest) { gbest = cur; memcpy(gS, S, sizeof(int) * (size_t)d); }
    double t0 = now();
    if (until <= t0 || cur == 0) return cur;
    double span = until - t0;
    double T = T0;
    unsigned long it = 0;
    while (cur > 0) {
        if ((++it & 31UL) == 0) {
            double tn = now();
            if (tn >= until) break;
            T = T0 * (1.0 - (tn - t0) / span) + 0.02;
        }
        int k = rndint(d);
        int old = S[k];
        int x;
        do x = rndint(N); while (in_S(x, d));
        S[k] = x;
        set_col(k);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < gbest) { gbest = cur; memcpy(gS, S, sizeof(int) * (size_t)d); }
        } else {
            S[k] = old;
            set_col(k);
        }
    }
    return cur;
}

/* Iterated local search on the current group, until time `until`.
   `seeded` says whether gS already holds a state from an earlier round.
   Each step is either a fresh greedy seed or a small perturbation of gS. */
static int search_group(double until, int seeded) {
    double total = until - now();
    if (total <= 0) return gbest == 0;
    double chunk = total / 6.0;
    if (chunk < 0.2) chunk = 0.2;
    int have = seeded;
    dcur = d;
    while (gbest > 0 && now() < until - 0.02) {
        double cu = now() + chunk;
        if (cu > until) cu = until;
        double T0;
        if (!have || rnd01() < 0.35) {
            greedy_seed(48);
            have = 1;
            T0 = 1.5;
        } else {
            memcpy(S, gS, sizeof(int) * (size_t)d);
            int reps = 1 + rndint(2);
            for (int r = 0; r < reps; r++) {
                int k = rndint(d), x;
                do x = rndint(N); while (in_S(x, d));
                S[k] = x;
            }
            for (int k = 0; k < d; k++) set_col(k);
            T0 = 0.6;
        }
        anneal(cu, T0);
    }
    return gbest == 0;
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }
    dcur = d;

    long moore = moore_bound();
    long bestN = d;

    int recHalf = (int)(ref / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = recHalf + 1;   /* smallest N that beats the record vertex count */

    /* 1. matrix groups in the window (fallbacks) */
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lowN || o > hiN || o > MAXN) continue;
            if (ncs >= 12) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            push_cand(c);
        }
    }

    /* 2. a few metacyclic groups just below the record (secure a fallback) */
    int nlo = 0;
    for (int Nv = recN - 1; Nv >= lowN && nlo < 3 && ncs < MAXCAND; Nv--)
        nlo += add_meta(Nv, 3 - nlo);

    /* 3. metacyclic groups beating the record, ascending (the real targets) */
    for (int Nv = recN; Nv <= hiN && ncs < MAXCAND; Nv++)
        add_meta(Nv, 2);

    /* Round-robin with doubling slices. Each candidate keeps its best state between rounds. */
    double usable_left = t_end - now();
    double base = usable_left * 0.03;
    if (base < 0.5) base = 0.5;
    int bestIdx = -1;

    for (int round = 0; round < 6; round++) {
        for (int i = 0; i < ncs; i++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &cs[i];
            if (c->dead) continue;
            if ((long)c->N <= bestN) continue;
            if (2L * c->N > moore) continue;
            double slice = base * (double)(1 << round);
            if (slice > rem - 0.1) slice = rem - 0.1;
            if (slice < 0.1) break;
            if (!apply_cand(c)) { c->dead = 1; continue; }
            gbest = c->bestcost;
            memcpy(gS, c->S, sizeof(int) * (size_t)d);
            int ok = search_group(now() + slice, c->seeded);
            c->bestcost = gbest;
            memcpy(c->S, gS, sizeof(int) * (size_t)d);
            c->seeded = 1;
            if (ok) {
                bestN = c->N;
                bestIdx = i;
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (bestIdx < 0 || !apply_cand(&cs[bestIdx])) { print_complete(); return 0; }
    memcpy(S, cs[bestIdx].S, sizeof(int) * (size_t)d);
    dcur = d;
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
    # Use most of the case's time for the C search; keep a margin for compile, I/O and checks.
    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.0
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
