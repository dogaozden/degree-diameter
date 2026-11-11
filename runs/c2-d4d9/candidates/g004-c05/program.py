"""Program: bi-Cayley search over metacyclic groups Z_m x| Z_k and SL/PSL(2,q).

Construction:
  * Group G of order N. Bi-Cayley graph: A_x is joined to B_{x*s_k} for k < d.
    This is d-regular, bipartite, with 2N vertices.
  * Left multiplication by any h in G is an automorphism, so diameter <= D holds iff
    BFS from A_e and from B_e reaches all 2N vertices within D steps.
  * Group multiplication is computed on the fly (no table), so large groups fit.

Search: simulated annealing over the connection set (worsening moves accepted with
probability exp(-delta/T)), with restarts after long stalls.

Candidate schedule (ref = target vertex count R, half = R/2):
  A. SL/PSL(2,q) with order in [0.87*half, half]    (fallback; SL(2,13) gives 4368)
  B. metacyclic groups with order just below half, descending (first success is largest)
  C. PSL(2,19) (order 3420) and metacyclic groups in [half+1, 1.4*half], ascending.
Each phase has its own deadline. Each candidate's slice is capped, and a success
raises the bar so later candidates must have larger order.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output
with lib.is_valid and keeps the best valid graph, falling back to the known start
or K_{d,d}.
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
#define MAXPOOL 96

static int d, D;
static double t_end;
static long MOORE;

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* gtype 0: Z_MM x| Z_KK, element (a,b) coded a*KK+b, (a,b)(c,d) = (a + r^b c, b + d).
 * gtype 1: SL(2,Q) or PSL(2,Q), elements are matrices indexed by canonical key. */
static int gtype = 0;
static int N = 0, e_id = 0;
static int MM = 1, KK = 1;
static int pw[MAXG];
static int Q = 2, PSL = 0;
static int gm[MAXG][4];
static int *idx = NULL;
static int idx_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int k = ((a * Q + b) * Q + c) * Q + e;
    if (!PSL) return k;
    int na = (Q - a) % Q, nb = (Q - b) % Q, nc = (Q - c) % Q, ne = (Q - e) % Q;
    int kn = ((na * Q + nb) * Q + nc) * Q + ne;
    return k < kn ? k : kn;
}

static int lookup(int a, int b, int c, int e) { return idx[canon_key(a, b, c, e)]; }

static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXG || n < 4 || m < 3 || k < 2) return 0;
    gtype = 0;
    N = n;
    MM = m;
    KK = k;
    e_id = 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    return N;
}

static int build_matrix(int qq, int psl) {
    Q = qq;
    PSL = psl;
    gtype = 1;
    int ks = Q * Q * Q * Q;
    if (ks > idx_cap) {
        free(idx);
        idx = malloc(sizeof(int) * (size_t)ks);
        idx_cap = ks;
    }
    for (int i = 0; i < ks; i++) idx[i] = -1;
    int cnt = 0;
    for (int a = 0; a < Q; a++)
        for (int b = 0; b < Q; b++)
            for (int c = 0; c < Q; c++)
                for (int e = 0; e < Q; e++) {
                    if ((((a * e - b * c) % Q) + Q) % Q != 1) continue;
                    int own = ((a * Q + b) * Q + c) * Q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXG) return 0;
                    gm[cnt][0] = a; gm[cnt][1] = b; gm[cnt][2] = c; gm[cnt][3] = e;
                    idx[own] = cnt;
                    cnt++;
                }
    N = cnt;
    e_id = lookup(1, 0, 0, 1);
    return N;
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / KK, b = x - a * KK;
        int c = y / KK, dd = y - c * KK;
        int aa = (a + (int)((long)pw[b] * c % MM)) % MM;
        int bb = b + dd;
        if (bb >= KK) bb -= KK;
        return aa * KK + bb;
    } else {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        int a2 = gm[y][0], b2 = gm[y][1], c2 = gm[y][2], e2 = gm[y][3];
        return lookup((a * a2 + b * c2) % Q, (a * b2 + b * e2) % Q,
                      (c * a2 + e * c2) % Q, (c * b2 + e * e2) % Q);
    }
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / KK, b = x - a * KK;
        int nb = (KK - b) % KK;
        int c = (int)(((long)(MM - a) % MM) * pw[nb] % MM);
        return c * KK + nb;
    } else {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        return lookup(e, (Q - b) % Q, (Q - c) % Q, a);
    }
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int type, q, psl, m, k, r, N; double frac; } Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void push_cand(Cand *pool, int *cnt, int cap, Cand c) {
    if (*cnt < cap) pool[(*cnt)++] = c;
}

/* Matrix groups with order in [lo, hi], ascending order. */
static void add_matrix(Cand *pool, int *cnt, long lo, long hi, long moore, double frac) {
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    Cand tmp[16];
    int nt = 0;
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long qq = qs[qi];
            long o = qq * (qq * qq - 1);
            if (psl) o /= 2;
            if (o < lo || o > hi || 2 * o > moore || o > MAXG) continue;
            if (nt >= 16) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)qq;
            c.psl = psl;
            c.N = (int)o;
            c.frac = frac;
            tmp[nt++] = c;
        }
    for (int i = 1; i < nt; i++) {
        Cand t = tmp[i];
        int j = i - 1;
        while (j >= 0 && tmp[j].N > t.N) { tmp[j + 1] = tmp[j]; j--; }
        tmp[j + 1] = t;
    }
    for (int i = 0; i < nt; i++) push_cand(pool, cnt, MAXPOOL, tmp[i]);
}

/* Metacyclic groups of order Nv with a few r per divisor k. */
static void add_meta(int Nv, Cand *pool, int *cnt, double frac) {
    for (int k = 2; k <= Nv / 3 && *cnt < MAXPOOL; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < MAXPOOL; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nv;
            c.frac = frac;
            push_cand(pool, cnt, MAXPOOL, c);
            got++;
        }
    }
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG], SI[MAXDEG];
static int Rr[MAXDEG][MAXG];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXG];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = ginv(s);
    SI[k] = si;
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

/* Pairs unreached within D steps from A_e and B_e; 0 means diameter <= D. */
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

/* Simulated annealing over the connection set. Returns 1 when cost is 0, 0 on timeout. */
static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 31) == 0 && now() > until) return 0;
        if (stall > 20000) {
            randomize_S();
            cur = cost_now();
            best_c = cur;
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
        long delta = nc - cur;
        double T = 0.2 + 0.005 * (double)cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            S[k] = old;
            set_col(k);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ driver */

static int have = 0;
static long bestN = 0;
static Cand best;
static int bS[MAXDEG];

static void run_pool(Cand *pool, int n, double phase_end, double usable) {
    for (int i = 0; i < n; i++) {
        double rem = phase_end - now();
        if (rem < 0.2) break;
        Cand *c = &pool[i];
        if ((long)c->N <= bestN) continue;
        if (2L * c->N > MOORE) continue;
        if (!apply_cand(c)) continue;
        double slice = usable * c->frac;
        if (slice > rem) slice = rem;
        if (climb(now() + slice)) {
            have = 1;
            bestN = N;
            best = *c;
            memcpy(bS, S, sizeof(int) * (size_t)d);
        }
    }
}

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
    long ref = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 2.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    MOORE = moore_bound();
    if (ref <= 0) ref = MOORE / 4;
    if (ref < 2 * d) ref = 2 * d;

    long half = ref / 2;
    long lo = (long)(0.87 * (double)half);
    if (lo < 4) lo = 4;
    long recN = half + 1;             /* smallest group order giving > ref vertices */
    long hi = (long)(1.40 * (double)half);
    if (hi > MAXG) hi = MAXG;
    if (2 * hi > MOORE) hi = MOORE / 2;
    long loTop = recN - 1;

    static Cand poolA[MAXPOOL], poolB[MAXPOOL], poolC[MAXPOOL];
    int nA = 0, nB = 0, nC = 0;
    add_matrix(poolA, &nA, lo, loTop, MOORE, 0.12);
    for (long Nv = loTop; Nv >= lo && nB < MAXPOOL; Nv--)
        add_meta((int)Nv, poolB, &nB, 0.06);
    add_matrix(poolC, &nC, recN, hi, MOORE, 0.04);
    for (long Nv = recN; Nv <= hi && nC < MAXPOOL; Nv++)
        add_meta((int)Nv, poolC, &nC, 0.04);

    run_pool(poolA, nA, t0 + 0.30 * usable, usable);
    run_pool(poolB, nB, t0 + 0.55 * usable, usable);
    run_pool(poolC, nC, t_end, usable);

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
            ref = REF_VERTICES.get((d, D), max(2 * d, lib.moore_bound(d, D) // 4))
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
