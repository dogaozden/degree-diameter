"""Program: multi-orbit group lifts (a base vertices per side), plus metacyclic bi-Cayley search.

Construction (bold variant):
  * Base graph: a vertices per side (a = 1, 2, 3), d-regular bipartite multigraph given by
    d permutations sigma_k of {0..a-1}. Dart (k, i) joins base A_i to base B_{sigma_k(i)}.
  * Group G = Z_m x|_r Z_k (order N, element code a*k+b, cyclic when k = 1). Each dart t has
    a voltage g_t in G. The lift has vertices (A_i, x) and (B_j, y), 2*a*N in total.
    (A_i, x) is joined to (B_j, x*g_t) for every dart t from i to j.
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from the
    2a fibre representatives (A_i, e) and (B_j, e) reaches all vertices within D steps.
  * Voltages within one cell must be distinct (else a multi-edge). Violations are penalised.
  * a = 1 is the parent's bi-Cayley search and keeps the record-finding path.

Scheduling inside the C engine:
  * Phase 1 (about 40% of the time): a = 1 candidates, parent order (descending below the
    record, then ascending). It stops early once the record vertex count is matched.
  * Phase 2 (the rest): a = 2 and a = 3 lifts, plus a = 1 above the record, all with more
    vertices than the current best, sorted by vertex count ascending. Slices double each round.

Safety: the C engine re-checks the final lift and prints K_{d,d} if nothing is valid.
Python checks the output with lib.is_valid and keeps the better of that and the fallback.
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

#define MAXN 4200
#define MAXA 3
#define MAXDEG 8
#define MAXDARTS (MAXA * MAXDEG)
#define MAXV (2 * MAXA * MAXN)
#define MAXL1 4000
#define MAXL2 12000
#define STALL 3000

static int d, D;
static double t_end;
static long moore_g;

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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GR, N;
static int pw[MAXN];

/* element (a,b) coded as a*k+b; (a,b)(c,d) = (a + r^b c, b + d) */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, dd = y % GK;
    int aa = (a + pw[b] * c) % GM;
    int bb = (b + dd) % GK;
    return aa * GK + bb;
}

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; N = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

/* ------------------------------------------------------------ lift state */

static int A, NT, VT, ATOT;
static int P[MAXDEG][MAXA];                 /* P[k][i] = sigma_k(i) */
static int DFROM[MAXDARTS], DTO[MAXDARTS], G[MAXDARTS];
static int FROMD[MAXA][MAXDEG], TOD[MAXA][MAXDEG];
static int R[MAXDARTS][MAXN], RI[MAXDARTS][MAXN];

static void use_group(int a, int m, int k, int r) {
    A = a;
    set_group(m, k, r);
    ATOT = A * N;
    VT = 2 * ATOT;
    NT = A * d;
}

static void random_perms(void) {
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < A; i++) P[k][i] = i;
        for (int i = A - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = P[k][i];
            P[k][i] = P[k][j];
            P[k][j] = tmp;
        }
    }
}

static void rebuild_adj(void) {
    int cf[MAXA], ct[MAXA];
    for (int i = 0; i < A; i++) { cf[i] = 0; ct[i] = 0; }
    for (int k = 0; k < d; k++)
        for (int i = 0; i < A; i++) {
            int t = k * A + i, j = P[k][i];
            DFROM[t] = i;
            DTO[t] = j;
            FROMD[i][cf[i]++] = t;
            TOD[j][ct[j]++] = t;
        }
}

static void set_dart(int t) {
    int g = G[t];
    for (int x = 0; x < N; x++) {
        int y = gmul(x, g);
        R[t][x] = y;
        RI[t][y] = x;
    }
}

/* ------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* number of vertices within distance D of src (vertex ids: A-fibre i*N+x, B-fibre ATOT+j*N+y) */
static int ball(int src) {
    if (++tick == 0x7fffffff) { memset(stamp, 0, sizeof stamp); tick = 1; }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < ATOT) {
                int i = v / N, x = v - i * N;
                for (int q = 0; q < d; q++) {
                    int t = FROMD[i][q];
                    int u = ATOT + DTO[t] * N + R[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - ATOT;
                int j = w / N, y = w - j * N;
                for (int q = 0; q < d; q++) {
                    int t = TOD[j][q];
                    int u = DFROM[t] * N + RI[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* zero iff the lift is a simple d-regular bipartite graph with diameter <= D */
static long eval_cost(void) {
    long c = 0;
    for (int t1 = 0; t1 < NT; t1++)
        for (int t2 = t1 + 1; t2 < NT; t2++)
            if (DFROM[t1] == DFROM[t2] && DTO[t1] == DTO[t2] && G[t1] == G[t2]) c += 50;
    for (int s = 0; s < A; s++) {
        c += VT - ball(s * N);
        c += VT - ball(ATOT + s * N);
    }
    return c;
}

static long reinit(void) {
    random_perms();
    rebuild_adj();
    for (int t = 0; t < NT; t++) {
        G[t] = rndint(N);
        set_dart(t);
    }
    return eval_cost();
}

static int climb(double until) {
    long cur = reinit(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        if (stall > STALL) {
            cur = reinit();
            best_c = cur;
            stall = 0;
            continue;
        }
        int t = rndint(NT);
        int old = G[t];
        int ng = rndint(N);
        if (ng == old) { stall++; continue; }
        G[t] = ng;
        set_dart(t);
        long nc = eval_cost();
        if (nc <= cur || rnd01() < 0.02) {
            cur = nc;
        } else {
            G[t] = old;
            set_dart(t);
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------ best so far */

static int have = 0;
static long bestV = 0;
static int bestA, bestGM, bestGK, bestGR;
static int bestP[MAXDEG][MAXA];
static int bestG[MAXDARTS];

static void save_best(void) {
    have = 1;
    bestV = VT;
    bestA = A; bestGM = GM; bestGK = GK; bestGR = GR;
    memcpy(bestP, P, sizeof P);
    memcpy(bestG, G, sizeof(int) * (size_t)NT);
}

/* ------------------------------------------------------------ candidates */

typedef struct { int a, m, k, r, N; } Cand;
static Cand L1[MAXL1], L2[MAXL2];
static int n1 = 0, n2 = 0;

static void push_cand(Cand *arr, int *cnt, int cap, int a, int m, int k, int r) {
    if (*cnt >= cap) return;
    Cand c;
    c.a = a; c.m = m; c.k = k; c.r = r; c.N = m * k;
    arr[(*cnt)++] = c;
}

/* metacyclic groups of order Nv: cyclic, plus up to two (r) choices per divisor k >= 2 */
static void add_group_cands(Cand *arr, int *cnt, int cap, int a, int Nv) {
    if (Nv < 3) return;
    push_cand(arr, cnt, cap, a, Nv, 1, 1);
    for (int k = 2; k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 1; r < m && got < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            push_cand(arr, cnt, cap, a, m, k, r);
            got++;
        }
    }
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = x, *q = y;
    long vp = 2L * p->a * p->N, vq = 2L * q->a * q->N;
    return (vp > vq) - (vp < vq);
}

static void run_rounds(Cand *arr, int cnt, double end_time, double base, int rounds,
                       long ref, int early) {
    for (int round = 0; round < rounds; round++) {
        int any = 0;
        for (int i = 0; i < cnt; i++) {
            if (early && have && bestV >= ref) return;
            double remaining = end_time - now();
            if (remaining < 0.2) return;
            Cand *c = &arr[i];
            long V = 2L * c->a * c->N;
            if (V <= bestV || V > moore_g) continue;
            any = 1;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            use_group(c->a, c->m, c->k, c->r);
            if (climb(now() + slice)) save_best();
        }
        if (!any) return;
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
    double usable = limit - 1.5;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    moore_g = moore_bound();
    if (ref <= 0) ref = moore_g / 4;

    long mo = moore_g;
    int recHalf = (int)(ref / 2);
    int recN = recHalf + 1;
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > mo) hiN = (int)(mo / 2);
    if (lowN < 3) lowN = 3;

    /* Phase 1: a = 1 (bi-Cayley over metacyclic groups), parent order */
    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_group_cands(L1, &n1, MAXL1, 1, Nv);
    for (int Nv = recN; Nv <= hiN; Nv++) add_group_cands(L1, &n1, MAXL1, 1, Nv);

    double p1_end = t0 + 0.4 * usable;
    double base1 = 0.03 * (p1_end - now());
    if (base1 < 0.2) base1 = 0.2;
    run_rounds(L1, n1, p1_end, base1, 8, ref, 1);

    /* Phase 2: a = 2, a = 3 lifts and a = 1 above the record, ascending in vertices */
    int start2 = (int)(ref / 6);
    if (start2 < 3) start2 = 3;
    for (int Nv = start2; Nv <= MAXN; Nv++) {
        if (4L * Nv > ref && 4L * Nv <= mo) add_group_cands(L2, &n2, MAXL2, 2, Nv);
        if (6L * Nv > ref && 6L * Nv <= mo) add_group_cands(L2, &n2, MAXL2, 3, Nv);
        if (Nv >= recN && Nv <= hiN && 2L * Nv > ref && 2L * Nv <= mo)
            add_group_cands(L2, &n2, MAXL2, 1, Nv);
    }
    qsort(L2, (size_t)n2, sizeof(Cand), cmp_cand);

    double base2 = 0.02 * (t_end - now());
    if (base2 < 0.2) base2 = 0.2;
    run_rounds(L2, n2, t_end, base2, 10, ref, 0);

    if (!have) { print_complete(); return 0; }

    use_group(bestA, bestGM, bestGK, bestGR);
    memcpy(P, bestP, sizeof P);
    memcpy(G, bestG, sizeof(int) * (size_t)NT);
    rebuild_adj();
    for (int t = 0; t < NT; t++) set_dart(t);
    if (eval_cost() != 0) { print_complete(); return 0; }

    printf("%d %d\n", VT, A * N * d);
    for (int i = 0; i < A; i++)
        for (int x = 0; x < N; x++)
            for (int q = 0; q < d; q++) {
                int t = FROMD[i][q];
                printf("%d %d\n", i * N + x, ATOT + DTO[t] * N + R[t][x]);
            }
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
            ref = REF_VERTICES.get((d, D), 0)
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
