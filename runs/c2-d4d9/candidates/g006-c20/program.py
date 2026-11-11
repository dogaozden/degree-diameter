"""Program: multi-fibre voltage lifts over metacyclic groups (new construction).

Construction:
  * Base graph with 2b vertices: fibres A_0..A_{b-1} and B_0..B_{b-1}, with b in 1..6.
    Dart k (k < d) joins A_i to B_{sig_k(i)}, where sig_k is a permutation of [b].
  * Voltages: dart k from fibre i carries group element g_{k,i} of G = Z_m x| Z_k.
    The lift has vertices (X, x), X in 2b base vertices and x in G, with
    (A_i, x) ~ (B_{sig_k(i)}, x*g_{k,i}) for each k. It is d-regular, bipartite,
    and has 2bN vertices, where N = |G|.
  * Left multiplication by any h in G is an automorphism, so the diameter is <= D iff
    BFS from (X, e) reaches all 2bN vertices within D steps, for each of the 2b base X.
  * Search: hill climbing over voltages and fibre permutations, with cost equal to the
    total number of unreached (base, vertex) pairs at depth D. Candidates (b, G) are
    chosen so that 2bN is close to the reference vertex count. They are scheduled in
    iterative-deepening rounds, and candidates that cannot beat the current best are skipped.
  * Duplicate edges created by a voltage pattern are removed at output time. This does not
    change distances, so the BFS cost stays exact.

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

#define MAXN 3200
#define MAXB 6
#define MAXDEG 8
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 40
#define PERB 6
#define STALL 2000
#define TMPMAX 32768

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

static long powmod_l(long bb, long e, long m) {
    long r = 1 % m;
    bb %= m;
    while (e > 0) {
        if (e & 1) r = r * bb % m;
        bb = bb * bb % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------------ group */
/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */

static int GM, GK, GN;
static int PW[MAXN];
static int GA[MAXN], GB[MAXN];

static int gmul(int x, int y) {
    int a = GA[x], b = GB[x], c = GA[y], e = GB[y];
    int aa = (a + PW[b] * c) % GM;
    int bb = b + e;
    if (bb >= GK) bb -= GK;
    return aa * GK + bb;
}

static int setup_group(int m, int k, int r) {
    if (m < 2 || k < 1 || m * k > MAXN) return 0;
    GM = m;
    GK = k;
    GN = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
    for (int x = 0; x < GN; x++) { GA[x] = x / k; GB[x] = x % k; }
    return 1;
}

/* ------------------------------------------------------------------ state */

static int NF;                       /* fibres per side */
static int SIG[MAXDEG][MAXB];        /* SIG[k][i] = j : A_i -> B_j via dart k */
static int G[MAXDEG][MAXB];          /* voltage of dart k from fibre i */
static int NB[MAXV * MAXDEG];        /* NB[v*d+k] = neighbour of v via dart k */
static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

/* Vertex ids: A_i, element x -> i*GN + x ; B_j, element y -> (NF + j)*GN + y. */
static void refresh_nb(void) {
    int N = GN, nf = NF;
    for (int k = 0; k < d; k++)
        for (int i = 0; i < nf; i++) {
            int j = SIG[k][i], g = G[k][i];
            for (int x = 0; x < N; x++) {
                int y = gmul(x, g);
                int va = i * N + x;
                int vb = (nf + j) * N + y;
                NB[va * d + k] = vb;
                NB[vb * d + k] = va;
            }
        }
}

/* Darts k2 < k from the same fibre i must not create the same edge. */
static int pair_ok(int k, int i) {
    for (int k2 = 0; k2 < k; k2++)
        if (SIG[k2][i] == SIG[k][i] && G[k2][i] == G[k][i]) return 0;
    return 1;
}

static int ok_fibre(int i) {
    for (int k = 0; k < d; k++)
        if (!pair_ok(k, i)) return 0;
    return 1;
}

static void random_state(void) {
    for (int k = 0; k < d; k++) {
        int p[MAXB];
        for (int i = 0; i < NF; i++) p[i] = i;
        for (int i = NF - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < NF; i++) SIG[k][i] = p[i];
    }
    for (int k = 0; k < d; k++)
        for (int i = 0; i < NF; i++) {
            int tries = 0;
            do {
                G[k][i] = rndint(GN);
            } while (!pair_ok(k, i) && ++tries < 10000);
        }
}

/* ------------------------------------------------------------------ BFS cost */

static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            const int *nb = &NB[qv[head] * d];
            for (int k = 0; k < d; k++) {
                int u = nb[k];
                if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
            }
        }
    }
    return tail;
}

static long cost_now(void) {
    refresh_nb();
    long NV = 2L * NF * GN, c = 0;
    for (int X = 0; X < 2 * NF; X++)
        c += NV - ball(X * GN);   /* (X, identity) */
    return c;
}

/* ------------------------------------------------------------------ search */

static int climb(double until) {
    random_state();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > STALL) {
            random_state();
            cur = cost_now();
            best_c = cur;
            stall = 0;
            continue;
        }
        if (NF >= 2 && rndint(4) == 0) {
            /* swap two fibre targets of one dart */
            int k = rndint(d);
            int i1 = rndint(NF), i2 = rndint(NF - 1);
            if (i2 >= i1) i2++;
            int t = SIG[k][i1]; SIG[k][i1] = SIG[k][i2]; SIG[k][i2] = t;
            if (!ok_fibre(i1) || !ok_fibre(i2)) {
                t = SIG[k][i1]; SIG[k][i1] = SIG[k][i2]; SIG[k][i2] = t;
                stall++;
                continue;
            }
            long nc = cost_now();
            if (nc <= cur || rnd01() < 0.02) {
                cur = nc;
            } else {
                t = SIG[k][i1]; SIG[k][i1] = SIG[k][i2]; SIG[k][i2] = t;
            }
        } else {
            /* change one voltage */
            int k = rndint(d), i = rndint(NF);
            int old = G[k][i];
            G[k][i] = rndint(GN);
            if (!ok_fibre(i)) {
                G[k][i] = old;
                stall++;
                continue;
            }
            long nc = cost_now();
            if (nc <= cur || rnd01() < 0.02) cur = nc;
            else G[k][i] = old;
        }
        if (cur < best_c) { best_c = cur; stall = 0; }
        else stall++;
    }
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int b, m, k, r, N;
    long T;
    long key;
} Cand;

static Cand cand[MAXCAND];
static int ncand = 0;
static Cand tmp[TMPMAX];
static int ntmp = 0;

static int cmp_key(const void *a, const void *b) {
    long x = ((const Cand *)a)->key, y = ((const Cand *)b)->key;
    return (x > y) - (x < y);
}

static void add_tmp(int b, int m, int k, int r, long ref) {
    if (ntmp >= TMPMAX) return;
    Cand c;
    c.b = b;
    c.m = m;
    c.k = k;
    c.r = r;
    c.N = m * k;
    c.T = 2L * b * c.N;
    long dist = labs(c.T - ref);
    c.key = dist * 100000L + c.T;
    tmp[ntmp++] = c;
}

static void gen_candidates(long ref, long moore) {
    long lo = (long)(0.93 * (double)ref), hi = (long)(1.12 * (double)ref);
    if (hi > moore) hi = moore;
    if (lo < 4) lo = 4;
    ncand = 0;
    for (int b = 1; b <= MAXB; b++) {
        ntmp = 0;
        long Nlo = (lo + 2L * b - 1) / (2L * b);
        long Nhi = hi / (2L * b);
        if (Nhi > MAXN) Nhi = MAXN;
        for (long N = Nlo; N <= Nhi; N++) {
            if (N < 4) continue;
            for (long k = 1; k <= N / 2; k++) {
                if (N % k) continue;
                long m = N / k;
                if (m < 2) continue;
                if (k == 1) { add_tmp(b, (int)m, 1, 1, ref); continue; }
                int got = 0;
                for (long r = 1; r < m && got < 3; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1 % m) continue;
                    add_tmp(b, (int)m, (int)k, (int)r, ref);
                    got++;
                }
            }
        }
        qsort(tmp, (size_t)ntmp, sizeof(Cand), cmp_key);
        for (int i = 0; i < ntmp && i < PERB && ncand < MAXCAND; i++)
            cand[ncand++] = tmp[i];
    }
    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_key);
}

/* ------------------------------------------------------------------ output */

static int EU[MAXV * MAXDEG], EV[MAXV * MAXDEG];

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    int ne = 0;
    int NA = NF * GN;
    for (int v = 0; v < NA; v++)
        for (int k = 0; k < d; k++) {
            int u = NB[v * d + k];
            int dup = 0;
            for (int k2 = 0; k2 < k; k2++)
                if (NB[v * d + k2] == u) { dup = 1; break; }
            if (!dup) { EU[ne] = v; EV[ne] = u; ne++; }
        }
    printf("%d %d\n", 2 * NF * GN, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", EU[e], EV[e]);
}

/* ------------------------------------------------------------------ main */

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
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    if (ref <= 0) ref = moore / 4;
    if (ref < 4) ref = 4;

    gen_candidates(ref, moore);

    long bestT = 2L * d;
    int have = 0, bi = -1;
    static int bSIG[MAXDEG][MAXB], bG[MAXDEG][MAXB];

    double budget0 = t_end - now();
    double base = budget0 / (2.0 * (ncand > 0 ? ncand : 1));
    if (base < 0.15) base = 0.15;

    for (int round = 0; round < 10; round++) {
        for (int i = 0; i < ncand; i++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            Cand *c = &cand[i];
            if (c->T <= bestT) continue;
            if (c->T > moore) continue;
            if (!setup_group(c->m, c->k, c->r)) continue;
            NF = c->b;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                have = 1;
                bestT = c->T;
                bi = i;
                memcpy(bSIG, SIG, sizeof SIG);
                memcpy(bG, G, sizeof G);
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    Cand *c = &cand[bi];
    if (!setup_group(c->m, c->k, c->r)) { print_complete(); return 0; }
    NF = c->b;
    memcpy(SIG, bSIG, sizeof SIG);
    memcpy(G, bG, sizeof G);
    if (cost_now() != 0) { print_complete(); return 0; }
    print_graph();
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
        return best   # Moore graph already; nothing to search for

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0:
        ref = REF_VERTICES.get((d, D), max(2 * d, moore // 4))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
