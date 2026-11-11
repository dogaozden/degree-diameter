"""Program: bold switch to voltage lifts over small base graphs.

Construction (new family, replacing the bi-Cayley-only search):
  * Base graph: nb vertices per side (nb = 1..4). Each of the d "matchings" t is a
    permutation sig_t of {0..nb-1} with a voltage g_t in a metacyclic group G = Z_m x| Z_k
    of order N. Lift: A_{i,x} ~ B_{sig_t(i), x*g_t} for every t. Vertices: 2*nb*N, degree d,
    bipartite by construction.
  * Left multiplication is an automorphism, so the diameter is <= D iff BFS from each of the
    2*nb representatives A_{i,e}, B_{j,e} reaches all vertices within D steps.
  * nb = 1 is exactly the bi-Cayley family of the parent, so the search still covers it.

Search:
  * Candidate (nb, group) pairs with vertex counts just above the record, plus a few
    just below it as fallbacks, ordered by vertex count.
  * Simulated annealing over permutations and voltages, with the cost = total unreached
    (source, vertex) pairs within distance D. State is kept between time slices, and the
    slice length doubles each round (iterative deepening).
  * Only lifts with no repeated edges are accepted (compat check), and the best valid lift
    found is printed.

Safety: Python re-checks the output with lib.is_valid and keeps the best valid graph,
falling back to the known start or K_{d,d}.
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
#define MAXB 4
#define MAXD 8
#define MAXVV (2 * MAXB * MAXN)
#define MAXCAND 80

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

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

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int N = 0, e_id = 0, cap_N = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;
static int pw[MAXN], yc[MAXN], yd[MAXN];

/* (a,b)(c,d) = (a + r^b c, b + d), element (a,b) coded as a*k+b. */
static int build_meta(int m, int k, int r) {
    int n = m * k;
    if (n > MAXN || n < 2) return 0;
    if (n > cap_N) {
        free(T);
        free(INV);
        T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
        INV = malloc(sizeof(int) * (size_t)n);
        if (!T || !INV) exit(1);
        cap_N = n;
    }
    N = n;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int y = 0; y < N; y++) { yc[y] = y / k; yd[y] = y % k; }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        long pb = pw[b];
        uint16_t *row = T + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int aa = (int)((a + pb * yc[y]) % m);
            int bb = (b + yd[y]) % k;
            int z = aa * k + bb;
            row[y] = (uint16_t)z;
            if (z == 0) INV[x] = y;
        }
    }
    e_id = 0;
    return 1;
}

/* ------------------------------------------------------------ candidates */

typedef struct {
    int b, m, k, r, N, V;
    int started;
    int sig[MAXD][MAXB];
    int gel[MAXD];
} Cand;

static Cand cands[MAXCAND];
static int ncand = 0;

static void add_cands_for_V(long V, int cap) {
    for (int b = 1; b <= MAXB; b++) {
        if (V % (2 * b)) continue;
        long Nv = V / (2 * b);
        if (Nv < 2 || Nv > MAXN) continue;
        int got = 0;
        for (long k = 1; k <= Nv && got < 3 && ncand < cap; k++) {
            if (Nv % k) continue;
            long m = Nv / k;
            if (m < 2) continue;
            for (long r = 1; r < m && got < 3 && ncand < cap; r++) {
                if (k > 1 && r == 1) continue;   /* skip abelian direct product */
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1 % m) continue;
                Cand *c = &cands[ncand++];
                memset(c, 0, sizeof *c);
                c->b = b;
                c->m = (int)m;
                c->k = (int)k;
                c->r = (int)r;
                c->N = (int)Nv;
                c->V = (int)V;
                got++;
            }
        }
    }
}

/* ------------------------------------------------------------ lift state */

static int nb = 1;
static int sig[MAXD][MAXB], isig[MAXD][MAXB];
static int gel[MAXD], gin[MAXD];

static void set_isig(int t) {
    for (int i = 0; i < nb; i++) isig[t][sig[t][i]] = i;
}

/* Two darts at the same A vertex must not reach the same B vertex: the same voltage
   with the same permutation value at some i is forbidden. */
static int compat_t(int t) {
    for (int tp = 0; tp < d; tp++) {
        if (tp == t || gel[tp] < 0) continue;
        if (gel[tp] != gel[t]) continue;
        for (int i = 0; i < nb; i++)
            if (sig[tp][i] == sig[t][i]) return 0;
    }
    return 1;
}

static int compat_all(void) {
    for (int t = 0; t < d; t++)
        if (!compat_t(t)) return 0;
    return 1;
}

static int stamp[MAXVV];
static int tick = 0;
static int qv[MAXVV];

/* Number of vertices reached from src within D steps. */
static int reach(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int half = nb * N;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < half) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int u = half + sig[t][i] * N + T[(size_t)x * N + gel[t]];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int u = isig[t][j] * N + T[(size_t)y * N + gin[t]];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Total number of unreached (source, vertex) pairs over all 2*nb representatives. */
static long cost_now(void) {
    long V = 2L * nb * N;
    long c = 0;
    for (int i = 0; i < nb; i++) c += V - reach(i * N + e_id);
    for (int j = 0; j < nb; j++) c += V - reach(nb * N + j * N + e_id);
    return c;
}

static void store_cand(Cand *c) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < nb; i++) c->sig[t][i] = sig[t][i];
        c->gel[t] = gel[t];
    }
}

static void load_cand(const Cand *c) {
    nb = c->b;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < nb; i++) sig[t][i] = c->sig[t][i];
        set_isig(t);
        gel[t] = c->gel[t];
        gin[t] = INV[gel[t]];
    }
}

static void init_cand(Cand *c) {
    nb = c->b;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < nb; i++) sig[t][i] = i;
        for (int i = nb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sig[t][i]; sig[t][i] = sig[t][j]; sig[t][j] = tmp;
        }
        set_isig(t);
        gel[t] = -1;
        gin[t] = -1;
    }
    for (int t = 0; t < d; t++) {
        int tries = 0;
        do {
            gel[t] = rndint(N);
            gin[t] = INV[gel[t]];
            tries++;
        } while (!compat_t(t) && tries < 100000);
    }
    store_cand(c);
}

/* Simulated annealing on one candidate until `until`. Returns 1 if a valid lift was found
   (the state stored in c is then that lift). */
static int run_slice(Cand *c, double until) {
    load_cand(c);
    long cur = cost_now();
    double start = now();
    double span = until - start;
    if (span <= 0.0 && cur != 0) { store_cand(c); return 0; }
    if (span < 1e-9) span = 1e-9;
    double temp = T_HI;
    long it = 0;
    while (cur != 0) {
        if ((++it & 7) == 0) {
            double tt = now();
            if (tt >= until) break;
            double f = (tt - start) / span;
            double ph = f * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int t = rndint(d);
        if (nb > 1 && rnd01() < 0.5) {
            int i = rndint(nb), ip = rndint(nb - 1);
            if (ip >= i) ip++;
            int tmp = sig[t][i]; sig[t][i] = sig[t][ip]; sig[t][ip] = tmp;
            set_isig(t);
            if (!compat_t(t)) {
                tmp = sig[t][i]; sig[t][i] = sig[t][ip]; sig[t][ip] = tmp;
                set_isig(t);
                continue;
            }
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                tmp = sig[t][i]; sig[t][i] = sig[t][ip]; sig[t][ip] = tmp;
                set_isig(t);
            }
        } else {
            int old = gel[t], oldin = gin[t];
            int x = rndint(N);
            if (x == old) continue;
            gel[t] = x;
            gin[t] = INV[x];
            if (!compat_t(t)) {
                gel[t] = old;
                gin[t] = oldin;
                continue;
            }
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                gel[t] = old;
                gin[t] = oldin;
            }
        }
    }
    store_cand(c);
    if (cur == 0 && compat_all()) return 1;
    return 0;
}

/* ------------------------------------------------------------ output */

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
    long refV = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2 || refV <= 0) { print_complete(); return 0; }

    long moore = moore_bound();

    /* Target: even vertex counts just above the record, ascending. */
    long vt_lo = (refV / 2 + 1) * 2;
    long vt_hi = refV + refV / 60;
    for (long V = vt_lo; V <= vt_hi && ncand < 48; V += 2)
        if (V <= moore && V <= 2L * MAXB * MAXN) add_cands_for_V(V, 48);

    /* Fallback: valid lifts just below the record, descending. */
    long vf_hi = (refV / 2) * 2 - 2;
    long vf_lo = refV - refV / 20;
    for (long V = vf_hi; V >= vf_lo && ncand < 60; V -= 2)
        if (V <= moore && V > 0 && V <= 2L * MAXB * MAXN) add_cands_for_V(V, 60);

    if (ncand == 0) { print_complete(); return 0; }

    double budget0 = t_end - now();
    double base = budget0 / (4.0 * (double)ncand);
    if (base < 0.05) base = 0.05;

    int bestIdx = -1;
    long bestV = 0;
    int stop = 0;
    for (int round = 0; round < 40 && !stop; round++) {
        for (int i = 0; i < ncand && !stop; i++) {
            Cand *c = &cands[i];
            if (c->V <= bestV) continue;
            double remaining = t_end - now();
            if (remaining < 0.1) { stop = 1; break; }
            double slice = base * (double)(1L << (round < 16 ? round : 16));
            if (slice > remaining) slice = remaining;
            if (!build_meta(c->m, c->k, c->r)) continue;
            if (!c->started) { init_cand(c); c->started = 1; }
            if (run_slice(c, now() + slice)) {
                bestV = c->V;
                bestIdx = i;
            }
        }
    }

    if (bestIdx < 0) { print_complete(); return 0; }
    Cand *c = &cands[bestIdx];
    if (!build_meta(c->m, c->k, c->r)) { print_complete(); return 0; }
    load_cand(c);
    if (cost_now() != 0 || !compat_all()) { print_complete(); return 0; }

    long V = 2L * nb * N;
    printf("%ld %ld\n", V, (long)d * nb * N);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < nb; i++)
            for (int x = 0; x < N; x++) {
                int u = i * N + x;
                int v = nb * N + sig[t][i] * N + T[(size_t)x * N + gel[t]];
                printf("%d %d\n", u, v);
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

    ref = REF_VERTICES.get((d, D), 0)
    if ref <= 0 or d > 8 or D < 2:
        return best

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 3.0
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
