"""Program: bi-Cayley graphs over PSL(2,q) / SL(2,q), replacing the earlier voltage-lift search.

New construction (replaces the metacyclic voltage lifts):
  * Take a finite group G = PSL(2,q) or SL(2,q) for a prime q, with |G| = N.
  * Bi-Cayley graph with connection set S = {s_1..s_d} (distinct elements of G):
    vertex A_x is joined to B_{x s_k} for each k. This is d-regular and bipartite,
    with 2N vertices.
  * Left multiplication by any h in G is an automorphism that maps A_x -> A_{hx} and
    B_y -> B_{hy}. So diameter <= D iff BFS from A_e and from B_e reaches all 2N
    vertices within D steps. That is two BFS runs per evaluation.
  * Groups are tried in order of closeness to a target order (about 6840 vertices, above
    the record 4970). Each is searched by hill-climbing over the connection set.
    Once a group succeeds, larger groups are still tried.

Safety: the C engine always prints a valid graph (K_{d,d} if nothing is found). Python
checks it with lib.is_valid and keeps the best valid graph, falling back to the known
start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over PSL(2,q) / SL(2,q), q prime.
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * Output: "n m" then m lines "u v": a bipartite graph, every degree d, diameter <= D
 *         (K_{d,d} if nothing better was found).
 *
 * Vertices: A_x = x, B_y = N + y, for group elements x, y in 0..N-1.
 * Edges: A_x -- B_{x*s_k} for k < d.
 */
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

/* ------------------------------------------------------------------ group */

static int q, isPSL, N, e_id;
static int gm[MAXG][4];   /* matrix entries a,b,c,e of element x = [[a,b],[c,e]] */
static int *idx = NULL;   /* key -> element index */
static int idx_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int k = ((a * q + b) * q + c) * q + e;
    if (!isPSL) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int lookup(int a, int b, int c, int e) { return idx[canon_key(a, b, c, e)]; }

static int build_group(int qq, int psl) {
    q = qq;
    isPSL = psl;
    int ks = q * q * q * q;
    if (ks > idx_cap) {
        free(idx);
        idx = malloc(sizeof(int) * (size_t)ks);
        idx_cap = ks;
    }
    for (int i = 0; i < ks; i++) idx[i] = -1;
    N = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (N >= MAXG) return 0;
                    gm[N][0] = a; gm[N][1] = b; gm[N][2] = c; gm[N][3] = e;
                    idx[own] = N;
                    N++;
                }
    e_id = lookup(1, 0, 0, 1);
    return N;
}

static int inv_index(int s) {
    return lookup(gm[s][3], (q - gm[s][1]) % q, (q - gm[s][2]) % q, gm[s][0]);
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXG];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXG];   /* Ri[k][y] = y * s_k^{-1} */

static void set_col(int k) {
    int s = S[k], si = inv_index(s);
    int sa = gm[s][0], sb = gm[s][1], sc = gm[s][2], se = gm[s][3];
    int ta = gm[si][0], tb = gm[si][1], tc = gm[si][2], te = gm[si][3];
    for (int x = 0; x < N; x++) {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        Rr[k][x] = lookup((a * sa + b * sc) % q, (a * sb + b * se) % q,
                          (c * sa + e * sc) % q, (c * sb + e * se) % q);
        Ri[k][x] = lookup((a * ta + b * tc) % q, (a * tb + b * te) % q,
                          (c * ta + e * tc) % q, (c * tb + e * te) % q);
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

/* Number of (source, vertex) pairs unreached within D steps; 0 means diameter <= D. */
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

/* Hill-climb over the connection set of the current group. Returns 1 with S valid. */
static int climb(double until) {
    randomize_S();
    long cur = cost_now(), best_c = cur, stall = 0, it = 0;
    while (cur > 0) {
        if ((++it & 31) == 0 && now() > until) return 0;
        if (stall > 3000) {
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
        if (nc <= cur || rnd01() < 0.01) {
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

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

typedef struct { int q, psl; long bi; double key; } Cand;

static int cmp_cand(const void *a, const void *b) {
    double x = ((const Cand *)a)->key, y = ((const Cand *)b)->key;
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
    t_end = t0 + limit * 0.8;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long best_n = 2L * d;
    int bq = 0, bpsl = 0, bN = 0;

    static const int primes[] = {5, 7, 11, 13, 17, 19, 23};
    static Cand cs[32];
    int nc = 0;
    for (unsigned pi = 0; pi < sizeof primes / sizeof primes[0]; pi++) {
        for (int psl = 0; psl < 2; psl++) {
            long qq = primes[pi];
            long order = qq * (qq * qq - 1);
            if (psl) order /= 2;
            long bi = 2 * order;
            if (bi > moore || order > MAXG || nc >= 32) continue;
            cs[nc].q = (int)qq;
            cs[nc].psl = psl;
            cs[nc].bi = bi;
            cs[nc].key = fabs(log((double)bi) - log(6840.0));
            nc++;
        }
    }
    qsort(cs, (size_t)nc, sizeof(Cand), cmp_cand);

    static int bS[MAXDEG];
    for (int c = 0; c < nc; c++) {
        if (cs[c].bi <= best_n) continue;
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        double until = now() + remaining * 0.4;
        if (build_group(cs[c].q, cs[c].psl) == 0) continue;
        if (climb(until)) {
            best_n = 2L * N;
            bq = cs[c].q;
            bpsl = cs[c].psl;
            bN = N;
            memcpy(bS, S, sizeof(int) * (size_t)d);
        }
    }

    if (bN == 0) {
        print_complete();
        return 0;
    }
    build_group(bq, bpsl);
    memcpy(S, bS, sizeof(int) * (size_t)d);
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
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
