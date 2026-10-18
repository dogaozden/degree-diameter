"""Program: bi-Cayley graphs over finite groups, with a metacyclic group family added.

Construction:
  * Pick a finite group G of order N. Bi-Cayley graph with connection set S = {s_1..s_d}:
    A_x is joined to B_{x s_k} for each k. This is d-regular, bipartite, with 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D iff BFS from A_e and from B_e
    reaches all 2N vertices within D steps.

Changes from the previous version:
  * Groups: besides PSL(2,q) and SL(2,q), the engine tries nonabelian metacyclic groups
    Z_m x|_r Z_k (r^k = 1 mod m, r != 1). Their orders fill the gap between the PSL/SL
    orders, which previously jumped from 4368 to 6840 vertices and could not reach the record.
  * Candidates are ranked by log-distance of 2N from a target 0.28 * Moore bound (about 5500
    for d=4, D=9), so the search starts just above the record order.
  * Search: simulated annealing with a time-based cooling schedule replaces plain hill-climbing.
  * Time: each candidate gets 30% of the remaining budget.

Safety: the C engine always prints a valid graph (K_{d,d} if nothing is found). Python
checks it with lib.is_valid and keeps the best valid graph, falling back to the known
start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over PSL/SL(2,q) and metacyclic groups Z_m x|_r Z_k.
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
#define MAXCAND 96
#define MAXK 40

static int d, D;
static double t_end;
static double target_bi;

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

/* ------------------------------------------------------------------ groups */
/* gtype 0: PSL/SL(2,q) as 2x2 matrices over GF(q) (q prime).
 * gtype 1: metacyclic Z_m x|_r Z_k, element (a,b) coded as a*k+b,
 *          (a,b)(c,d) = (a + r^b c, b + d).                               */

static int gtype = 0;
static int N = 0, e_id = 0;

static int q = 0, isPSL = 0;
static int gm[MAXG][4];
static int *idx = NULL;
static int idx_cap = 0;

static int mm = 1, mk = 1, mr = 1;
static int mpow[MAXK];

static int canon_key(int a, int b, int c, int e) {
    int k = ((a * q + b) * q + c) * q + e;
    if (!isPSL) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int lookup(int a, int b, int c, int e) { return idx[canon_key(a, b, c, e)]; }

static int build_matrix_group(int qq, int psl) {
    gtype = 0;
    q = qq;
    isPSL = psl;
    int ks = q * q * q * q;
    if (ks > idx_cap) {
        free(idx);
        idx = malloc(sizeof(int) * (size_t)ks);
        if (!idx) { idx_cap = 0; N = 0; return 0; }
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

static int build_meta_group(int m, int k, int r) {
    if (m < 2 || k < 2 || k > MAXK || (long)m * k > MAXG) return 0;
    gtype = 1;
    mm = m; mk = k; mr = r;
    mpow[0] = 1 % m;
    for (int b = 1; b < k; b++) mpow[b] = (mpow[b - 1] * r) % m;
    N = m * k;
    e_id = 0;
    return N;
}

static int gmul(int x, int y) {
    if (gtype == 0) {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        int sa = gm[y][0], sb = gm[y][1], sc = gm[y][2], se = gm[y][3];
        return lookup((a * sa + b * sc) % q, (a * sb + b * se) % q,
                      (c * sa + e * sc) % q, (c * sb + e * se) % q);
    }
    int a = x / mk, b = x % mk, c = y / mk, dd = y % mk;
    int aa = (a + mpow[b] * c) % mm;
    int bb = (b + dd) % mk;
    return aa * mk + bb;
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        return lookup(e, (q - b) % q, (q - c) % q, a);
    }
    int a = x / mk, b = x % mk;
    int nb = (mk - b) % mk;
    int ai = (mm - (mpow[nb] * a) % mm) % mm;
    return ai * mk + nb;
}

/* ------------------------------------------------------------------ connection set */

static int S[MAXDEG];
static int Rr[MAXDEG][MAXG];   /* Rr[k][x] = x * s_k */
static int Ri[MAXDEG][MAXG];   /* Ri[k][y] = y * s_k^{-1} */

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

/* Simulated annealing over the connection set. Returns 1 with S valid, 0 on timeout. */
static int anneal(double until) {
    double t_start = now();
    double span = until - t_start;
    if (span <= 0) return 0;
    randomize_S();
    long cur = cost_now();
    double T = 3.0;
    long it = 0;
    while (cur > 0) {
        if ((++it & 15) == 0) {
            double tn = now();
            if (tn > until) return 0;
            double f = (tn - t_start) / span;
            if (f > 1.0) f = 1.0;
            T = 3.0 * pow(0.1 / 3.0, f);
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
        } else {
            S[k] = old;
            set_col(k);
        }
    }
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct { int type, q, psl, m, k, r, N; double key; } Cand;
static Cand cs[MAXCAND];
static int nc = 0;

static void offer(Cand c) {
    if (nc < MAXCAND) { cs[nc++] = c; return; }
    int w = 0;
    for (int i = 1; i < nc; i++)
        if (cs[i].key > cs[w].key) w = i;
    if (c.key < cs[w].key) cs[w] = c;
}

static int cmp_cand(const void *a, const void *b) {
    double x = ((const Cand *)a)->key, y = ((const Cand *)b)->key;
    return (x > y) - (x < y);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void gather(long moore) {
    static const int primes[] = {5, 7, 11, 13, 17, 19, 23};
    for (unsigned pi = 0; pi < sizeof primes / sizeof primes[0]; pi++) {
        for (int psl = 0; psl < 2; psl++) {
            long qq = primes[pi];
            long order = qq * (qq * qq - 1);
            if (psl) order /= 2;
            long bi = 2 * order;
            if (bi > moore || order > MAXG) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.q = (int)qq;
            c.psl = psl;
            c.N = (int)order;
            c.key = fabs(log((double)bi) - log(target_bi));
            offer(c);
        }
    }

    /* Metacyclic groups: N = m*k in a window around half the target order. */
    long Nt = (long)(target_bi / 2.0);
    if (Nt < 50) Nt = 50;
    long nlo = Nt / 2;
    long nhi = 2 * Nt;
    if (nhi > MAXG) nhi = MAXG;
    if (nhi > moore / 2) nhi = moore / 2;
    for (int k = 2; k <= MAXK; k++) {
        long mlo = (nlo + k - 1) / k;
        if (mlo < 3) mlo = 3;
        long mhi = nhi / k;
        for (long m = mlo; m <= mhi; m++) {
            long Nn = m * k;
            if (Nn > MAXG || 2 * Nn > moore) continue;
            double key = fabs(log(2.0 * (double)Nn) - log(target_bi));
            for (long r = 2; r < m; r++) {
                long pw = 1 % m;
                for (int i = 0; i < k; i++) pw = (pw * r) % m;
                if (pw != 1 % m) continue;
                if (gcd_i((int)r, (int)m) != 1) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.m = (int)m;
                c.k = k;
                c.r = (int)r;
                c.N = (int)Nn;
                c.key = key;
                offer(c);
            }
        }
    }
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
    double t0 = now();
    t_end = t0 + limit * 0.8;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    target_bi = 0.28 * (double)moore;
    if (target_bi < 8.0) target_bi = 8.0;

    nc = 0;
    gather(moore);
    qsort(cs, (size_t)nc, sizeof(Cand), cmp_cand);

    long best_n = 2L * d;
    static int bS[MAXDEG];
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);
    int have = 0;

    for (int c = 0; c < nc; c++) {
        if (2L * cs[c].N <= best_n) continue;
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        double until = now() + remaining * 0.3;
        int ok;
        if (cs[c].type == 0) ok = build_matrix_group(cs[c].q, cs[c].psl);
        else ok = build_meta_group(cs[c].m, cs[c].k, cs[c].r);
        if (!ok) continue;
        if (anneal(until)) {
            best_n = 2L * N;
            bestc = cs[c];
            have = 1;
            memcpy(bS, S, sizeof(int) * (size_t)d);
        }
    }

    if (!have) {
        print_complete();
        return 0;
    }
    if (bestc.type == 0) build_matrix_group(bestc.q, bestc.psl);
    else build_meta_group(bestc.m, bestc.k, bestc.r);
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
