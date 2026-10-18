"""Program: bi-Cayley search over metacyclic groups Z_p x| Z_k as well as PSL(2,q) / SL(2,q).

New idea in this version (not in the parent):
  * Metacyclic (Frobenius-type) groups G = Z_m x| Z_k, with m prime, k | m-1, k >= 2 and r of
    multiplicative order exactly k mod m. Elements are (a, b) coded as a*k + b, with
    (a, b)(c, f) = (a + r^b c, b + f). These groups are non-abelian and have orders in a
    range that covers the record factorisation (for example 2485 = 71 * 35 = Z_71 x| Z_35).
  * Both families use one group interface, gmul/ginv. The bi-Cayley engine (vertices A_x,
    B_y; A_x ~ B_{x s_k}) and its diameter cost (two BFS runs from A_e and B_e) do not depend
    on the group, so they are shared.
  * Candidate groups are ranked by closeness of 2N to a target of 5200, just above the record
    4970. Each group gets a chunk of the remaining time, and once a group succeeds, only
    groups with larger order are tried.

Safety: the C engine always prints a valid graph (K_{d,d} if nothing is found). Python
checks the output with lib.is_valid and keeps the best valid graph, falling back to the
known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over metacyclic groups Z_m x| Z_k (m prime) and PSL/SL(2,q), q prime.
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * Output: "n m" then m lines "u v": bipartite, all degrees d, diameter <= D
 *         (K_{d,d} if nothing better was found).
 *
 * Vertices: A_x = x, B_y = N + y for group elements x, y in 0..N-1 (identity = 0 for metacyclic).
 * Edges:    A_x -- B_{x * s_k} for k < d.
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
#define MAXCAND 4096
#define MINN 2000
#define MAXN 4000
#define TARGET_N 2600.0

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

/* ------------------------------------------------------------------ group interface */

static int kind;             /* 0 = metacyclic Z_m x| Z_k, 1 = PSL/SL(2,q) */
static int N, e_id;
static int gm_m, gm_k;
static int pw[MAXG];         /* pw[b] = r^b mod m */
static int q, isPSL;
static int gm[MAXG][4];      /* matrix entries a,b,c,e of element x */
static int *idx = NULL;
static int idx_cap = 0;

static int canon_key(int a, int b, int c, int e) {
    int k = ((a * q + b) * q + c) * q + e;
    if (!isPSL) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int lookup(int a, int b, int c, int e) { return idx[canon_key(a, b, c, e)]; }

static int build_matrix(int qq, int psl) {
    kind = 1;
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

static void build_meta(int m, int k, int r) {
    kind = 0;
    gm_m = m;
    gm_k = k;
    N = m * k;
    e_id = 0;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

/* Group product x*y. */
static int gmul(int x, int y) {
    if (kind == 0) {
        int a = x / gm_k, b = x % gm_k, c = y / gm_k, f = y % gm_k;
        int nb = b + f;
        if (nb >= gm_k) nb -= gm_k;
        int na = (int)(((long)pw[b] * c + a) % gm_m);
        return na * gm_k + nb;
    }
    int p0 = gm[x][0], p1 = gm[x][1], p2 = gm[x][2], p3 = gm[x][3];
    int r0 = gm[y][0], r1 = gm[y][1], r2 = gm[y][2], r3 = gm[y][3];
    return lookup((p0 * r0 + p1 * r2) % q, (p0 * r1 + p1 * r3) % q,
                  (p2 * r0 + p3 * r2) % q, (p2 * r1 + p3 * r3) % q);
}

/* Group inverse of x. */
static int ginv(int x) {
    if (kind == 0) {
        int a = x / gm_k, b = x % gm_k;
        int nb = (gm_k - b) % gm_k;          /* inverse of (a,b) is (-r^{-b} a, -b) */
        int na = (int)(((long)pw[nb] * a) % gm_m);
        na = (gm_m - na) % gm_m;
        return na * gm_k + nb;
    }
    return lookup(gm[x][3], (q - gm[x][1]) % q, (q - gm[x][2]) % q, gm[x][0]);
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

/* Pairs of (source, vertex) not reached within D steps; 0 means diameter <= D. */
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

/* ------------------------------------------------------------------ candidates */

typedef struct { int kind, q, psl, m, k, r, n; double key; } Cand;
static Cand cands[MAXCAND];
static int nc = 0;

static int isprime(int x) {
    if (x < 2) return 0;
    for (int i = 2; i * i <= x; i++)
        if (x % i == 0) return 0;
    return 1;
}

/* Element r mod m whose multiplicative order is exactly k (returns -1 if none). */
static int find_r(int m, int k) {
    for (int r = 2; r < m; r++) {
        long x = 1;
        int ord = 0;
        for (int i = 1; i <= k; i++) {
            x = x * r % m;
            if (x == 1) { ord = i; break; }
        }
        if (ord == k) return r;
    }
    return -1;
}

static void add_cand(Cand c) {
    if (nc < MAXCAND) cands[nc++] = c;
}

static int cmp_cand(const void *a, const void *b) {
    double x = ((const Cand *)a)->key, y = ((const Cand *)b)->key;
    return (x > y) - (x < y);
}

static void gen_cands(void) {
    static const int mq[] = {7, 11, 13, 17, 19, 23};
    for (unsigned i = 0; i < sizeof mq / sizeof mq[0]; i++) {
        for (int psl = 0; psl < 2; psl++) {
            long qq = mq[i];
            long ord = qq * (qq * qq - 1);
            if (psl) ord /= 2;
            if (ord < MINN || ord > MAXN) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.kind = 1;
            c.q = (int)qq;
            c.psl = psl;
            c.n = (int)ord;
            add_cand(c);
        }
    }
    for (int m = 5; m <= MAXN / 2; m++) {
        if (!isprime(m)) continue;
        for (int k = 2; k < m && (long)m * k <= MAXN; k++) {
            if ((m - 1) % k) continue;
            if ((long)m * k < MINN) continue;
            int r = find_r(m, k);
            if (r < 0) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.kind = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.n = m * k;
            add_cand(c);
        }
    }
    for (int i = 0; i < nc; i++)
        cands[i].key = fabs(log((double)cands[i].n) - log(TARGET_N));
    qsort(cands, (size_t)nc, sizeof(Cand), cmp_cand);
}

static int set_group(const Cand *c) {
    if (c->kind == 0) build_meta(c->m, c->k, c->r);
    else build_matrix(c->q, c->psl);
    return N;
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long best_n = 2L * d;
    int have = 0;
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);
    static int bestS[MAXDEG];

    gen_cands();
    for (int c = 0; c < nc; c++) {
        if (2L * cands[c].n <= best_n) continue;     /* only strictly larger graphs */
        if (2L * cands[c].n > moore) continue;
        double remaining = t_end - now();
        if (remaining < 0.4) break;
        double chunk = remaining * 0.12;
        if (chunk < 1.0) chunk = 1.0;
        if (chunk > remaining) chunk = remaining;
        set_group(&cands[c]);
        if (climb(now() + chunk)) {
            best_n = 2L * N;
            bestc = cands[c];
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            have = 1;
        }
    }

    if (!have) {
        print_complete();
        return 0;
    }
    set_group(&bestc);
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
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
