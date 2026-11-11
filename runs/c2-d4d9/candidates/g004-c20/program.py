"""Program: bi-Cayley graphs over a mixed family of groups (new construction).

Previous engine: bi-Cayley graphs over PSL(2,q)/SL(2,q) only.

This version widens the family to metacyclic groups Z_m x|_r Z_k (r^k = 1 mod m,
gcd(r,m) = 1, including cyclic and abelian cases r = 1) as well as the matrix groups.

Construction (unchanged in principle):
  * Group G with |G| = N, connection set S = {s_1..s_d}.
  * Bi-Cayley graph: A_x ~ B_{x s_k}. d-regular, bipartite, 2N vertices.
  * Left multiplication is an automorphism, so diameter <= D iff BFS from A_e and
    from B_e reaches all 2N vertices within D steps.

Search: candidate groups are sorted by closeness of N to a target order and tried
in turn. Each gets a share of the remaining time for a simulated-annealing search
over S. After a success, only larger groups are tried. The C engine always prints a
valid graph (K_{d,d} if nothing is found). Python checks the output with lib.is_valid,
keeps the best valid graph, and falls back to the known start or K_{d,d}.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over matrix groups PSL/SL(2,q) and metacyclic groups
 * Z_m x|_r Z_k.  Usage: prog d D seed time_limit   (stdin ignored)
 * Output: "n m" then m lines "u v": bipartite, degree d, diameter <= D.
 * Vertices: A_x = x, B_y = N + y.  Edges: A_x -- B_{x*s_k}.
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
#define QMAX 23
#define MIDX (QMAX * QMAX * QMAX * QMAX)
#define MAXCAND 100000

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------------ groups */

static int gtype = 0;          /* 0: matrix group PSL/SL(2,q); 1: Z_m x|_r Z_k */
static int N = 0, e_id = 0;
static int qm = 0, isPSL = 0;
static int gm[MAXG][4];        /* matrix entries a,b,c,e */
static int midx[MIDX];         /* canonical key -> element index */
static int sm = 0, sk = 0;     /* semidirect: element x = a*sk + b */
static int spow[MAXG];        /* spow[b] = r^b mod m */

static int canon_key(int a, int b, int c, int e) {
    int k = ((a * qm + b) * qm + c) * qm + e;
    if (!isPSL) return k;
    int na = (qm - a) % qm, nb = (qm - b) % qm, nc = (qm - c) % qm, ne = (qm - e) % qm;
    int kn = ((na * qm + nb) * qm + nc) * qm + ne;
    return k < kn ? k : kn;
}

static int mat_lookup(int a, int b, int c, int e) { return midx[canon_key(a, b, c, e)]; }

static int build_matrix(int qq, int psl) {
    qm = qq;
    isPSL = psl;
    gtype = 0;
    int ks = qm * qm * qm * qm;
    for (int i = 0; i < ks; i++) midx[i] = -1;
    N = 0;
    for (int a = 0; a < qm; a++)
        for (int b = 0; b < qm; b++)
            for (int c = 0; c < qm; c++)
                for (int e = 0; e < qm; e++) {
                    if ((((a * e - b * c) % qm) + qm) % qm != 1) continue;
                    int own = ((a * qm + b) * qm + c) * qm + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (N >= MAXG) return 0;
                    gm[N][0] = a; gm[N][1] = b; gm[N][2] = c; gm[N][3] = e;
                    midx[own] = N;
                    N++;
                }
    e_id = mat_lookup(1, 0, 0, 1);
    return N;
}

static int build_semi(int m, int k, int r) {
    gtype = 1;
    sm = m;
    sk = k;
    N = m * k;
    e_id = 0;
    spow[0] = 1 % m;
    for (int b = 1; b < k; b++) spow[b] = (int)((long)spow[b - 1] * r % m);
    return N;
}

static int gmul(int x, int y) {
    if (gtype == 0) {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        int f = gm[y][0], g = gm[y][1], h = gm[y][2], i = gm[y][3];
        return mat_lookup((a * f + b * h) % qm, (a * g + b * i) % qm,
                          (c * f + e * h) % qm, (c * g + e * i) % qm);
    }
    int a = x / sk, b = x % sk, c = y / sk, dd = y % sk;
    int na = (int)(((long)a + (long)spow[b] * c) % sm);
    int nb = (b + dd) % sk;
    return na * sk + nb;
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = gm[x][0], b = gm[x][1], c = gm[x][2], e = gm[x][3];
        return mat_lookup(e, (qm - b) % qm, (qm - c) % qm, a);
    }
    int a = x / sk, b = x % sk;
    int nb = (sk - b) % sk;
    int na = (int)(((long)sm - ((long)spow[nb] * a) % sm) % sm);
    return na * sk + nb;
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

/* Pairs not covered within D from A_e and B_e; zero means diameter <= D. */
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

/* Simulated annealing over S. Returns 1 when cost 0 is reached, 0 at the deadline. */
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

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;      /* 0 matrix, 1 semidirect */
    int q, psl;    /* matrix parameters */
    int m, k, r;   /* semidirect parameters */
    int N;
    double key;
} Cand;

static Cand cand[MAXCAND];
static int ncand = 0;

static int cmp_key(const void *a, const void *b) {
    double x = ((const Cand *)a)->key, y = ((const Cand *)b)->key;
    return (x > y) - (x < y);
}

static void add_cand(int type, int q, int psl, int m, int k, int r, int n, double tN) {
    if (ncand >= MAXCAND) return;
    Cand *c = &cand[ncand++];
    c->type = type;
    c->q = q;
    c->psl = psl;
    c->m = m;
    c->k = k;
    c->r = r;
    c->N = n;
    /* Small random jitter in log-space gives diversity among equal orders. */
    c->key = fabs(log((double)n) - log(tN)) + 0.02 * rnd01();
}

static int build_cand(const Cand *c) {
    int n;
    if (c->type == 0) n = build_matrix(c->q, c->psl);
    else n = build_semi(c->m, c->k, c->r);
    if (n != c->N) return 0;
    if (n <= d) return 0;
    return 1;
}

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
    t_end = t0 + limit * 0.85;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long tNl = 2600;
    if (moore / 4 < tNl) tNl = moore / 4;
    if (tNl < 2) tNl = 2;
    double tN = (double)tNl;

    int lo = (int)(0.7 * tN);
    if (lo < 2) lo = 2;
    long hiL = (long)(1.6 * tN);
    if (hiL > moore / 2) hiL = moore / 2;
    if (hiL > MAXG) hiL = MAXG;
    int hi = (int)hiL;

    /* Matrix-group candidates: PSL/SL(2,q), q prime. */
    static const int primes[] = {5, 7, 11, 13, 17, 19, 23};
    for (unsigned pi = 0; pi < sizeof primes / sizeof primes[0]; pi++) {
        for (int psl = 0; psl < 2; psl++) {
            long qq = primes[pi];
            long order = qq * (qq * qq - 1);
            if (psl) order /= 2;
            if (2 * order > moore || order > MAXG || order <= d) continue;
            add_cand(0, (int)qq, psl, 0, 0, 0, (int)order, tN);
        }
    }

    /* Metacyclic candidates Z_m x|_r Z_k with N = m*k in [lo, hi]. */
    for (int k = 1; k <= hi; k++) {
        int mlo = (lo + k - 1) / k;
        if (mlo < 2) mlo = 2;
        int mhi = hi / k;
        for (int m = mlo; m <= mhi; m++) {
            int n = m * k;
            if (n > hi || n <= d) continue;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_i(r, k, m) != 1 % m) continue;
                add_cand(1, 0, 0, m, k, r, n, tN);
            }
        }
    }

    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_key);

    long best_v = 2L * d;
    int have = 0;
    Cand bc;
    static int bS[MAXDEG];
    for (int c = 0; c < ncand; c++) {
        if (2L * cand[c].N <= best_v) continue;
        double remaining = t_end - now();
        if (remaining < 0.3) break;
        double share = remaining * 0.12;
        if (share < 0.8) share = remaining;
        if (!build_cand(&cand[c])) continue;
        if (climb(now() + share)) {
            best_v = 2L * N;
            bc = cand[c];
            memcpy(bS, S, sizeof(int) * (size_t)d);
            have = 1;
        }
    }

    if (!have) {
        print_complete();
        return 0;
    }
    build_cand(&bc);
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
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 15)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
