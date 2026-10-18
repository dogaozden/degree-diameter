"""Program: lifted-group search for bipartite graphs with diameter <= D.

New construction (not in the parent): voltage lifts over a SMALL base graph with
A vertices per side, A = 1..5.

  * Base: A "A-vertices" and A "B-vertices". Each A_i has d darts. Dart k of A_i goes
    to B_{pi_k(i)} with voltage v_{i,k} in G, where each pi_k is a permutation of
    {0..A-1}. This makes the base d-regular on both sides.
  * Lift over a finite group G of order N: (A_i, x) ~ (B_{pi_k(i)}, x * v_{i,k}).
    The lift has 2*A*N vertices, is bipartite and d-regular. Darts from the same A_i
    to the same B_j need distinct voltages, which keeps the lift simple.
  * Left multiplication by G is an automorphism, so diameter <= D holds iff BFS from
    (A_i, e) and (B_j, e) reaches all 2AN vertices within D steps, for every i and j.
  * Search: simulated annealing over voltages and permutation swaps. The cost is the
    total number of unreached (source, vertex) pairs. Metropolis acceptance is decided
    before the BFS (threshold = cur + floor(-T ln u)), so BFS stops early on rejects.
  * Candidates: all (A, G) with 2*A*N > record. Groups are metacyclic Z_m x| Z_k and
    PSL/SL(2,q). They are sorted by vertex count, so the smallest improvements are
    tried first, and the schedule doubles time slices across rounds.

Safety: the C engine prints K_{d,d} if it finds nothing. Python checks the output with
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

#define MAXN 5600
#define MAXA 5
#define MAXDEG 8
#define MAXV 12000
#define MAXCAND 160
#define POOLMAX 4096
#define BIG (1L << 60)

static int d, D;
static long moore_g;
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

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

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

static int N = 0, e_id = 0;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;     /* INV[x] = x^{-1} */

static void alloc_group(int n) {
    free(T);
    free(INV);
    N = n;
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
    if (n > MAXN || n < 2 || k > 64) return 0;
    alloc_group(n);
    static int pw[64];
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
    return 1;
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
    alloc_group(cnt);
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
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int a, N, type, q, psl, m, k, r;
    long total;
} Cand;

static Cand pool[POOLMAX];
static int npool = 0;

static void push_cand(int a, int Nv, int type, int q, int psl, int m, int k, int r) {
    if (npool >= POOLMAX) return;
    Cand c;
    c.a = a;
    c.N = Nv;
    c.type = type;
    c.q = q;
    c.psl = psl;
    c.m = m;
    c.k = k;
    c.r = r;
    c.total = 2L * a * Nv;
    pool[npool++] = c;
}

static void gen_pool(long lowT, long highT) {
    static const int qs[] = {5, 7, 11, 13, 17};
    for (int a = 1; a <= MAXA; a++) {
        long Nlo = (lowT + 2L * a - 1) / (2L * a);
        long Nhi = highT / (2L * a);
        if (Nlo < 3) Nlo = 3;
        for (long Nv = Nlo; Nv <= Nhi; Nv++) {
            int cnt = 0;
            for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
                for (int psl = 0; psl < 2; psl++) {
                    long q = qs[qi];
                    long o = q * (q * q - 1);
                    if (psl) o /= 2;
                    if (o == Nv && Nv <= 2700 && cnt < 3) {
                        push_cand(a, (int)Nv, 1, (int)q, psl, 0, 0, 0);
                        cnt++;
                    }
                }
            }
            int mc = 0;
            for (int k = 2; k <= 12 && cnt < 3 && mc < 2; k++) {
                if (Nv % k) continue;
                long m = Nv / k;
                if (m < 3) continue;
                for (long r = 2; r < m; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    push_cand(a, (int)Nv, 0, 0, 0, (int)m, k, (int)r);
                    cnt++;
                    mc++;
                    break;
                }
            }
            if (cnt < 3) push_cand(a, (int)Nv, 0, 0, 0, (int)Nv, 1, 1);
        }
    }
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = (const Cand *)x, *q = (const Cand *)y;
    if (p->total != q->total) return p->total < q->total ? -1 : 1;
    if (p->a != q->a) return p->a - q->a;
    return p->type - q->type;
}

/* Set group globals and lift shape (A base vertices per side). */
static int A = 1, aN = 0, V = 0;

static int prepare(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r)
                            : build_matrix(c->q, c->psl);
    if (!ok) return 0;
    A = c->a;
    aN = A * N;
    V = 2 * aN;
    return V <= MAXV;
}

/* ------------------------------------------------------------------ lift state */

/* Dart k of A-vertex i goes to B-vertex PI[k][i] with voltage VV[i][k].
   PINV[k][j] is the A-index whose dart k reaches B_j. */
static int PI[MAXDEG][MAXA], PINV[MAXDEG][MAXA], VV[MAXA][MAXDEG];
static int oPI[MAXDEG][MAXA], oVV[MAXA][MAXDEG];

static void init_state(void) {
    int p[MAXA];
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < A; i++) p[i] = i;
        for (int i = A - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < A; i++) {
            PI[k][i] = p[i];
            PINV[k][p[i]] = i;
        }
    }
    for (int i = 0; i < A; i++)
        for (int k = 0; k < d; k++) VV[i][k] = rndint(N);
}

/* Distinct darts from the same A_i to the same B_j must have distinct voltages. */
static int valid_row(int i) {
    for (int k = 0; k < d; k++)
        for (int k2 = k + 1; k2 < d; k2++)
            if (PI[k][i] == PI[k2][i] && VV[i][k] == VV[i][k2]) return 0;
    return 1;
}

static int valid_all(void) {
    for (int i = 0; i < A; i++)
        if (!valid_row(i)) return 0;
    return 1;
}

static void swap_perm(int k, int i1, int i2) {
    int t = PI[k][i1];
    PI[k][i1] = PI[k][i2];
    PI[k][i2] = t;
    PINV[k][PI[k][i1]] = i1;
    PINV[k][PI[k][i2]] = i2;
}

static void save_state(void) {
    memcpy(oPI, PI, sizeof PI);
    memcpy(oVV, VV, sizeof VV);
}

static void load_state(void) {
    memcpy(PI, oPI, sizeof PI);
    memcpy(VV, oVV, sizeof VV);
    for (int k = 0; k < d; k++)
        for (int i = 0; i < A; i++) PINV[k][PI[k][i]] = i;
}

/* ------------------------------------------------------------------ BFS cost */

/* Vertices: A_i,x -> i*N+x ; B_j,y -> aN + j*N + y. Left G-multiplication is an automorphism. */
static int stamp[MAXV];
static int tick = 0;
static int qbuf[MAXV];

static int reached(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qbuf[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qbuf[head];
            if (v < aN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int j = PI[k][i];
                    int w = (int)T[(size_t)x * N + VV[i][k]];
                    int u = aN + j * N + w;
                    if (stamp[u] != tick) { stamp[u] = tick; qbuf[tail++] = u; }
                }
            } else {
                int r = v - aN;
                int j = r / N, y = r - j * N;
                for (int k = 0; k < d; k++) {
                    int i = PINV[k][j];
                    int w = (int)T[(size_t)y * N + INV[VV[i][k]]];
                    int u = i * N + w;
                    if (stamp[u] != tick) { stamp[u] = tick; qbuf[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of (source, vertex) pairs not reached within D. Stops early once above lim. */
static long cost_bounded(long lim) {
    long c = 0;
    for (int s = 0; s < 2 * A; s++) {
        int src = (s < A) ? s * N + e_id : aN + (s - A) * N + e_id;
        c += (long)(V - reached(src));
        if (c > lim) return c;
    }
    return c;
}

/* ------------------------------------------------------------------ annealing */

static int anneal(double until, double T0) {
    int tries = 0;
    do {
        init_state();
        tries++;
    } while (!valid_all() && tries < 2000);
    if (!valid_all()) return 0;

    long cur = cost_bounded(BIG);
    double ts = now();
    double span = until - ts;
    if (span <= 0.0) return 0;
    double temp = T0;
    long it = 0;
    while (cur > 0) {
        if ((++it & 31) == 0) {
            double t = now();
            if (t > until) return 0;
            double prog = (t - ts) / span;
            temp = T0 * (1.0 - prog) + 0.05;
        }
        /* Metropolis threshold drawn before the BFS: accept iff nc <= lim. */
        long lim = cur + (long)(-temp * log(rnd01() + 1e-12));
        if (A > 1 && rndint(2) == 0) {
            int k = rndint(d);
            int i1 = rndint(A);
            int i2 = rndint(A - 1);
            if (i2 >= i1) i2++;
            swap_perm(k, i1, i2);
            long nc = BIG;
            if (valid_row(i1) && valid_row(i2)) nc = cost_bounded(lim);
            if (nc <= lim) cur = nc;
            else swap_perm(k, i1, i2);
        } else {
            int i = rndint(A), k = rndint(d);
            int old = VV[i][k];
            int nv = rndint(N);
            if (nv == old) continue;
            VV[i][k] = nv;
            long nc = BIG;
            if (valid_row(i)) nc = cost_bounded(lim);
            if (nc <= lim) cur = nc;
            else VV[i][k] = old;
        }
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    moore_g = moore_bound();
    long lowT = ref + 1;
    long highT = (long)(1.07 * (double)ref) + 16;
    if (highT > moore_g) highT = moore_g;
    if (lowT > highT) { print_complete(); return 0; }

    gen_pool(lowT, highT);
    if (npool == 0) { print_complete(); return 0; }
    qsort(pool, (size_t)npool, sizeof(Cand), cmp_cand);
    int ncand = npool < MAXCAND ? npool : MAXCAND;

    /* Iterative deepening over candidates in ascending vertex count. */
    double budget0 = t_end - now();
    double base = budget0 * 0.02;
    if (base < 0.2) base = 0.2;
    if (base > 1.5) base = 1.5;

    long bestT = ref;
    int have = 0;
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);

    for (int round = 0; round < 10; round++) {
        for (int i = 0; i < ncand; i++) {
            double rem = t_end - now();
            if (rem < 0.2) break;
            Cand *c = &pool[i];
            if (c->total <= bestT) continue;
            if (!prepare(c)) continue;
            double slice = base * (double)(1L << round);
            if (slice > rem) slice = rem;
            if (anneal(now() + slice, 2.0)) {
                have = 1;
                bestc = *c;
                bestT = c->total;
                save_state();
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!prepare(&bestc)) { print_complete(); return 0; }
    load_state();
    if (!valid_all() || cost_bounded(0) != 0) { print_complete(); return 0; }

    printf("%d %ld\n", V, (long)A * N * d);
    for (int i = 0; i < A; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int j = PI[k][i];
                int w = (int)T[(size_t)x * N + VV[i][k]];
                printf("%d %d\n", i * N + x, aN + j * N + w);
            }
    return 0;
}
'''

REF_VERTICES = {(3, 3): 14, (4, 9): 4970}


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
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
