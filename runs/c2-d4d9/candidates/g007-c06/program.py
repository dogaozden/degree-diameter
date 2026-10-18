"""Program: bi-lift search. Base multigraph with P A-vertices and P B-vertices, lifted over a
finite group (metacyclic or SL/PSL(2,q)), with simulated annealing on the voltages and on the
target permutations.

Construction:
  * Base: d permutations sig[k] of {0..P-1}. Dart (i,k) joins A_i to B_{sig[k][i]} with voltage s_{ik}.
  * Lift: A_{i,x} ~ B_{sig[k][i], x*s_{ik}} for k < d. Degree d, bipartite, 2PN vertices.
  * Simplicity holds iff, for each i, the pairs (sig[k][i], s_{ik}) are distinct over k. Moves keep this.
  * Left multiplication is an automorphism, so the diameter is <= D iff BFS from each base
    representative (A_{i,e} and B_{j,e}) reaches all vertices within D steps.

Search:
  * Phase 1 (p = 1, ascending V): secures a fallback, like the earlier bi-Cayley ladder.
  * Phase 2 (random order over all P, V above the best found): tries multi-vertex base lifts
    (P = 2..12), which is the new part of the search.
  * Each candidate gets a short triage run, and a longer run only if it came close to valid.

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
#define MAXP 12
#define MAXDEG 8
#define VMAX 8192
#define MAXCAND 60000
#define T_HI 3.0
#define T_LO 0.05
#define CYCLES 3.0
#define NEAR_MISS 6
#define BIG_COST (1L << 60)

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

/* SL(2,q) or PSL(2,q), q prime. */
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

/* ------------------------------------------------------------------ lift state */

static int P = 1, PN = 0, VT = 0;
static int sig[MAXDEG][MAXP];        /* A_i -> B_{sig[k][i]} */
static int sigInv[MAXDEG][MAXP];     /* B_j <- A_{sigInv[k][j]} */
static int VV[MAXP][MAXDEG];         /* voltage of dart (i,k) */
static int Rf[MAXP][MAXDEG][MAXN];   /* Rf[i][k][x] = x * s */
static int Rb[MAXP][MAXDEG][MAXN];   /* Rb[i][k][y] = y * s^{-1} */

static int ibSig[MAXDEG][MAXP];
static int ibVV[MAXP][MAXDEG];
static int oSig[MAXDEG][MAXP];
static int oVV[MAXP][MAXDEG];

static int stamp[VMAX];
static int tick = 0;
static int qv[VMAX];

static void set_dart(int i, int k) {
    int s = VV[i][k], si = INV[s];
    for (int x = 0; x < N; x++) {
        Rf[i][k][x] = (int)T[(size_t)x * N + s];
        Rb[i][k][x] = (int)T[(size_t)x * N + si];
    }
}

static void set_all_darts(void) {
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) set_dart(i, k);
}

static void set_perm_inv(int k) {
    for (int i = 0; i < P; i++) sigInv[k][sig[k][i]] = i;
}

/* Does dart (i,k) clash with another dart of row i? */
static int conflict_row(int i, int k) {
    for (int k2 = 0; k2 < d; k2++)
        if (k2 != k && sig[k2][i] == sig[k][i] && VV[i][k2] == VV[i][k]) return 1;
    return 0;
}

static int row_ok(int i) {
    for (int k = 0; k < d; k++)
        if (conflict_row(i, k)) return 0;
    return 1;
}

static int all_rows_ok(void) {
    for (int i = 0; i < P; i++)
        if (!row_ok(i)) return 0;
    return 1;
}

static int conflict_before(int i, int k) {
    for (int k2 = 0; k2 < k; k2++)
        if (sig[k2][i] == sig[k][i] && VV[i][k2] == VV[i][k]) return 1;
    return 0;
}

static int randomize_state(void) {
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < P; i++) sig[k][i] = i;
        for (int i = P - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int t = sig[k][i];
            sig[k][i] = sig[k][r];
            sig[k][r] = t;
        }
        set_perm_inv(k);
    }
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) {
            int tries = 0;
            do {
                VV[i][k] = rndint(N);
                tries++;
            } while (conflict_before(i, k) && tries < 10000);
            if (conflict_before(i, k)) return 0;
        }
    set_all_darts();
    return 1;
}

/* ------------------------------------------------------------------ BFS cost */

/* Number of vertices reached within dmax of src. */
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
            if (v < PN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int j = sig[k][i];
                    int u = PN + j * N + Rf[i][k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int i = sigInv[k][j];
                    int u = i * N + Rb[i][k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base representatives A_{i,e} and B_{j,e} of unreached vertices (0 = valid). */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < P; i++) {
        c += (long)(VT - ball(i * N + e_id, D));
        c += (long)(VT - ball(PN + i * N + e_id, D));
    }
    return c;
}

/* ------------------------------------------------------------------ annealing */

static long last_min = BIG_COST;

static void save_best(void) {
    memcpy(ibSig, sig, sizeof sig);
    memcpy(ibVV, VV, sizeof VV);
}

static void load_best(void) {
    memcpy(sig, ibSig, sizeof sig);
    memcpy(VV, ibVV, sizeof VV);
    for (int k = 0; k < d; k++) set_perm_inv(k);
    set_all_darts();
}

static int climb(double until) {
    last_min = BIG_COST;
    if (N <= d + 1) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    if (!randomize_state()) return 0;
    long cur = cost_now();
    long bestc = cur;
    save_best();
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        if (P > 1 && rndint(10) < 4) {
            /* swap the targets of two A-vertices within permutation k */
            int k = rndint(d), i = rndint(P), i2 = rndint(P);
            if (i == i2) continue;
            int ji = sig[k][i], ji2 = sig[k][i2];
            sig[k][i] = ji2;
            sig[k][i2] = ji;
            sigInv[k][ji2] = i;
            sigInv[k][ji] = i2;
            if (!row_ok(i) || !row_ok(i2)) {
                sig[k][i] = ji;
                sig[k][i2] = ji2;
                sigInv[k][ji] = i;
                sigInv[k][ji2] = i2;
                continue;
            }
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) { bestc = cur; save_best(); }
            } else {
                sig[k][i] = ji;
                sig[k][i2] = ji2;
                sigInv[k][ji] = i;
                sigInv[k][ji2] = i2;
            }
        } else {
            /* change one voltage */
            int i = rndint(P), k = rndint(d);
            int old = VV[i][k];
            int nv = rndint(N);
            if (nv == old) continue;
            VV[i][k] = nv;
            if (!row_ok(i)) { VV[i][k] = old; continue; }
            set_dart(i, k);
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
                if (cur < bestc) { bestc = cur; save_best(); }
            } else {
                VV[i][k] = old;
                set_dart(i, k);
            }
        }
    }
    last_min = bestc;
    if (bestc != 0) return 0;
    load_best();
    return 1;
}

/* Short run first; a longer run only if the short run came close to valid. */
static int triage(double s1, double s2, double deadline) {
    double rem = deadline - now();
    double slice = s1 < rem ? s1 : rem;
    if (slice <= 0.05) return 0;
    if (climb(now() + slice)) return 1;
    if (last_min > (long)NEAR_MISS * P) return 0;
    rem = deadline - now();
    slice = s2 < rem ? s2 : rem;
    if (slice <= 0.05) return 0;
    return climb(now() + slice);
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r;
    int p, N, V;
} Cand;

static Cand *cands = NULL;
static int ncand = 0;

static void push_cand(int type, int q, int psl, int m, int k, int r, int p, int Nn) {
    if (ncand >= MAXCAND) return;
    Cand c;
    c.type = type;
    c.q = q;
    c.psl = psl;
    c.m = m;
    c.k = k;
    c.r = r;
    c.p = p;
    c.N = Nn;
    c.V = 2 * p * Nn;
    cands[ncand++] = c;
}

static void gen_cands(long vlo, long vhi) {
    static const int plist[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
    static const int mq[][2] = {{5, 0}, {5, 1}, {7, 0}, {7, 1}, {11, 0},
                                {11, 1}, {13, 0}, {13, 1}, {17, 1}};
    int np = (int)(sizeof plist / sizeof plist[0]);
    int nmq = (int)(sizeof mq / sizeof mq[0]);
    for (int pi = 0; pi < np; pi++) {
        int p = plist[pi];
        long nlo = (vlo + 2L * p - 1) / (2L * p);
        long nhi = vhi / (2L * p);
        if (nhi > MAXN) nhi = MAXN;
        for (long Nn = nlo; Nn <= nhi; Nn++) {
            if (Nn < d + 2) continue;
            for (long k = 1; k <= Nn / 2; k++) {
                if (Nn % k) continue;
                long m = Nn / k;
                if (m < 2) continue;
                if (k == 1) {
                    push_cand(0, 0, 0, (int)m, 1, 1, p, (int)Nn);
                    continue;
                }
                int got = 0;
                for (long r = 1; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1 % m) continue;
                    push_cand(0, 0, 0, (int)m, (int)k, (int)r, p, (int)Nn);
                    got++;
                }
            }
        }
    }
    for (int pi = 0; pi < np; pi++) {
        int p = plist[pi];
        for (int mi = 0; mi < nmq; mi++) {
            long q = mq[mi][0];
            int psl = mq[mi][1];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXN) continue;
            long V = 2L * p * o;
            if (V < vlo || V > vhi) continue;
            push_cand(1, (int)q, psl, 0, 0, 0, p, (int)o);
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return x->p - y->p;
}

static void shuffle_cands(void) {
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand t = cands[i];
        cands[i] = cands[j];
        cands[j] = t;
    }
}

/* Build the group for c and set the lift size. */
static int apply_candidate(const Cand *c) {
    int n;
    if (c->type == 0) n = build_meta(c->m, c->k, c->r);
    else n = build_matrix(c->q, c->psl);
    if (n != c->N || n < 2) return 0;
    P = c->p;
    PN = P * N;
    VT = 2 * PN;
    if (VT > VMAX) return 0;
    return 1;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_lift(void) {
    long M = (long)PN * d;
    printf("%d %ld\n", VT, M);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, PN + sig[k][i] * N + Rf[i][k][x]);
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

    double t0 = now();
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    if (ref <= 0) ref = moore / 4;
    long vlo = (long)(0.70 * (double)ref);
    long vhi = (long)(1.12 * (double)ref);
    if (vhi > moore) vhi = moore;
    if (vhi > VMAX) vhi = VMAX;
    if (vlo < 2L * d + 2) vlo = 2L * d + 2;
    if (vhi <= vlo) { print_complete(); return 0; }

    cands = malloc(sizeof(Cand) * MAXCAND);
    if (!cands) { print_complete(); return 0; }
    gen_cands(vlo, vhi);
    if (ncand == 0) { print_complete(); return 0; }

    long bestV = 2L * d;
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);

    /* Phase 1: ascending p = 1 ladder for a secure fallback (about half the time). */
    qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);
    double t1 = t0 + 0.5 * usable;
    for (int ci = 0; ci < ncand; ci++) {
        Cand *c = &cands[ci];
        if (c->p != 1) continue;
        if (now() >= t1) break;
        if (c->V <= bestV) continue;
        if (!apply_candidate(c)) continue;
        if (triage(0.02 * usable, 0.10 * usable, t1)) {
            have = 1;
            bestV = VT;
            best = *c;
            memcpy(oSig, sig, sizeof sig);
            memcpy(oVV, VV, sizeof VV);
        }
    }

    /* Phase 2: random order over all base sizes, only V above the best so far. */
    shuffle_cands();
    for (int ci = 0; ci < ncand; ci++) {
        Cand *c = &cands[ci];
        if (now() >= t_end - 0.3) break;
        if (c->V <= bestV) continue;
        if (!apply_candidate(c)) continue;
        if (triage(0.04 * usable, 0.15 * usable, t_end)) {
            have = 1;
            bestV = VT;
            best = *c;
            memcpy(oSig, sig, sizeof sig);
            memcpy(oVV, VV, sizeof VV);
        }
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_candidate(&best)) { print_complete(); return 0; }
    memcpy(sig, oSig, sizeof sig);
    memcpy(VV, oVV, sizeof VV);
    for (int k = 0; k < d; k++) set_perm_inv(k);
    set_all_darts();
    if (cost_now() != 0 || !all_rows_ok()) { print_complete(); return 0; }
    print_lift();
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
            ref = REF_VERTICES.get((d, D), max(2 * d + 2, lib.moore_bound(d, D) // 4))
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
