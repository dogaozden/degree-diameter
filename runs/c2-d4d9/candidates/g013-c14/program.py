"""Program: multi-vertex voltage lifts over finite groups, found by simulated annealing.

Construction (replaces the single-orbit bi-Cayley search of the parent):
  * Base graph with PB vertices on each side (PB = 1..4). Dart k (0 <= k < d) joins A_i
    to B_{sig[k][i]}, where sig[k] is a permutation for k >= 1 and sig[0] = identity.
  * Each dart carries a voltage vol[k][i] in a group G of order N. Dart 0 has voltage e
    (a normalisation: relabel the B side). The lift has vertices (A_i, x) and (B_j, y),
    and (A_i, x) ~ (B_j, x * vol) for each dart from A_i to B_j.
  * The lift has 2*PB*N vertices and is d-regular and bipartite. It is simple iff, for
    each i, the pairs (sig[k][i], vol[k][i]) are distinct over k.
  * Left multiplication is an automorphism, so diameter <= D iff BFS from (A_i, e) and
    (B_j, e) for every i, j reaches all vertices within D.

Search:
  * Candidate (PB, group) pairs have vertex counts in [ref, 1.2*ref + 16], sorted by
    vertex count. Groups: metacyclic Z_m x| Z_k (including cyclic) and SL/PSL(2, q), q prime.
  * Iterative-deepening rounds give each still-improving candidate a slice that doubles
    each round. Within a slice, simulated annealing with sawtooth reheating moves voltages
    and base permutations, with cost = number of (source, vertex) pairs beyond distance D.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks its output with
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
#define MAXPB 4
#define MAXDEG 8
#define MAXV 8192
#define MAXCAND 24
#define MAXGEN 40000

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D;
static int PB;             /* base size: PB vertices on each side */
static int N, e_id;        /* group order and identity element */
static uint16_t *T = NULL; /* T[x*N+y] = x*y */
static int *INV = NULL;    /* INV[x] = x^{-1} */
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

/* ------------------------------------------------------------------ groups */

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

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;     /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r;
    int N;        /* group order */
    int P;        /* base size PB */
    int V;        /* vertex count 2*P*N */
} Cand;

static Cand gen[MAXGEN];
static int ngen = 0;

static int apply_cand(const Cand *c) {
    int got = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    return got == c->N;
}

static void push_cand(int type, int q, int psl, int m, int k, int r, int Nv, int p) {
    if (ngen >= MAXGEN) return;
    Cand c;
    c.type = type; c.q = q; c.psl = psl; c.m = m; c.k = k; c.r = r;
    c.N = Nv; c.P = p; c.V = 2 * p * Nv;
    gen[ngen++] = c;
}

static void gen_candidates(long Vlo, long Vhi, long moore) {
    ngen = 0;
    for (int p = 1; p <= MAXPB; p++) {
        long Nlo = (Vlo + 2L * p - 1) / (2L * p);
        long Nhi = Vhi / (2L * p);
        if (Nlo < 3) Nlo = 3;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long Nv = Nlo; Nv <= Nhi; Nv++) {
            long V = 2L * p * Nv;
            if (V > moore || V > MAXV) break;
            for (long k = 1; k <= Nv; k++) {
                if (Nv % k) continue;
                long m = Nv / k;
                if (m < 2) continue;
                int got = 0;
                for (long r = 2; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, k, m) != 1) continue;
                    push_cand(0, 0, 0, (int)m, (int)k, (int)r, (int)Nv, p);
                    got++;
                }
                if (got == 0 && powmod_l(1, k, m) == 1)
                    push_cand(0, 0, 0, (int)m, (int)k, 1, (int)Nv, p);
            }
        }
    }
    static const int mq[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < 6; qi++)
        for (int psl = 0; psl < 2; psl++)
            for (int p = 1; p <= MAXPB; p++) {
                long q = mq[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                if (o > MAXN) continue;
                long V = 2L * p * o;
                if (V < Vlo || V > Vhi || V > moore || V > MAXV) continue;
                push_cand(1, (int)q, psl, 0, 0, 0, (int)o, p);
            }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->P != y->P) return x->P - y->P;
    if (x->type != y->type) return x->type - y->type;
    return x->N - y->N;
}

/* ------------------------------------------------------------------ lift state */

static int sig[MAXDEG][MAXPB], sigInv[MAXDEG][MAXPB];
static int vol[MAXDEG][MAXPB], volInv[MAXDEG][MAXPB];
/* nbA[k][i][x]: neighbour of vertex (A_i, x) via dart k (a B index).
   nbB[k][j][y]: neighbour of vertex (B_j, y) via dart k (an A index). */
static int nbA[MAXDEG][MAXPB][MAXN];
static int nbB[MAXDEG][MAXPB][MAXN];
static int bestSig[MAXDEG][MAXPB], bestVol[MAXDEG][MAXPB];

static int stamp[MAXV];
static int qv[MAXV];
static int tick = 0;

/* Recompute the neighbour columns of dart (k, i). */
static void set_dart_col(int k, int i) {
    int j = sig[k][i];
    int g = vol[k][i], gi = volInv[k][i];
    int baseB = PB * N + j * N;
    int baseA = i * N;
    for (int x = 0; x < N; x++) nbA[k][i][x] = baseB + (int)T[(size_t)x * N + g];
    for (int y = 0; y < N; y++) nbB[k][j][y] = baseA + (int)T[(size_t)y * N + gi];
}

static void set_vol(int k, int i, int v) {
    vol[k][i] = v;
    volInv[k][i] = INV[v];
    set_dart_col(k, i);
}

static void swap_sig(int k, int i1, int i2) {
    int t = sig[k][i1];
    sig[k][i1] = sig[k][i2];
    sig[k][i2] = t;
    sigInv[k][sig[k][i1]] = i1;
    sigInv[k][sig[k][i2]] = i2;
    set_dart_col(k, i1);
    set_dart_col(k, i2);
}

/* Simple-graph condition at base vertex A_i: darts from A_i must have distinct (target, voltage). */
static int ok_i(int i) {
    for (int k1 = 0; k1 < d; k1++)
        for (int k2 = k1 + 1; k2 < d; k2++)
            if (sig[k1][i] == sig[k2][i] && vol[k1][i] == vol[k2][i]) return 0;
    return 1;
}

static int randomize_state(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < PB; i++) sig[k][i] = i;
    for (int k = 1; k < d; k++) {
        int perm[MAXPB];
        for (int i = 0; i < PB; i++) perm[i] = i;
        for (int i = PB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < PB; i++) sig[k][i] = perm[i];
    }
    for (int k = 0; k < d; k++)
        for (int i = 0; i < PB; i++) sigInv[k][sig[k][i]] = i;
    for (int i = 0; i < PB; i++) vol[0][i] = e_id;
    for (int i = 0; i < PB; i++) {
        int good = 0;
        for (int tries = 0; tries < 20000 && !good; tries++) {
            for (int k = 1; k < d; k++) vol[k][i] = rndint(N);
            good = ok_i(i);
        }
        if (!good) return 0;
    }
    for (int k = 0; k < d; k++)
        for (int i = 0; i < PB; i++) volInv[k][i] = INV[vol[k][i]];
    for (int k = 0; k < d; k++)
        for (int i = 0; i < PB; i++) set_dart_col(k, i);
    return 1;
}

static void restore_state(void) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < PB; i++) {
            sig[k][i] = bestSig[k][i];
            vol[k][i] = bestVol[k][i];
        }
    for (int k = 0; k < d; k++)
        for (int i = 0; i < PB; i++) {
            sigInv[k][sig[k][i]] = i;
            volInv[k][i] = INV[vol[k][i]];
        }
    for (int k = 0; k < d; k++)
        for (int i = 0; i < PB; i++) set_dart_col(k, i);
}

/* ------------------------------------------------------------------ BFS cost */

static int ball(int src) {
    int V = 2 * PB * N, pN = PB * N;
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
            int v = qv[head];
            if (v < pN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int u = nbA[k][i][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int t = v - pN;
                int j = t / N, y = t - j * N;
                for (int k = 0; k < d; k++) {
                    int u = nbB[k][j][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
        if (tail == V) break;
    }
    return tail;
}

/* Number of (source, vertex) pairs at distance > D; 0 means the lift is valid. */
static long cost_now(void) {
    long V = 2L * PB * N;
    long c = 0;
    for (int i = 0; i < PB; i++) c += V - ball(i * N + e_id);
    for (int j = 0; j < PB; j++) c += V - ball(PB * N + j * N + e_id);
    return c;
}

/* Simulated annealing with sawtooth reheating. Returns 1 when the cost reaches 0. */
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    if (!randomize_state()) return 0;
    long cur = cost_now();
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
        if (PB >= 2 && rndint(100) < 15) {
            int k = 1 + rndint(d - 1);
            int i1 = rndint(PB);
            int i2 = rndint(PB - 1);
            if (i2 >= i1) i2++;
            swap_sig(k, i1, i2);
            if (!ok_i(i1) || !ok_i(i2)) {
                swap_sig(k, i1, i2);
                continue;
            }
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                swap_sig(k, i1, i2);
            }
        } else {
            int k = 1 + rndint(d - 1);
            int i = rndint(PB);
            int old = vol[k][i];
            int v = rndint(N);
            if (v == old) continue;
            set_vol(k, i, v);
            if (!ok_i(i)) {
                set_vol(k, i, old);
                continue;
            }
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                set_vol(k, i, old);
            }
        }
    }
    return cur == 0;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    int V = 2 * PB * N;
    printf("%d %d\n", V, PB * N * d);
    for (int i = 0; i < PB; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, nbA[k][i][x]);
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

    if (d < 3 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    if (ref <= 0) ref = 2L * d;
    long Vlo = ref;
    long Vhi = (long)(1.2 * (double)ref) + 16;
    if (Vhi > moore) Vhi = moore;
    if (Vhi > MAXV) Vhi = MAXV;

    gen_candidates(Vlo, Vhi, moore);
    if (ngen == 0) { print_complete(); return 0; }
    qsort(gen, (size_t)ngen, sizeof(Cand), cmp_cand);
    int nc = ngen < MAXCAND ? ngen : MAXCAND;

    double remaining0 = t_end - now();
    double slice0 = remaining0 / (nc * 4.0);
    if (slice0 < 0.3) slice0 = 0.3;

    long bestV = 0;
    int have = 0;
    Cand best;
    memset(&best, 0, sizeof best);

    /* Iterative deepening: candidates in order of vertex count; slices double per round. */
    for (int round = 0; round < 8; round++) {
        for (int ci = 0; ci < nc; ci++) {
            double remaining = t_end - now();
            if (remaining < 0.2) break;
            const Cand *c = &gen[ci];
            if ((long)c->V <= bestV) continue;
            if (!apply_cand(c)) continue;
            PB = c->P;
            double slice = slice0 * (double)(1L << round);
            if (slice > remaining) slice = remaining;
            if (climb(now() + slice)) {
                if (cost_now() == 0) {
                    have = 1;
                    bestV = c->V;
                    best = *c;
                    memcpy(bestSig, sig, sizeof sig);
                    memcpy(bestVol, vol, sizeof vol);
                }
            }
        }
        if (t_end - now() < 0.2) break;
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&best)) { print_complete(); return 0; }
    PB = best.P;
    restore_state();
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
    budget = 0.82 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.5:
        try:
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), ref],
                             timeout=budget + 10)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass   # keep the valid fallback
    return best
