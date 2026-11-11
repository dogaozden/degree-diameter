"""Program: multi-orbit bi-Cayley (base-graph lift) search with simulated annealing.

New construction idea: a bipartite graph on 2*B*N vertices built from B orbits per side of a
group G of order N. Dart (i, j, s) joins A_i g to B_j (g s). Each A_i and each B_j carries d
darts, set by a base multiplicity pattern M with row and column sums d. Darts that share the
same (i, j) need distinct voltages, so the graph stays simple.

Left multiplication is an automorphism, so diameter <= D only needs BFS from the 2B vertices
A_i e and B_j e. With B = 2, SL(2,11) (order 1320) gives 4 * 1320 = 5280 vertices, above the
record 4970. The C engine searches voltages for all these candidates in ascending order of
order, so the search climbs one size at a time. B = 1 candidates are the parent's bi-Cayley
graphs. Python keeps the validated best graph, with the known start or K_{d,d} as fallback.
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
#define MAXB 2
#define MAXDEG 8
#define MAXE (MAXB * MAXDEG)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 8000

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D;
static double usable, t_end;

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
static int *INV = NULL;

static void alloc_group(int n) {
    free(T);
    free(INV);
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
}

static void finish_inv(void) {
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if ((int)T[(size_t)x * N + y] == e_id) { INV[x] = y; break; }
    }
}

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b. */
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
static int qg = 0, psl_g = 0;
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

/* ------------------------------------------------------------------ base graph and darts */

static int B = 1, E = 0, NV = 0;
static int DA[MAXE], DB[MAXE], S[MAXE];
static int BD[MAXB][MAXDEG];          /* darts entering B_j */
static int RA[MAXE][MAXN];            /* RA[e][g] = g * s_e   */
static int RB[MAXE][MAXN];            /* RB[e][h] = h * s_e^-1 */

/* Base multiplicity pattern: B = 1 gives [[d]]; B = 2 gives [[a, d-a], [d-a, a]].
   Dart e has DA[e] = e / d, so the darts of A_i are i*d .. i*d+d-1. */
static void setup_pattern(int Bn, int a) {
    int M[MAXB][MAXB];
    B = Bn;
    E = B * d;
    if (B == 1) {
        M[0][0] = d;
    } else {
        M[0][0] = a;
        M[0][1] = d - a;
        M[1][0] = d - a;
        M[1][1] = a;
    }
    int cntB[MAXB];
    for (int j = 0; j < MAXB; j++) cntB[j] = 0;
    int e = 0;
    for (int i = 0; i < B; i++)
        for (int j = 0; j < B; j++)
            for (int t = 0; t < M[i][j]; t++) {
                DA[e] = i;
                DB[e] = j;
                BD[j][cntB[j]++] = e;
                e++;
            }
}

static void set_dart(int e) {
    int s = S[e], si = INV[s];
    for (int x = 0; x < N; x++) {
        RA[e][x] = (int)T[(size_t)x * N + s];
        RB[e][x] = (int)T[(size_t)x * N + si];
    }
}

static void set_all(void) {
    for (int e = 0; e < E; e++) set_dart(e);
}

/* 1 if voltage x on dart e clashes with an earlier dart f < lim on the same (i, j). */
static int conflict(int e, int x, int lim) {
    for (int f = 0; f < lim; f++)
        if (f != e && DA[f] == DA[e] && DB[f] == DB[e] && S[f] == x) return 1;
    return 0;
}

static void randomize(void) {
    for (int e = 0; e < E; e++) {
        int x;
        do x = rndint(N); while (conflict(e, x, e));
        S[e] = x;
    }
    set_all();
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
    int nA = B * N;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < nA) {
                int i = v / N, g = v - i * N;
                for (int k = 0; k < d; k++) {
                    int e = i * d + k;
                    int u = (B + DB[e]) * N + RA[e][g];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - nA;
                int j = w / N, h = w - j * N;
                for (int k = 0; k < d; k++) {
                    int e = BD[j][k];
                    int u = DA[e] * N + RB[e][h];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertices not reached within D from the 2B orbit representatives (0 = valid). */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < B; i++) {
        c += (long)(NV - ball(i * N + e_id, D));
        c += (long)(NV - ball((B + i) * N + e_id, D));
    }
    return c;
}

/* Simulated annealing with sawtooth reheating over the dart voltages. */
static int cbS[MAXE];
static int climb(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize();
    long cur = cost_now();
    long bestc = cur;
    memcpy(cbS, S, sizeof(int) * (size_t)E);
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
        int e = rndint(E);
        int old = S[e];
        int x;
        do x = rndint(N); while (x == old || conflict(e, x, E));
        S[e] = x;
        set_dart(e);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(cbS, S, sizeof(int) * (size_t)E);
            }
        } else {
            S[e] = old;
            set_dart(e);
        }
    }
    if (bestc != 0) return 0;
    memcpy(S, cbS, sizeof(int) * (size_t)E);
    set_all();
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;          /* 0 metacyclic, 1 matrix */
    int q, psl, m, k, r;
    int B, a;          /* orbits per side and base pattern */
    int N, total;      /* group order and 2*B*N */
    int tried;
    unsigned tie;
} Cand;

static Cand cand[MAXCAND];
static int ncand = 0;
static int bestCi = -1;
static int bestTotal = 0;
static int gS[MAXE];

static void add_cand(const Cand *c) {
    if (ncand < MAXCAND) cand[ncand++] = *c;
}

static void new_cand(Cand *c, int type, int nb, int na, int Nv) {
    memset(c, 0, sizeof *c);
    c->type = type;
    c->B = nb;
    c->a = na;
    c->N = Nv;
    c->total = 2 * nb * Nv;
    c->tie = (unsigned)rnd();
}

static void gen_meta(int Nv, int nb, int na) {
    for (int k = 2; k <= Nv / 3; k++) {
        if (Nv % k) continue;
        int m = Nv / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            new_cand(&c, 0, nb, na, Nv);
            c.m = m;
            c.k = k;
            c.r = r;
            add_cand(&c);
            got++;
        }
    }
}

static void gen_all(int lo, int hi) {
    for (int Nv = (lo + 1) / 2; 2 * Nv <= hi && Nv <= MAXN; Nv++)
        gen_meta(Nv, 1, 0);
    for (int a = 1; 2 * a <= d; a++)
        for (int Nv = (lo + 3) / 4; 4 * Nv <= hi && Nv <= MAXN; Nv++)
            gen_meta(Nv, 2, a);
}

static void gen_matrix(int lo, int hi) {
    static const int qs[4] = {5, 7, 11, 13};
    for (int qi = 0; qi < 4; qi++)
        for (int psl = 0; psl < 2; psl++) {
            int q = qs[qi];
            int o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o > MAXN) continue;
            Cand c;
            if (2 * o >= lo && 2 * o <= hi) {
                new_cand(&c, 1, 1, 0, o);
                c.q = q;
                c.psl = psl;
                add_cand(&c);
            }
            for (int a = 1; 2 * a <= d; a++)
                if (4 * o >= lo && 4 * o <= hi) {
                    new_cand(&c, 1, 2, a, o);
                    c.q = q;
                    c.psl = psl;
                    add_cand(&c);
                }
        }
}

static int cmp_cand(const void *pa, const void *pb) {
    const Cand *a = pa, *b = pb;
    if (a->total != b->total) return a->total < b->total ? -1 : 1;
    if (a->tie != b->tie) return a->tie < b->tie ? -1 : 1;
    return 0;
}

static int apply_cand(const Cand *c) {
    int n = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (n != c->N) return 0;
    setup_pattern(c->B, c->a);
    NV = 2 * B * N;
    return 1;
}

static void attempt(int i, double frac) {
    Cand *c = &cand[i];
    c->tried = 1;
    double remaining = t_end - now();
    if (remaining < 0.2) return;
    if (!apply_cand(c)) return;
    double slice = usable * frac;
    if (slice > remaining) slice = remaining;
    if (climb(now() + slice)) {
        bestTotal = c->total;
        bestCi = i;
        memcpy(gS, S, sizeof(int) * (size_t)E);
    }
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void output_best(void) {
    if (!apply_cand(&cand[bestCi])) { print_complete(); return; }
    memcpy(S, gS, sizeof(int) * (size_t)E);
    set_all();
    if (cost_now() != 0) { print_complete(); return; }
    printf("%d %d\n", NV, E * N);
    for (int e = 0; e < E; e++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", DA[e] * N + x, (B + DB[e]) * N + RA[e][x]);
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
    usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    long lo = (long)(0.7 * (double)ref);
    long hi = (long)(1.2 * (double)ref);
    if (hi > moore) hi = moore;
    if (lo < 6) lo = 6;

    gen_all((int)lo, (int)hi);
    gen_matrix((int)lo, (int)hi);
    if (ncand > 1) qsort(cand, (size_t)ncand, sizeof(Cand), cmp_cand);

    /* Phase A: matrix-group lifts first (SL/PSL, incl. B = 2 orders above the record). */
    for (int i = 0; i < ncand; i++) {
        if (now() > t_end - 0.2) break;
        if (cand[i].type != 1) continue;
        if (cand[i].total <= bestTotal || cand[i].total > moore) continue;
        attempt(i, 0.08);
    }

    /* Phase B: ascending ladder over all untried candidates above the current best. */
    for (int i = 0; i < ncand; i++) {
        if (now() > t_end - 0.2) break;
        if (cand[i].tried) continue;
        if (cand[i].total <= bestTotal || cand[i].total > moore) continue;
        attempt(i, 0.04);
    }

    if (bestCi < 0) { print_complete(); return 0; }
    output_best();
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
            ref = REF_VERTICES.get((d, D), 4970)
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
