"""Program: multi-orbit voltage lifts over metacyclic and matrix groups, with a
parent-style bi-Cayley phase kept as the safety net.

New construction (bold change):
  * Base graph with B "A" vertices and B "B" vertices, each base vertex of degree d.
    Dart p of A_i goes to B_{sig_p(i)}, for permutations sig_p of {0..B-1}.
  * Voltages t_{p,i} in a group G of order N. Lift: A(i,g) ~ B(sig_p(i), g*t_{p,i}).
    The lift has 2*B*N vertices, is bipartite, has degree d, and is invariant under
    left multiplication by G.
  * Validity: BFS from the 2B base vertices A(i,e), B(j,e) must reach all 2BN vertices
    within D steps. Since left multiplication is an automorphism, this is exactly the
    diameter condition. A duplicate-edge penalty keeps the lift simple.
  * Moves: voltage changes and swaps inside a base permutation, under simulated annealing
    with sawtooth reheating and best-state memory.

Scheduling:
  * Phase A: the parent's bi-Cayley search (B = 1) over groups near the record vertex
    count, tried first so the record is reproduced when reachable.
  * Phase B: B >= 2 lifts with 2BN just above the reference, sorted by vertex count
    ascending, so the smallest improvements are attempted first.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid, keeps it only if it has more vertices than the known start, and otherwise
returns the known start or K_{d,d}.

Risk: the record is reproduced only if phase A rediscovers it within its share of the
time budget. If it does not, the returned graph is the much smaller fallback.
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
#define MAXB 16
#define MAXDEG 8
#define MAXV (2 * MAXB * MAXN)
#define MAXEDGES (MAXB * MAXN * MAXDEG)
#define MAXGEN 40000
#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D;
static double t_end;
static long bestFound = 0;
static int outN = 0, outM = 0;
static int outE[2 * MAXEDGES];

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

static int N = 0, e_id = 0, B = 1;
static uint16_t *T = NULL;   /* T[x*N+y] = x*y */
static int *INV = NULL;      /* INV[x] = x^{-1} */

static int alloc_group(int n) {
    free(T);
    free(INV);
    T = NULL;
    INV = NULL;
    T = malloc(sizeof(uint16_t) * (size_t)n * (size_t)n);
    INV = malloc(sizeof(int) * (size_t)n);
    return T != NULL && INV != NULL;
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
    if (!alloc_group(n)) return 0;
    N = n;
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
    return 1;
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
        if (!idxm) { idxm_cap = 0; return 0; }
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
    if (cnt < 2) return 0;
    if (!alloc_group(cnt)) return 0;
    N = cnt;
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
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, B, N;
    long V;     /* total vertices = 2 * B * N */
} Cand;

static Cand genA[MAXGEN], genB[MAXGEN];
static int nGenA = 0, nGenB = 0;

static long matrix_order(int q, int psl) {
    long o = (long)q * ((long)q * q - 1);
    if (psl) o /= 2;
    return o;
}

static void add_meta(int Nval, int Bv, Cand *arr, int *cnt) {
    for (int k = 2; k <= Nval / 3 && *cnt < MAXGEN; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 1; r < m && got < 2 && *cnt < MAXGEN; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.B = Bv;
            c.N = Nval;
            c.V = 2L * Bv * Nval;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

static void add_matrix(int q, int psl, int Bv, Cand *arr, int *cnt) {
    if (*cnt >= MAXGEN) return;
    Cand c;
    memset(&c, 0, sizeof c);
    c.type = 1;
    c.q = q;
    c.psl = psl;
    c.B = Bv;
    c.N = (int)matrix_order(q, psl);
    c.V = 2L * Bv * c.N;
    arr[(*cnt)++] = c;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return x->B - y->B;
}

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok) return 0;
    B = c->B;
    if (B < 1 || B > MAXB) return 0;
    if (N < 2) return 0;
    if (2L * B * N > moore_bound()) return 0;
    return 1;
}

/* ------------------------------------------------------------------ lift state */

static int sig[MAXDEG][MAXB];      /* A_i -> B_{sig[p][i]} */
static int siginv[MAXDEG][MAXB];   /* B_j -> A_{siginv[p][j]} */
static int tv[MAXDEG][MAXB];       /* voltage of dart (p,i) */
static int tinv[MAXDEG][MAXB];     /* inverse voltage */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int next_tick(void) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    return tick;
}

/* Vertices: A(i,g) = i*N+g, B(j,h) = B*N + j*N + h. Number reached within dmax. */
static int lift_ball(int src, int dmax) {
    int tk = next_tick();
    int BN = B * N;
    int head = 0, tail = 0;
    stamp[src] = tk;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                for (int p = 0; p < d; p++) {
                    int u = BN + sig[p][i] * N + (int)T[(size_t)g * N + tv[p][i]];
                    if (stamp[u] != tk) { stamp[u] = tk; qv[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, h = w - j * N;
                for (int p = 0; p < d; p++) {
                    int i = siginv[p][j];
                    int u = i * N + (int)T[(size_t)h * N + tinv[p][i]];
                    if (stamp[u] != tk) { stamp[u] = tk; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Each duplicate dart pair (same A_i, same B_j, same voltage) costs N. */
static long dup_penalty(void) {
    long c = 0;
    for (int i = 0; i < B; i++)
        for (int p = 0; p < d; p++)
            for (int q = p + 1; q < d; q++)
                if (sig[p][i] == sig[q][i] && tv[p][i] == tv[q][i]) c++;
    return c * (long)N;
}

/* Unreached pairs from the 2B base vertices, plus duplicate penalty. 0 = valid simple graph. */
static long lift_cost(void) {
    long V = 2L * B * N;
    long c = 0;
    for (int s = 0; s < 2 * B; s++) {
        int src = (s < B) ? s * N + e_id : B * N + (s - B) * N + e_id;
        c += V - lift_ball(src, D);
    }
    return c + dup_penalty();
}

static void set_volt(int p, int i, int g) {
    tv[p][i] = g;
    tinv[p][i] = INV[g];
}

static void recompute_perm_inv(int p) {
    for (int i = 0; i < B; i++) siginv[p][sig[p][i]] = i;
}

static void random_state(void) {
    for (int p = 0; p < d; p++) {
        for (int i = 0; i < B; i++) sig[p][i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[p][i];
            sig[p][i] = sig[p][j];
            sig[p][j] = t;
        }
        recompute_perm_inv(p);
        for (int i = 0; i < B; i++) set_volt(p, i, rndint(N));
    }
}

static void save_state(int bs[MAXDEG][MAXB], int bv[MAXDEG][MAXB]) {
    memcpy(bs, sig, sizeof sig);
    memcpy(bv, tv, sizeof tv);
}

static void load_state(int bs[MAXDEG][MAXB], int bv[MAXDEG][MAXB]) {
    memcpy(sig, bs, sizeof sig);
    memcpy(tv, bv, sizeof tv);
    for (int p = 0; p < d; p++) {
        recompute_perm_inv(p);
        for (int i = 0; i < B; i++) tinv[p][i] = INV[tv[p][i]];
    }
}

/* Simulated annealing with sawtooth reheating. Returns 1 and leaves the best valid state. */
static int anneal(double until) {
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    random_state();
    long cur = lift_cost();
    long bestc = cur;
    static int bsig[MAXDEG][MAXB], btv[MAXDEG][MAXB];
    save_state(bsig, btv);
    double scale = (double)(2L * B * N) / 1000.0;
    if (scale < 1.0) scale = 1.0;
    double temp = scale * T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double ph = (t - start) / span * CYCLES;
            ph = ph - floor(ph);
            temp = scale * T_HI * pow(T_LO / T_HI, ph);
        }
        if (B == 1 || rndint(10) < 8) {
            int p = rndint(d), i = rndint(B);
            int oldg = tv[p][i];
            int g = rndint(N);
            if (g == oldg) continue;
            set_volt(p, i, g);
            long nc = lift_cost();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                set_volt(p, i, oldg);
            }
        } else {
            int p = rndint(d), i = rndint(B), i2 = rndint(B);
            if (i == i2) continue;
            int t = sig[p][i];
            sig[p][i] = sig[p][i2];
            sig[p][i2] = t;
            recompute_perm_inv(p);
            long nc = lift_cost();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = nc;
            } else {
                t = sig[p][i];
                sig[p][i] = sig[p][i2];
                sig[p][i2] = t;
                recompute_perm_inv(p);
            }
        }
        if (cur < bestc) {
            bestc = cur;
            save_state(bsig, btv);
        }
    }
    if (bestc != 0) return 0;
    load_state(bsig, btv);
    return 1;
}

/* Write the current lift as an edge list (deduplicated, A-side enumeration). */
static void record_graph(void) {
    int BN = B * N;
    int m = 0;
    for (int i = 0; i < B; i++)
        for (int g = 0; g < N; g++) {
            int v = i * N + g;
            int nb[MAXDEG];
            int cnt = 0;
            for (int p = 0; p < d; p++) {
                int u = BN + sig[p][i] * N + (int)T[(size_t)g * N + tv[p][i]];
                int dup = 0;
                for (int q = 0; q < cnt; q++)
                    if (nb[q] == u) { dup = 1; break; }
                if (!dup) {
                    nb[cnt++] = u;
                    outE[2 * m] = v;
                    outE[2 * m + 1] = u;
                    m++;
                }
            }
        }
    outN = 2 * BN;
    outM = m;
    bestFound = outN;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* Iterative deepening over a candidate list; each round doubles every slice. */
static void run_phase(Cand *list, int n, double until) {
    double total = until - now();
    if (total < 0.5) return;
    double base = total * 0.02;
    if (base < 0.3) base = 0.3;
    for (int round = 0; round < 8; round++) {
        int tried = 0;
        for (int i = 0; i < n; i++) {
            if (list[i].V <= bestFound) continue;
            double remaining = until - now();
            if (remaining < 0.2) return;
            if (!apply_cand(&list[i])) continue;
            tried = 1;
            double slice = base * (double)(1 << round);
            if (slice > remaining) slice = remaining;
            if (anneal(now() + slice)) {
                if (lift_cost() == 0 && 2L * B * N > bestFound) record_graph();
            }
        }
        if (!tried) return;
        if (until - now() < 0.2) return;
    }
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
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    const int nq = (int)(sizeof qs / sizeof qs[0]);

    /* Phase A: bi-Cayley (B = 1) candidates around the reference, parent-style order. */
    int recHalf = (int)(ref / 2);
    int lowN = (int)(0.87 * (double)recHalf);
    int hiN = (int)(1.13 * (double)recHalf);
    if (hiN > MAXN) hiN = MAXN;
    if (2L * hiN > moore) hiN = (int)(moore / 2);
    if (lowN < 3) lowN = 3;
    int recN = recHalf + 1;

    nGenA = 0;
    for (int qi = 0; qi < nq; qi++)
        for (int psl = 0; psl < 2; psl++) {
            long O = matrix_order(qs[qi], psl);
            if (O >= lowN && O <= hiN && O <= MAXN)
                add_matrix(qs[qi], psl, 1, genA, &nGenA);
        }
    for (int Nv = recN - 1; Nv >= lowN; Nv--) add_meta(Nv, 1, genA, &nGenA);
    for (int Nv = recN; Nv <= hiN; Nv++) add_meta(Nv, 1, genA, &nGenA);

    /* Phase B: multi-orbit lifts with 2*B*N just above the reference. */
    nGenB = 0;
    for (int Bv = 2; Bv <= MAXB; Bv++) {
        long Nlo = (long)ref / (2L * Bv) + 1;
        long Nhi = (long)(1.2 * (double)ref / (2.0 * Bv));
        if (Nhi > MAXN) Nhi = MAXN;
        if (Nlo < 3) Nlo = 3;
        for (long Nv = Nlo; Nv <= Nhi; Nv++) {
            if (2L * Bv * Nv > moore) break;
            add_meta((int)Nv, Bv, genB, &nGenB);
        }
        for (int qi = 0; qi < nq; qi++)
            for (int psl = 0; psl < 2; psl++) {
                long O = matrix_order(qs[qi], psl);
                if (O > MAXN) continue;
                long V = 2L * Bv * O;
                if (V > (long)ref && V <= (long)(1.2 * (double)ref) && V <= moore)
                    add_matrix(qs[qi], psl, Bv, genB, &nGenB);
            }
    }
    qsort(genB, (size_t)nGenB, sizeof(Cand), cmp_cand);

    double mid = now() + 0.6 * (t_end - now());
    run_phase(genA, nGenA, mid);
    run_phase(genB, nGenB, t_end);

    if (outM == 0) { print_complete(); return 0; }
    printf("%d %d\n", outN, outM);
    for (int k = 0; k < outM; k++)
        printf("%d %d\n", outE[2 * k], outE[2 * k + 1]);
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
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, ref], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
