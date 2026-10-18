"""Program: multi-orbit lift search (bold change from the bi-Cayley parent).

Construction:
  * Base graph with P vertices per side (P = 1 or 2). Dart slot k joins block A_i to block
    B_{sig_k(i)} with voltage g_{i,k} in a finite group G, where each sig_k is a permutation.
    Each vertex has degree d, so the lift is d-regular and bipartite with 2*P*N vertices.
  * Lift: A_{i,x} ~ B_{sig_k(i), x*g_{i,k}}. Left multiplication is an automorphism, so the
    diameter holds iff BFS from A_{i,e} and B_{j,e} for all i, j reaches all 2PN vertices in D.
  * P = 1 is exactly the old bi-Cayley graph, so it serves as the fallback. P = 2 is the new
    search space: 2d voltages plus block permutations, with more freedom at a smaller group
    order (N about ref/4 instead of ref/2).

Search: simulated annealing over voltages and permutations, with sawtooth reheating. Groups come
from metacyclic Z_m x| Z_k and SL(2,q)/PSL(2,q). Candidates are sampled evenly from each order
window.

Safety: the C engine prints K_{d,d} if nothing is found. Python checks the output with
lib.is_valid and keeps the best valid graph.
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
#define MAXP 3
#define MAXD 8
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 6000
#define MAXSLICE 6.0
#define BIGC 1000000000000L

#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0

static int d, D, P = 1;
static double t_end;
static long moore_g = 0;

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

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;   /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N;
} Cand;

static int apply_cand(const Cand *c) {
    if (c->type == 0) return build_meta(c->m, c->k, c->r);
    return build_matrix(c->q, c->psl);
}

static void add_meta(int Nval, Cand *arr, int *cnt) {
    for (int k = 2; k <= Nval / 3 && *cnt < MAXCAND; k++) {
        if (Nval % k) continue;
        int m = Nval / k;
        if (m < 3) continue;
        int got = 0;
        for (int r = 2; r < m && got < 2 && *cnt < MAXCAND; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 0;
            c.m = m;
            c.k = k;
            c.r = r;
            c.N = Nval;
            arr[(*cnt)++] = c;
            got++;
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->N > y->N) - (x->N < y->N);
}

static void gen_cands(int lo, int hi, Cand *arr, int *cnt) {
    *cnt = 0;
    static const int qs[] = {5, 7, 11, 13, 17, 19};
    for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = qs[qi];
            long o = q * (q * q - 1);
            if (psl) o /= 2;
            if (o < lo || o > hi || o > MAXN) continue;
            if (*cnt >= MAXCAND) break;
            Cand c;
            memset(&c, 0, sizeof c);
            c.type = 1;
            c.q = (int)q;
            c.psl = psl;
            c.N = (int)o;
            arr[(*cnt)++] = c;
        }
    }
    for (int Nv = lo; Nv <= hi && *cnt < MAXCAND - 8; Nv++) add_meta(Nv, arr, cnt);
    qsort(arr, (size_t)*cnt, sizeof(Cand), cmp_cand);
}

/* ------------------------------------------------------------------ lifted state */

/* gv[i][k]: voltage of dart slot k at block i.
   sig[k][i]: target block of that dart (a permutation of 0..P-1 for each k).
   sinv[k][j]: block i with sig[k][i] = j.
   Rf[i][k][x] = x*g,  Rb[i][k][y] = y*g^{-1}. */
static int gv[MAXP][MAXD];
static int sig[MAXD][MAXP];
static int sinv[MAXD][MAXP];
static int Rf[MAXP][MAXD][MAXN];
static int Rb[MAXP][MAXD][MAXN];

static void set_volt(int i, int k) {
    int g = gv[i][k], gi = INV[g];
    for (int x = 0; x < N; x++) {
        Rf[i][k][x] = (int)T[(size_t)x * N + g];
        Rb[i][k][x] = (int)T[(size_t)x * N + gi];
    }
}

static void fix_sinv(int k) {
    for (int i = 0; i < P; i++) sinv[k][sig[k][i]] = i;
}

static void random_perm(int *p) {
    for (int i = 0; i < P; i++) p[i] = i;
    for (int i = P - 1; i > 0; i--) {
        int r = rndint(i + 1);
        int t = p[i];
        p[i] = p[r];
        p[r] = t;
    }
}

static void set_all(void) {
    for (int k = 0; k < d; k++) fix_sinv(k);
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) set_volt(i, k);
}

static void randomize_state(void) {
    for (int k = 0; k < d; k++) random_perm(sig[k]);
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) gv[i][k] = rndint(N);
    set_all();
}

/* Two darts from the same block i to the same target block with equal voltage give a
   repeated edge, so that state is rejected with a huge cost. */
static int dup_bad(void) {
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++)
            for (int k2 = 0; k2 < k; k2++)
                if (sig[k][i] == sig[k2][i] && gv[i][k] == gv[i][k2]) return 1;
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
    int PN = P * N;
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
                    int u = PN + sig[k][i] * N + Rf[i][k][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - PN;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int i = sinv[k][j];
                    int u = i * N + Rb[i][k][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertices unreached within D from all 2P base sources (0 = valid). */
static long cost_now(void) {
    if (dup_bad()) return BIGC;
    int V = 2 * P * N, PN = P * N;
    long c = 0;
    for (int i = 0; i < P; i++) c += (long)(V - ball(i * N + e_id, D));
    for (int j = 0; j < P; j++) c += (long)(V - ball(PN + j * N + e_id, D));
    return c;
}

/* ------------------------------------------------------------------ annealing */

static int bgv[MAXP][MAXD], bsig[MAXD][MAXP];

static int accept(long delta, double temp) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / temp);
}

static int climb(double until) {
    if (N < 3) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize_state();
    long cur = cost_now();
    long bestc = cur;
    memcpy(bgv, gv, sizeof gv);
    memcpy(bsig, sig, sizeof sig);
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
        if (P > 1 && rndint(8) == 0) {
            int k = rndint(d);
            int old[MAXP];
            memcpy(old, sig[k], sizeof old);
            random_perm(sig[k]);
            fix_sinv(k);
            long nc = cost_now();
            if (accept(nc - cur, temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(bgv, gv, sizeof gv);
                    memcpy(bsig, sig, sizeof sig);
                }
            } else {
                memcpy(sig[k], old, sizeof old);
                fix_sinv(k);
            }
        } else {
            int i = rndint(P), k = rndint(d);
            int old = gv[i][k];
            gv[i][k] = rndint(N);
            set_volt(i, k);
            long nc = cost_now();
            if (accept(nc - cur, temp)) {
                cur = nc;
                if (cur < bestc) {
                    bestc = cur;
                    memcpy(bgv, gv, sizeof gv);
                    memcpy(bsig, sig, sizeof sig);
                }
            } else {
                gv[i][k] = old;
                set_volt(i, k);
            }
        }
    }
    if (bestc != 0) return 0;
    memcpy(gv, bgv, sizeof gv);
    memcpy(sig, bsig, sizeof sig);
    set_all();
    return 1;
}

/* ------------------------------------------------------------------ phases */

static long bestTot = 0;
static int bestP = 1;
static Cand bestCand;
static int bestGV[MAXP][MAXD], bestSIG[MAXD][MAXP];

static void run_phase(int Pv, const Cand *arr, int na, double deadline, int maxs) {
    int ns = na < maxs ? na : maxs;
    for (int s = 0; s < ns; s++) {
        int idx = (int)((long)s * na / ns);
        const Cand *c = &arr[idx];
        double remaining = deadline - now();
        if (remaining < 0.2) break;
        if (!apply_cand(c)) continue;
        if (2L * Pv * N <= bestTot) continue;
        if (2L * Pv * N > moore_g) continue;
        P = Pv;
        double slice = remaining / (double)(ns - s);
        if (slice > MAXSLICE) slice = MAXSLICE;
        if (climb(now() + slice)) {
            long tot = 2L * Pv * N;
            if (tot > bestTot) {
                bestTot = tot;
                bestP = Pv;
                bestCand = *c;
                memcpy(bestGV, gv, sizeof gv);
                memcpy(bestSIG, sig, sizeof sig);
            }
        }
    }
}

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
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }

    moore_g = moore_bound();

    /* Windows: P=1 has total 2N near ref; P=2 has total 4N near ref. */
    double rh = (double)ref / 2.0, rq = (double)ref / 4.0;
    int lo1 = (int)(0.87 * rh), hi1 = (int)(1.13 * rh);
    int lo2 = (int)(0.80 * rq), hi2 = (int)(1.13 * rq);
    if (hi1 > MAXN) hi1 = MAXN;
    if (hi1 > moore_g / 2) hi1 = (int)(moore_g / 2);
    if (hi2 > MAXN) hi2 = MAXN;
    if (hi2 > moore_g / 4) hi2 = (int)(moore_g / 4);
    if (lo1 < 3) lo1 = 3;
    if (lo2 < 3) lo2 = 3;

    static Cand cands[MAXCAND];
    int na = 0;

    /* Phase 1: bi-Cayley (P=1) fallback, same as the parent window. */
    gen_cands(lo1, hi1, cands, &na);
    run_phase(1, cands, na, t0 + usable * 0.30, 12);

    /* Phase 2: two base vertices per side (P=2), the new multi-orbit search. */
    gen_cands(lo2, hi2, cands, &na);
    run_phase(2, cands, na, t_end, 40);

    if (bestTot == 0) { print_complete(); return 0; }
    P = bestP;
    if (!apply_cand(&bestCand)) { print_complete(); return 0; }
    memcpy(gv, bestGV, sizeof gv);
    memcpy(sig, bestSIG, sizeof sig);
    set_all();
    if (cost_now() != 0) { print_complete(); return 0; }

    int PN = P * N;
    printf("%d %ld\n", 2 * PN, (long)PN * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", i * N + x, PN + sig[k][i] * N + Rf[i][k][x]);
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
    # Leave margin for the one-time C compile, which runs outside the subprocess timeout.
    budget = 0.82 * time_limit - 2.0 - (time.monotonic() - t0)
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
