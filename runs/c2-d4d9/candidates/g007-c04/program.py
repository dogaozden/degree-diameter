"""Program: merged voltage-lift search over SL/PSL and metacyclic groups.

Merges the two parents:
  * Base structure (from both parents): P base vertices per side (P <= 8) and d colour
    permutations pm[c]. Slot t = c*P + i is the dart A-row i -> B-row pm[c][i]. Each dart
    carries a voltage g, and the lift joins A(i,x) to B(j, x*g). Darts sharing (i,j) get
    distinct voltages, so the lift is simple, bipartite and d-regular on 2*P*N vertices.
    Left multiplication by G is an automorphism, so diameter <= D iff BFS from A(i,e) and
    B(j,e) for all i, j reaches everything within D steps.
  * Search: simulated annealing with sawtooth reheating and an elite state per cycle
    (from the voltage parent), with joint moves that swap two rows of one colour
    permutation (from the joint-base parent). Row swaps change the base multigraph itself.
  * Candidate order: the exact record order first, then orders just above the record in
    ascending order, so beating the record is attempted early. Orders below the best found
    are skipped. A fixed SL(2,13) floor (4368 vertices) is tried first as a safety net.

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
#define MAXP 8
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 200000
#define IDXM_CAP 100000
#define T_HI 4.0
#define T_LO 0.2
#define CYCLES 4.0
#define PPERM 0.2
#define MAIN_FRAC 0.04
#define FLOOR_FRAC 0.10

static int d, D;
static long MOORE, REFV;
static int useref;
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

static int N = 1, e_id = 0;
static uint16_t T[MAXN * MAXN];   /* T[x*N+y] = x*y */
static int INV[MAXN];
static int pw_tmp[MAXN];
static int qg, psl_g;
static int gmat[MAXN][4];
static int idxm[IDXM_CAP];

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
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    N = (int)n;
    pw_tmp[0] = 1 % m;
    for (int b = 1; b < k; b++) pw_tmp[b] = (int)((long)pw_tmp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + pw_tmp[b] * c) % m;
            int bb = (b + dd) % k;
            T[(size_t)x * N + y] = (uint16_t)(aa * k + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return 1;
}

static int canon_key(int a, int b, int c, int e) {
    int q = qg;
    int k = ((a * q + b) * q + c) * q + e;
    if (!psl_g) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc2 = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc2) * q + ne;
    return k < kn ? k : kn;
}

/* SL(2,q) or PSL(2,q), q prime. */
static int build_matrix(int q, int psl) {
    qg = q;
    psl_g = psl;
    int ks = q * q * q * q;
    if (ks > IDXM_CAP) return 0;
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
    int type;      /* 0 = metacyclic, 1 = matrix */
    int q, psl, m, k, r, N, P;
    long V;        /* total vertices = 2 * P * N */
    double key;    /* smaller = tried earlier */
} Cand;

static Cand CAND[MAXCAND];
static int nc = 0;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->key < y->key) return -1;
    if (x->key > y->key) return 1;
    return 0;
}

static void push_cand(const Cand *c) {
    if (nc < MAXCAND) CAND[nc++] = *c;
}

static void gen_candidates(long lowV, long hiV) {
    static const int qs[] = {5, 7, 11, 13, 17};
    nc = 0;
    for (int Pp = 1; Pp <= MAXP; Pp++) {
        for (unsigned qi = 0; qi < sizeof qs / sizeof qs[0]; qi++) {
            for (int psl = 0; psl < 2; psl++) {
                long q = qs[qi];
                long o = q * (q * q - 1);
                if (psl) o /= 2;
                long V = 2L * Pp * o;
                if (o > MAXN || V <= lowV || V > hiV || V > MOORE) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 1;
                c.q = (int)q;
                c.psl = psl;
                c.N = (int)o;
                c.P = Pp;
                c.V = V;
                push_cand(&c);
            }
        }
    }
    for (long Nv = 3; Nv <= MAXN && 2L * Nv <= hiV; Nv++) {
        int any = 0;
        for (int Pp = 1; Pp <= MAXP && !any; Pp++) {
            long V = 2L * Pp * Nv;
            if (V > lowV && V <= hiV && V <= MOORE) any = 1;
        }
        if (!any) continue;
        for (long k = 2; k <= Nv / 3; k++) {
            if (Nv % k) continue;
            long m = Nv / k;
            if (m < 3) continue;
            int got = 0;
            for (long r = 2; r < m && r < 400 && got < 3; r++) {
                if (gcd_l(r, m) != 1 || powmod_l(r, k, m) != 1) continue;
                got++;
                for (int Pp = 1; Pp <= MAXP; Pp++) {
                    long V = 2L * Pp * Nv;
                    if (V <= lowV || V > hiV || V > MOORE) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 0;
                    c.m = (int)m;
                    c.k = (int)k;
                    c.r = (int)r;
                    c.N = (int)Nv;
                    c.P = Pp;
                    c.V = V;
                    push_cand(&c);
                }
            }
        }
    }
    for (int i = 0; i < nc; i++) {
        Cand *c = &CAND[i];
        double pen = (c->type == 0) ? 0.5 : 0.0;
        if (useref) {
            if (c->V == REFV) c->key = -1000.0;
            else if (c->V > REFV) c->key = (double)(c->V - REFV);
            else c->key = 1000.0 + (double)(REFV - c->V);
        } else {
            c->key = -(double)c->V;
        }
        c->key += pen + 0.01 * rnd01();
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

/* ------------------------------------------------------------------ base shape */

static int P = 1, half = 1, nd = 0;
static int pm[MAXDEG][MAXP];          /* pm[c][i] = B-row hit by A-row i in colour c */
static int dI[MAXDART], dJ[MAXDART], vol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];
static int FW[MAXDART][MAXN];         /* FW[t][x] = x * g_t        (A side -> B side) */
static int BW[MAXDART][MAXN];         /* BW[t][y] = y * g_t^{-1}   (B side -> A side) */

/* Slot t = c*P + i. Fixes dI and dA for a given P; uses the current N. */
static void set_shape(int Pn) {
    P = Pn;
    half = P * N;
    nd = d * P;
    for (int t = 0; t < nd; t++) dI[t] = t % P;
    for (int i = 0; i < P; i++)
        for (int c = 0; c < d; c++) dA[i][c] = c * P + i;
}

/* Recompute dJ and dB from pm. */
static void sync_base(void) {
    int cb[MAXP];
    memset(cb, 0, sizeof cb);
    for (int c = 0; c < d; c++)
        for (int i = 0; i < P; i++) {
            int t = c * P + i, j = pm[c][i];
            dJ[t] = j;
            dB[j][cb[j]++] = t;
        }
}

static void set_dart(int t) {
    int g = vol[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        FW[t][x] = (int)T[(size_t)x * N + g];
        BW[t][x] = (int)T[(size_t)x * N + gi];
    }
}

/* True if dart t with voltage g clashes with a dart s < upto (s != t) on the same (i,j). */
static int conflict_with(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && vol[s] == g) return 1;
    return 0;
}

/* Random colour permutations, then distinct voltages per (i,j). */
static int gen_base(void) {
    int perm[MAXP];
    for (int c = 0; c < d; c++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < P; i++) pm[c][i] = perm[i];
    }
    sync_base();
    for (int t = 0; t < nd; t++) {
        int g = 0, tries = 0;
        do {
            g = rndint(N);
            tries++;
        } while (conflict_with(t, g, t) && tries < 100000);
        if (tries >= 100000) return 0;
        vol[t] = g;
    }
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok || N != c->N) return 0;
    set_shape(c->P);
    return 1;
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
            if (v < half) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int t = dA[i][k];
                    int u = half + dJ[t] * N + FW[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int t = dB[j][k];
                    int u = dI[t] * N + BW[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of vertices not reached within D from A(i,e) and B(j,e); 0 = valid. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        c += (long)(2 * half - ball(i * N + e_id, D));
    for (int j = 0; j < P; j++)
        c += (long)(2 * half - ball(half + j * N + e_id, D));
    return c;
}

/* ------------------------------------------------------------------ elite state */

static int epm[MAXDEG][MAXP];
static int evol[MAXDART];
static long ebest_c;

static void save_elite(long c) {
    ebest_c = c;
    memcpy(epm, pm, sizeof pm);
    memcpy(evol, vol, sizeof(int) * (size_t)nd);
}

static void load_elite(void) {
    memcpy(pm, epm, sizeof pm);
    memcpy(vol, evol, sizeof(int) * (size_t)nd);
    sync_base();
    for (int t = 0; t < nd; t++) set_dart(t);
}

/* ------------------------------------------------------------------ search */

/* Annealing over voltages and row swaps on the current group and P.
   Returns 1 with a valid lift (cost 0) left in place, else 0. */
static int climb(double until) {
    if (!gen_base()) return 0;
    long cur = cost_now();
    if (cur == 0) return 1;
    save_elite(cur);
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    int cyc_prev = 0;
    double temp = T_HI;
    long it = 0;
    for (;;) {
        if ((++it & 15) == 0) {
            double tm = now();
            if (tm >= until) return 0;
            double ph = (tm - start) / span * CYCLES;
            int cyc = (int)floor(ph);
            double fr = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, fr);
            if (cyc != cyc_prev) {
                cyc_prev = cyc;
                if (rnd01() < 0.25) {
                    if (!gen_base()) return 0;
                    cur = cost_now();
                    if (cur == 0) return 1;
                    save_elite(cur);
                } else {
                    load_elite();
                    cur = ebest_c;
                }
            }
        }
        if (P >= 2 && rnd01() < PPERM) {
            int c = rndint(d);
            int i1 = rndint(P), i2 = rndint(P - 1);
            if (i2 >= i1) i2++;
            int j1 = pm[c][i1], j2 = pm[c][i2];
            int t1 = c * P + i1, t2 = c * P + i2;
            pm[c][i1] = j2;
            pm[c][i2] = j1;
            sync_base();
            if (conflict_with(t1, vol[t1], nd) || conflict_with(t2, vol[t2], nd)) {
                pm[c][i1] = j1;
                pm[c][i2] = j2;
                sync_base();
                continue;
            }
            long c2 = cost_now();
            long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = c2;
            } else {
                pm[c][i1] = j1;
                pm[c][i2] = j2;
                sync_base();
            }
        } else {
            int t = rndint(nd);
            int old = vol[t];
            int g = rndint(N);
            if (g == old || conflict_with(t, g, nd)) continue;
            vol[t] = g;
            set_dart(t);
            long c2 = cost_now();
            long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
                cur = c2;
            } else {
                vol[t] = old;
                set_dart(t);
            }
        }
        if (cur == 0) return 1;
        if (cur < ebest_c) save_elite(cur);
    }
}

/* ------------------------------------------------------------------ best so far */

static int have = 0;
static long bestV = 0;
static Cand bestc;
static int spm[MAXDEG][MAXP];
static int svol[MAXDART];

static void snapshot(const Cand *c) {
    have = 1;
    bestV = c->V;
    bestc = *c;
    memcpy(spm, pm, sizeof pm);
    memcpy(svol, vol, sizeof(int) * (size_t)nd);
}

static int restore(void) {
    if (!apply_cand(&bestc)) return 0;
    memcpy(pm, spm, sizeof pm);
    memcpy(vol, svol, sizeof(int) * (size_t)nd);
    sync_base();
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    printf("%d %d\n", 2 * half, nd * N);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int k = 0; k < d; k++) {
                int t = dA[i][k];
                printf("%d %d\n", i * N + x, half + dJ[t] * N + FW[t][x]);
            }
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

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    MOORE = moore_bound();
    long lowV, hiV;
    if (ref > 0) {
        useref = 1;
        REFV = ref;
        lowV = (long)(0.87 * (double)ref);
        if (lowV < 2L * d) lowV = 2L * d;
        hiV = (long)(1.25 * (double)ref);
        if (hiV > MOORE) hiV = MOORE;
    } else {
        useref = 0;
        REFV = 0;
        lowV = 2L * d;
        hiV = MOORE;
    }
    if (hiV > 2L * MAXP * MAXN) hiV = 2L * MAXP * MAXN;
    gen_candidates(lowV, hiV);

    /* Floor: SL(2,13) with one base vertex, 4368 vertices. */
    Cand fb;
    memset(&fb, 0, sizeof fb);
    fb.type = 1;
    fb.q = 13;
    fb.psl = 0;
    fb.N = 2184;
    fb.P = 1;
    fb.V = 2L * 2184;
    if (fb.V > lowV && fb.V <= hiV && apply_cand(&fb)) {
        double rem = t_end - now();
        double slice = usable * FLOOR_FRAC;
        if (slice > rem) slice = rem;
        if (slice > 0.0 && climb(now() + slice)) snapshot(&fb);
    }

    /* Main pass: record order first, then larger orders ascending. */
    for (int i = 0; i < nc; i++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand *c = &CAND[i];
        if (c->V <= bestV) continue;
        if (!apply_cand(c)) continue;
        double slice = usable * MAIN_FRAC;
        if (slice > rem) slice = rem;
        if (slice <= 0.0) break;
        if (climb(now() + slice)) snapshot(c);
    }

    if (!have || !restore() || cost_now() != 0) { print_complete(); return 0; }
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            ref = REF_VERTICES.get((d, D), 0)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
