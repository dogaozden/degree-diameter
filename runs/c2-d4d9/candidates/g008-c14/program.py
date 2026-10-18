"""Program: bi-Cayley-style voltage lifts with K base vertices per side over metacyclic and SL/PSL groups.

Construction (new in this version):
  * A lift over a group G of order M with K base vertices per side. Vertices are A_i(x) and B_j(y),
    i < K, j < K, x, y in G, so there are 2KM vertices. Each A_i has d darts, dart (t, i) joins
    A_i(x) to B_{pi_t(i)}(x * g_{t,i}), where each pi_t is a permutation of {0..K-1}.
    Every B_j then has degree d, and the graph is d-regular and bipartite.
  * Left multiplication by G is an automorphism, so diameter <= D holds iff BFS from A_i(e) and
    B_j(e) for every base index reaches all 2KM vertices within D steps.
  * Search: simulated annealing over voltages and permutations, with sawtooth reheating.
    K = 1 recovers the earlier bi-Cayley search.
  * Candidates: (K, group) pairs with 2KM in a window around the reference. Phase 1 secures a
    fallback from the smallest candidates. Phase 2 is successive halving over the survivors,
    with warm restarts from each candidate's best state.

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

#define MAXM 3200
#define MAXK 6
#define MAXD 8
#define MAXV 40000
#define MAXENUM 80000
#define MAXSEL 48
#define NSAFE 14
#define NPASS2 40
#define BIG_COST (1L << 60)
#define CYCLES 3.0

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

/* ------------------------------------------------------------------ groups */

static int M = 0, e_id = 0;
static uint16_t *T = NULL;     /* T[x*M+y] = x*y */
static int INV[MAXM];

static void ensure_table(void) {
    if (!T) T = malloc(sizeof(uint16_t) * (size_t)MAXM * (size_t)MAXM);
}

static void finish_inv(void) {
    for (int x = 0; x < M; x++) {
        INV[x] = -1;
        const uint16_t *row = T + (size_t)x * M;
        for (int y = 0; y < M; y++) {
            if ((int)row[y] == e_id) { INV[x] = y; break; }
        }
    }
}

/* Z_m x|_r Z_n, element (a,b) coded as a*n+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int build_meta(int m, int n, int r) {
    int tot = m * n;
    if (tot > MAXM || tot < 2 || m < 1 || n < 1) return 0;
    ensure_table();
    static int pw[MAXM];
    static int ga[MAXM], gb[MAXM];
    pw[0] = 1 % m;
    for (int b = 1; b < n; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    M = tot;
    for (int x = 0; x < M; x++) { ga[x] = x / n; gb[x] = x % n; }
    for (int x = 0; x < M; x++) {
        int a = ga[x], b = gb[x];
        size_t off = (size_t)x * M;
        for (int y = 0; y < M; y++) {
            int c = ga[y], dd = gb[y];
            int aa = (int)(((long)a + (long)pw[b] * c) % m);
            int bb = (b + dd) % n;
            T[off + y] = (uint16_t)(aa * n + bb);
        }
    }
    e_id = 0;
    finish_inv();
    return 1;
}

/* SL(2,q) or PSL(2,q), q prime. */
static int gq, gpsl;
static int gmat[MAXM][4];
static int idxm[20 * 20 * 20 * 20];

static int canon_key(int a, int b, int c, int e) {
    int q = gq;
    int k = ((a * q + b) * q + c) * q + e;
    if (!gpsl) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    ensure_table();
    gq = q;
    gpsl = psl;
    int ks = q * q * q * q;
    for (int i = 0; i < ks; i++) idxm[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXM) return 0;
                    gmat[cnt][0] = a;
                    gmat[cnt][1] = b;
                    gmat[cnt][2] = c;
                    gmat[cnt][3] = e;
                    idxm[own] = cnt;
                    cnt++;
                }
    M = cnt;
    for (int x = 0; x < M; x++) {
        int a = gmat[x][0], b = gmat[x][1], c = gmat[x][2], e = gmat[x][3];
        size_t off = (size_t)x * M;
        for (int y = 0; y < M; y++) {
            int a2 = gmat[y][0], b2 = gmat[y][1], c2 = gmat[y][2], e2 = gmat[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            T[off + y] = (uint16_t)idxm[canon_key(pa, pb, pc, pe)];
        }
    }
    e_id = idxm[canon_key(1, 0, 0, 1)];
    finish_inv();
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;          /* 0 = metacyclic (m,n,r), 1 = matrix (q,psl) */
    int q, psl, m, n, r;
    int k;             /* base vertices per side */
    int M;             /* group order */
    int V;             /* total vertices 2*k*M */
} Cand;

static const long MQ[6] = {5, 7, 11, 13, 17, 19};
static Cand cand_all[MAXENUM];
static int ncand_all = 0;
static int taken[MAXENUM];
static Cand sel[MAXSEL];
static int nsel = 0;

static void add_cand(const Cand *c) {
    if (ncand_all < MAXENUM) cand_all[ncand_all++] = *c;
}

static void enumerate(long lowV, long hiV) {
    for (int k = 1; k <= MAXK; k++) {
        long step = 2L * k;
        long V0 = ((lowV + step - 1) / step) * step;
        for (long V = V0; V <= hiV; V += step) {
            long Mv = V / step;
            if (Mv < 3 || Mv > MAXM) continue;
            for (int qi = 0; qi < 6; qi++) {
                for (int psl = 0; psl < 2; psl++) {
                    long q = MQ[qi];
                    long o = q * (q * q - 1);
                    if (psl) o /= 2;
                    if (o != Mv) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 1;
                    c.q = (int)q;
                    c.psl = psl;
                    c.k = k;
                    c.M = (int)Mv;
                    c.V = (int)V;
                    add_cand(&c);
                }
            }
            for (long n = 2; n <= Mv / 3; n++) {
                if (Mv % n) continue;
                long m = Mv / n;
                if (m < 3) continue;
                int got = 0;
                for (long r = 2; r < m && got < 2; r++) {
                    if (gcd_l(r, m) != 1) continue;
                    if (powmod_l(r, n, m) != 1 % m) continue;
                    Cand c;
                    memset(&c, 0, sizeof c);
                    c.type = 0;
                    c.m = (int)m;
                    c.n = (int)n;
                    c.r = (int)r;
                    c.k = k;
                    c.M = (int)Mv;
                    c.V = (int)V;
                    add_cand(&c);
                    got++;
                }
            }
        }
    }
}

static void select_cands(long lowV) {
    for (int i = ncand_all - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand t = cand_all[i];
        cand_all[i] = cand_all[j];
        cand_all[j] = t;
    }
    for (int i = 0; i < ncand_all; i++) taken[i] = 0;
    nsel = 0;
    /* a few safe (smaller-order) candidates for a fallback */
    for (int i = 0; i < ncand_all && nsel < NSAFE; i++) {
        if (!taken[i] && cand_all[i].V < lowV) {
            taken[i] = 1;
            sel[nsel++] = cand_all[i];
        }
    }
    /* lifts with K >= 2 first, the main target */
    for (int i = 0; i < ncand_all && nsel < NPASS2; i++) {
        if (!taken[i] && cand_all[i].k >= 2 && cand_all[i].V >= lowV) {
            taken[i] = 1;
            sel[nsel++] = cand_all[i];
        }
    }
    /* anything left */
    for (int i = 0; i < ncand_all && nsel < MAXSEL; i++) {
        if (!taken[i] && cand_all[i].V >= lowV) {
            taken[i] = 1;
            sel[nsel++] = cand_all[i];
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->V > y->V) - (x->V < y->V);
}

/* ------------------------------------------------------------------ lift state */

static int K = 1;
static int PI[MAXD][MAXK];            /* A_i -> B_{PI[t][i]} */
static int PIV[MAXD][MAXK];           /* B_j <- A_{PIV[t][j]} in matching t */
static int GV[MAXD][MAXK];            /* voltage of dart (t, i) */
static int FW[MAXD][MAXK][MAXM];      /* neighbour of A_i(x) via dart (t,i) */
static int RV[MAXD][MAXK][MAXM];      /* neighbour of B_{PI[t][i]}(y) via dart (t,i) */

static int cPI[MAXSEL][MAXD][MAXK];
static int cGV[MAXSEL][MAXD][MAXK];
static int cinit[MAXSEL];
static long ccost[MAXSEL];

static void dart_refresh(int t, int i) {
    int g = GV[t][i];
    int gi = INV[g];
    int j = PI[t][i];
    int base_b = (K + j) * M;
    int base_a = i * M;
    for (int x = 0; x < M; x++) {
        size_t off = (size_t)x * M;
        FW[t][i][x] = base_b + (int)T[off + g];
        RV[t][i][x] = base_a + (int)T[off + gi];
    }
}

static void full_refresh(void) {
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) PIV[t][PI[t][i]] = i;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) dart_refresh(t, i);
}

static void randomize_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) PI[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = PI[t][i];
            PI[t][i] = PI[t][j];
            PI[t][j] = tmp;
        }
        for (int i = 0; i < K; i++) GV[t][i] = rndint(M);
    }
    full_refresh();
}

/* ------------------------------------------------------------------ BFS cost */

static int stamp[MAXV];
static int tick = 0;
static int qv[MAXV];

static int ball(int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int KM = K * M;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < KM) {
                int i = v / M;
                int x = v - i * M;
                for (int t = 0; t < d; t++) {
                    int u = FW[t][i][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - KM;
                int j = w / M;
                int y = w - j * M;
                for (int t = 0; t < d; t++) {
                    int i = PIV[t][j];
                    int u = RV[t][i][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of vertices not reached within D from the 2K base representatives (0 = valid). */
static long cost_now(void) {
    long V = 2L * K * M;
    long c = 0;
    for (int i = 0; i < K; i++) c += V - ball(i * M + e_id);
    for (int j = 0; j < K; j++) c += V - ball((K + j) * M + e_id);
    return c;
}

/* ------------------------------------------------------------------ moves */

typedef struct { int kind, t, i, i2, old; } Undo;

static void apply_swap(int t, int i, int i2) {
    int tmp = PI[t][i];
    PI[t][i] = PI[t][i2];
    PI[t][i2] = tmp;
    PIV[t][PI[t][i]] = i;
    PIV[t][PI[t][i2]] = i2;
    dart_refresh(t, i);
    dart_refresh(t, i2);
}

static void do_move(Undo *u) {
    if (K >= 2 && rndint(4) == 0) {
        int t = rndint(d);
        int i = rndint(K);
        int i2 = rndint(K - 1);
        if (i2 >= i) i2++;
        u->kind = 1;
        u->t = t;
        u->i = i;
        u->i2 = i2;
        apply_swap(t, i, i2);
    } else {
        int t = rndint(d);
        int i = rndint(K);
        u->kind = 0;
        u->t = t;
        u->i = i;
        u->old = GV[t][i];
        int g;
        do g = rndint(M); while (g == GV[t][i]);
        GV[t][i] = g;
        dart_refresh(t, i);
    }
}

static void undo_move(const Undo *u) {
    if (u->kind == 1) {
        apply_swap(u->t, u->i, u->i2);
    } else {
        GV[u->t][u->i] = u->old;
        dart_refresh(u->t, u->i);
    }
}

/* ------------------------------------------------------------------ annealing */

static long last_best = BIG_COST;

/* Anneal from the current state until `until`. Leaves the best state in place.
   Returns 1 if that state has cost 0. */
static int climb(double until) {
    last_best = BIG_COST;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    long V = 2L * K * M;
    double Thi = 0.01 * (double)V;
    if (Thi < 3.0) Thi = 3.0;
    const double Tlo = 0.1;
    long cur = cost_now();
    long bestc = cur;
    static int bP[MAXD][MAXK], bG[MAXD][MAXK];
    memcpy(bP, PI, sizeof PI);
    memcpy(bG, GV, sizeof GV);
    double temp = Thi;
    long it = 0;
    while (cur > 0) {
        if ((++it & 3) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph = ph - floor(ph);
            temp = Thi * pow(Tlo / Thi, ph);
        }
        Undo u;
        do_move(&u);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(bP, PI, sizeof PI);
                memcpy(bG, GV, sizeof GV);
            }
        } else {
            undo_move(&u);
        }
    }
    memcpy(PI, bP, sizeof PI);
    memcpy(GV, bG, sizeof GV);
    full_refresh();
    last_best = bestc;
    return bestc == 0;
}

static int load_sel(int idx) {
    const Cand *c = &sel[idx];
    int ok = (c->type == 0) ? build_meta(c->m, c->n, c->r) : build_matrix(c->q, c->psl);
    if (!ok || M != c->M) return 0;
    K = c->k;
    if (!cinit[idx]) {
        randomize_state();
    } else {
        memcpy(PI, cPI[idx], sizeof PI);
        memcpy(GV, cGV[idx], sizeof GV);
        full_refresh();
    }
    return 1;
}

static void save_sel(int idx) {
    memcpy(cPI[idx], PI, sizeof PI);
    memcpy(cGV[idx], GV, sizeof GV);
    cinit[idx] = 1;
}

/* ------------------------------------------------------------------ output */

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void output_graph(void) {
    int KM = K * M;
    int V = 2 * KM;
    long E = 0;
    for (int v = 0; v < KM; v++) {
        int i = v / M;
        int x = v - i * M;
        for (int t = 0; t < d; t++) {
            int u = FW[t][i][x], dup = 0;
            for (int s = 0; s < t; s++)
                if (FW[s][i][x] == u) { dup = 1; break; }
            if (!dup) E++;
        }
    }
    printf("%d %ld\n", V, E);
    for (int v = 0; v < KM; v++) {
        int i = v / M;
        int x = v - i * M;
        for (int t = 0; t < d; t++) {
            int u = FW[t][i][x], dup = 0;
            for (int s = 0; s < t; s++)
                if (FW[s][i][x] == u) { dup = 1; break; }
            if (!dup) printf("%d %d\n", v, u);
        }
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

    if (d < 1 || d > MAXD || D < 2) { print_complete(); return 0; }
    ensure_table();

    long moore = moore_bound();
    long lowV = (long)(0.85 * (double)ref);
    long rangeLo = (long)(0.6 * (double)ref);
    if (rangeLo < 4) rangeLo = 4;
    if (lowV < rangeLo) lowV = rangeLo;
    long hiV = (long)(1.15 * (double)ref);
    if (hiV > moore) hiV = moore;
    if (hiV > MAXV) hiV = MAXV;
    hiV -= hiV % 2;
    if (hiV < rangeLo) { print_complete(); return 0; }

    enumerate(rangeLo, hiV);
    if (ncand_all == 0) { print_complete(); return 0; }
    select_cands(lowV);
    if (nsel == 0) { print_complete(); return 0; }
    qsort(sel, (size_t)nsel, sizeof(Cand), cmp_cand);

    static int alive[MAXSEL];
    for (int i = 0; i < nsel; i++) {
        cinit[i] = 0;
        ccost[i] = BIG_COST;
        alive[i] = 0;
    }

    int bestIdx = -1;
    long bestV = 0;

    /* Phase 1: secure a fallback, smallest orders first. */
    double p1_end = t0 + usable * 0.3;
    for (int i = 0; i < nsel; i++) {
        if (now() > p1_end) break;
        if (sel[i].V <= bestV) continue;
        if (!load_sel(i)) continue;
        double rem = t_end - now();
        double s = usable * 0.015;
        if (s > rem) s = rem;
        if (s < 0.05) break;
        int ok = climb(now() + s);
        save_sel(i);
        if (last_best < ccost[i]) ccost[i] = last_best;
        if (ok) {
            bestIdx = i;
            bestV = sel[i].V;
            break;
        }
    }

    /* Phase 2: successive halving over candidates above bestV. */
    for (int i = 0; i < nsel; i++) alive[i] = (sel[i].V > bestV) ? 1 : 0;
    int done = 0;
    while (!done) {
        double rem = t_end - now();
        if (rem < 0.1) break;
        int na = 0;
        for (int i = 0; i < nsel; i++) {
            if (alive[i] && sel[i].V <= bestV) alive[i] = 0;
            if (alive[i]) na++;
        }
        if (na == 0) break;
        double s = (na == 1) ? rem : rem * 0.5 / na;
        if (s < 0.05) s = 0.05;
        for (int i = 0; i < nsel && !done; i++) {
            if (!alive[i]) continue;
            if (sel[i].V <= bestV) { alive[i] = 0; continue; }
            rem = t_end - now();
            if (rem < 0.05) { done = 1; break; }
            double sl = s < rem ? s : rem;
            if (!load_sel(i)) { alive[i] = 0; continue; }
            int ok = climb(now() + sl);
            save_sel(i);
            if (last_best < ccost[i]) ccost[i] = last_best;
            if (ok) {
                bestIdx = i;
                bestV = sel[i].V;
                alive[i] = 0;
            }
        }
        /* keep the better half of the live candidates, ranked by the lowest cost reached */
        int arr[MAXSEL], m = 0;
        for (int i = 0; i < nsel; i++)
            if (alive[i] && sel[i].V > bestV) arr[m++] = i;
        if (m > 1) {
            for (int a = 1; a < m; a++) {
                int x = arr[a];
                int b = a - 1;
                while (b >= 0 && ccost[arr[b]] > ccost[x]) {
                    arr[b + 1] = arr[b];
                    b--;
                }
                arr[b + 1] = x;
            }
            int keep = (m + 1) / 2;
            for (int a = keep; a < m; a++) alive[arr[a]] = 0;
        }
    }

    if (bestIdx < 0) { print_complete(); return 0; }
    if (!load_sel(bestIdx)) { print_complete(); return 0; }
    if (cost_now() != 0) { print_complete(); return 0; }
    output_graph();
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


def default_ref(d, D):
    """Reference order used to centre the search window when no record is known."""
    return max(6, lib.moore_bound(d, D) // 2)


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
            ref = REF_VERTICES.get((d, D), default_ref(d, D))
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
