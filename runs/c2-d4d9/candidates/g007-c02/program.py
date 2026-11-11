"""Program: two-stage search for bipartite graphs with max degree d and diameter D.

Stage 1 (lift engine): the voltage-lift search from the parent program. It builds a
structured d-regular bipartite lift and returns it as a valid graph.

Stage 2 (growth engine, new): starts from the stage-1 graph and repeatedly adds two
vertices x (side A) and y (side B). Take d edges (a_i, b_i) with distinct a_i and
distinct b_i. Replace each with (x, b_i) and add (a_i, y). Degrees of old vertices are
kept, and x and y get degree d. Then simulated annealing with 2-switches
(a1,b1),(a2,b2) -> (a1,b2),(a2,b1) repairs the diameter. The cost is the number of
unreached (source, vertex) pairs within D, over a sampled set of sources. Whenever the
sampled cost reaches 0, a full all-sources check runs, and only a fully verified graph
is saved as a snapshot and grown again.

Safety: each stage returns only graphs that lib.is_valid accepts. If a stage fails, the
previous valid graph is kept, and the program falls back to the known start or K_{d,d}.
"""
import time

import lib

C_LIFT = r'''
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
#define MAXCAND 150000
#define IDXM_CAP 100000
#define T_HI 4.0
#define T_LO 0.2
#define CYCLES 4.0

static int d, D;
static long MOORE, REFV;
static double t_end, usable;

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
    double key;    /* priority: distance from the target order */
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
    for (long Nv = 3; Nv <= MAXN; Nv++) {
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
            for (long r = 2; r < m && got < 2; r++) {
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
        CAND[i].key = fabs((double)CAND[i].V - (double)(REFV + 1))
                    + 0.5 * (double)(1 - CAND[i].type);
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

static int P = 1, half = 1, nd = 0;

static int apply_cand(const Cand *c) {
    int ok = (c->type == 0) ? build_meta(c->m, c->k, c->r) : build_matrix(c->q, c->psl);
    if (!ok || N != c->N) return 0;
    P = c->P;
    half = P * N;
    return 1;
}

/* ------------------------------------------------------------------ voltage lift */

static int dI[MAXDART], dJ[MAXDART], vol[MAXDART], evol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];
static int FW[MAXDART][MAXN];   /* FW[t][x] = x * g_t        (A side -> B side) */
static int BW[MAXDART][MAXN];   /* BW[t][y] = y * g_t^{-1}   (B side -> A side) */

static void set_dart(int t) {
    int g = vol[t], gi = INV[g];
    for (int x = 0; x < N; x++) {
        FW[t][x] = (int)T[(size_t)x * N + g];
        BW[t][x] = (int)T[(size_t)x * N + gi];
    }
}

static void build_lists(void) {
    int ca[MAXP], cb[MAXP];
    memset(ca, 0, sizeof ca);
    memset(cb, 0, sizeof cb);
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t];
        dA[i][ca[i]++] = t;
        dB[j][cb[j]++] = t;
    }
}

/* True if dart t with voltage g clashes with another dart s < upto on the same (i,j). */
static int conflict(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && vol[s] == g) return 1;
    return 0;
}

static int gen_base(void) {
    int M[MAXP][MAXP];
    int perm[MAXP];
    memset(M, 0, sizeof M);
    for (int c = 0; c < d; c++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < P; i++) M[i][perm[i]]++;
    }
    nd = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++) {
            if (M[i][j] > N) return 0;
            for (int c = 0; c < M[i][j]; c++) {
                dI[nd] = i;
                dJ[nd] = j;
                nd++;
            }
        }
    build_lists();
    for (int t = 0; t < nd; t++) {
        int g, tries = 0;
        do {
            g = rndint(N);
            tries++;
        } while (conflict(t, g, t) && tries < 100000);
        if (tries >= 100000) return 0;
        vol[t] = g;
    }
    for (int t = 0; t < nd; t++) set_dart(t);
    return 1;
}

static void save_elite(void) { memcpy(evol, vol, sizeof(int) * (size_t)nd); }

static void load_elite(void) {
    memcpy(vol, evol, sizeof(int) * (size_t)nd);
    for (int t = 0; t < nd; t++) set_dart(t);
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

/* Number of vertices not reached within D from every A(i,e) and B(j,e); 0 = valid. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        c += (long)(2 * half - ball(i * N + e_id, D));
    for (int j = 0; j < P; j++)
        c += (long)(2 * half - ball(half + j * N + e_id, D));
    return c;
}

/* ------------------------------------------------------------------ search */

/* Annealing over voltages on a fresh base; returns 1 with a valid lift left in place. */
static int climb(double until) {
    if (!gen_base()) return 0;
    long cur = cost_now();
    if (cur == 0) return 1;
    long best_c = cur;
    save_elite();
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
                    best_c = cur;
                    save_elite();
                } else {
                    load_elite();
                    cur = best_c;
                }
            }
        }
        int tn = rndint(nd);
        int old = vol[tn];
        int g = rndint(N);
        if (g == old || conflict(tn, g, nd)) continue;
        vol[tn] = g;
        set_dart(tn);
        long c2 = cost_now();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = c2;
            if (cur == 0) return 1;
            if (cur < best_c) {
                best_c = cur;
                save_elite();
            }
        } else {
            vol[tn] = old;
            set_dart(tn);
        }
    }
}

/* ------------------------------------------------------------------ best so far */

static int have = 0;
static long bestV = 0;
static Cand bestc;
static int sP, sN, snd;
static int sdI[MAXDART], sdJ[MAXDART], svol[MAXDART];

static void snapshot(const Cand *c) {
    have = 1;
    bestV = c->V;
    bestc = *c;
    sP = P;
    sN = N;
    snd = nd;
    memcpy(sdI, dI, sizeof(int) * (size_t)nd);
    memcpy(sdJ, dJ, sizeof(int) * (size_t)nd);
    memcpy(svol, vol, sizeof(int) * (size_t)nd);
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
    usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG || D < 2) { print_complete(); return 0; }

    MOORE = moore_bound();
    if (ref <= 0) ref = 2L * d;
    REFV = ref;

    long lowV = (long)(0.87 * (double)ref);
    if (lowV < 2L * d) lowV = 2L * d;
    long hiV = (long)(1.25 * (double)ref);
    if (hiV > MOORE) hiV = MOORE;
    gen_candidates(lowV, hiV);

    /* Floor: SL(2,13), one base vertex, 4368 vertices for d = 4. */
    Cand fb;
    memset(&fb, 0, sizeof fb);
    fb.type = 1;
    fb.q = 13;
    fb.psl = 0;
    fb.N = 2184;
    fb.P = 1;
    fb.V = 2L * 2184;
    if (fb.V > lowV && fb.V <= hiV && fb.V <= MOORE && apply_cand(&fb)) {
        double rem = t_end - now();
        double slice = usable * 0.12;
        if (slice > rem) slice = rem;
        if (slice > 0.0 && climb(now() + slice)) snapshot(&fb);
    }

    /* Main pass: candidates ordered by distance of 2PN from the target. */
    for (int i = 0; i < nc; i++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand *c = &CAND[i];
        if (c->V <= bestV) continue;
        if (!apply_cand(c)) continue;
        double slice = usable * 0.05;
        if (slice > rem) slice = rem;
        if (slice <= 0.0) break;
        if (climb(now() + slice)) snapshot(c);
    }

    if (!have) { print_complete(); return 0; }
    if (!apply_cand(&bestc)) { print_complete(); return 0; }
    nd = snd;
    memcpy(dI, sdI, sizeof(int) * (size_t)nd);
    memcpy(dJ, sdJ, sizeof(int) * (size_t)nd);
    memcpy(vol, svol, sizeof(int) * (size_t)nd);
    build_lists();
    for (int t = 0; t < nd; t++) set_dart(t);
    if (cost_now() != 0) { print_complete(); return 0; }
    print_graph();
    return 0;
}
'''

C_GROW = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 20000
#define MAXD 8
#define MAXE (MAXV * MAXD / 2 + 8192)
#define NSRC 24
#define T_HI 2.0
#define T_LO 0.05

static int d, D;
static long MOORE;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
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

/* Graph state: edge k joins A-vertex EA[k] and B-vertex EB[k]. */
static int n = 0, m = 0;
static int EA[MAXE], EB[MAXE];
static int adj[MAXV][MAXD];
static int deg[MAXV];
static int side[MAXV];

static int SA[MAXE], SB[MAXE], sm = 0, sn = 0;
static int have_snap = 0;

static int stamp[MAXV];
static int tick = 0;
static int qb[MAXV];
static int src[NSRC];

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void adj_replace(int v, int old, int nw) {
    for (int k = 0; k < deg[v]; k++)
        if (adj[v][k] == old) { adj[v][k] = nw; return; }
}

/* Number of vertices reached from s within dmax steps (including s). */
static int reach_count(int s, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stamp, 0, sizeof stamp);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[s] = tick;
    qb[tail++] = s;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qb[head];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                if (stamp[u] != tick) { stamp[u] = tick; qb[tail++] = u; }
            }
        }
    }
    return tail;
}

static long cost_sampled(void) {
    long c = 0;
    for (int i = 0; i < NSRC; i++) c += (long)(n - reach_count(src[i], D));
    return c;
}

/* Returns -1 if every vertex reaches all others within D, else a bad source. */
static int full_check(void) {
    for (int v = 0; v < n; v++)
        if (reach_count(v, D) < n) return v;
    return -1;
}

static int lk1, lk2, la1, lb1, la2, lb2;

/* Random 2-switch; applies it and returns 1, or returns 0 with no change. */
static int try_switch(void) {
    int k1 = rndint(m), k2 = rndint(m);
    if (k1 == k2) return 0;
    int a1 = EA[k1], b1 = EB[k1], a2 = EA[k2], b2 = EB[k2];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    adj_replace(a1, b1, b2);
    adj_replace(b1, a1, a2);
    adj_replace(a2, b2, b1);
    adj_replace(b2, a2, a1);
    EB[k1] = b2;
    EB[k2] = b1;
    lk1 = k1; lk2 = k2;
    la1 = a1; lb1 = b1; la2 = a2; lb2 = b2;
    return 1;
}

static void undo_switch(void) {
    adj_replace(la1, lb2, lb1);
    adj_replace(lb1, la2, la1);
    adj_replace(la2, lb1, lb2);
    adj_replace(lb2, la1, la2);
    EB[lk1] = lb1;
    EB[lk2] = lb2;
}

/* Adds two vertices x (A side) and y (B side), each of degree d. Returns 0 with no change on failure. */
static int grow(int *nx, int *ny) {
    if (m < d || n + 2 > MAXV || (long)(n + 2) > MOORE || m + d > MAXE) return 0;
    int sel[MAXD];
    int cnt = 0, tries = 0;
    while (cnt < d && tries < 10000) {
        tries++;
        int k = rndint(m);
        int a = EA[k], b = EB[k];
        int ok = 1;
        for (int j = 0; j < cnt; j++)
            if (EA[sel[j]] == a || EB[sel[j]] == b || sel[j] == k) { ok = 0; break; }
        if (ok) sel[cnt++] = k;
    }
    if (cnt < d) return 0;
    int x = n, y = n + 1;
    n += 2;
    deg[x] = 0;
    deg[y] = 0;
    for (int i = 0; i < d; i++) {
        int k = sel[i];
        int a = EA[k], b = EB[k];
        adj_replace(a, b, y);
        adj_replace(b, a, x);
        adj[x][deg[x]++] = b;
        adj[y][deg[y]++] = a;
        EA[k] = x;
        EB[k] = b;
        EA[m] = a;
        EB[m] = y;
        m++;
    }
    *nx = x;
    *ny = y;
    return 1;
}

static void snapshot(void) {
    memcpy(SA, EA, sizeof(int) * (size_t)m);
    memcpy(SB, EB, sizeof(int) * (size_t)m);
    sm = m;
    sn = n;
    have_snap = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit   (graph on stdin)\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);

    double t0 = now();
    t_end = t0 + limit - 0.5;

    rs ^= (uint64_t)(seed + 7) * 0xD1B54A32D192ED03ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    MOORE = moore_bound();

    static int U[MAXE], V[MAXE];
    int nn = 0, mm = 0;
    if (d < 1 || d > MAXD || D < 2 || scanf("%d %d", &nn, &mm) != 2 ||
        nn <= 0 || mm <= 0 || nn > MAXV || mm > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < mm; i++)
        if (scanf("%d %d", &U[i], &V[i]) != 2) { printf("0 0\n"); return 0; }

    for (int v = 0; v < nn; v++) deg[v] = 0;
    for (int i = 0; i < mm; i++) {
        int u = U[i], v = V[i];
        if (u < 0 || v < 0 || u >= nn || v >= nn || u == v || deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    /* 2-colour the input; it must be bipartite. */
    static int stk[MAXV];
    for (int v = 0; v < nn; v++) side[v] = -1;
    for (int s = 0; s < nn; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int v = stk[--sp];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                if (side[u] == -1) {
                    side[u] = 1 - side[v];
                    stk[sp++] = u;
                } else if (side[u] == side[v]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    n = nn;
    m = 0;
    for (int i = 0; i < mm; i++) {
        int u = U[i], v = V[i];
        if (side[u] == 0) { EA[m] = u; EB[m] = v; }
        else { EA[m] = v; EB[m] = u; }
        m++;
    }

    for (int i = 0; i < NSRC; i++) src[i] = rndint(n);

    have_snap = 0;
    if (full_check() < 0) snapshot();
    long cur = cost_sampled();

    double span = t_end - t0;
    double cyc = span / 8.0;
    if (cyc < 1.0) cyc = 1.0;
    double temp = T_HI;
    long it = 0;

    for (;;) {
        if ((++it & 31) == 0) {
            double tm = now();
            if (tm >= t_end) break;
            double ph = fmod(tm - t0, cyc) / cyc;
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        if (cur == 0) {
            int bad = full_check();
            if (bad < 0) {
                snapshot();
                int x = 0, y = 0;
                if (!grow(&x, &y)) break;   /* grow leaves the graph unchanged on failure */
                src[rndint(NSRC)] = x;
                src[rndint(NSRC)] = y;
            } else {
                src[rndint(NSRC)] = bad;
            }
            cur = cost_sampled();
            continue;
        }
        if (!try_switch()) continue;
        long c2 = cost_sampled();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) cur = c2;
        else undo_switch();
    }

    if (cur == 0 && full_check() < 0) snapshot();

    if (!have_snap) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", sn, sm);
    for (int k = 0; k < sm; k++) printf("%d %d\n", SA[k], SB[k]);
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
    if best[0] >= lib.moore_bound(d, D):
        return best   # already optimal; nothing to search

    avail = 0.8 * time_limit - 4.0 - (time.monotonic() - t0)
    if avail < 5.0:
        return best

    # Stage 1: structured voltage-lift search (safe, produces the record-level start).
    ref = REF_VERTICES.get((d, D), best[0])
    b1 = 0.55 * avail
    try:
        text = lib.run_c(C_LIFT, [d, D, seed, round(b1, 3), ref], timeout=b1 + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback

    # Stage 2: grow the best graph by vertex pairs and repair by annealing.
    left = 0.8 * time_limit - 3.0 - (time.monotonic() - t0)
    if left > 3.0 and best[0] > 2 * d:
        try:
            text = lib.run_c(C_GROW, [d, D, seed, round(left, 3)],
                             stdin_graph=best, timeout=left + 6)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the stage-1 result
    return best
