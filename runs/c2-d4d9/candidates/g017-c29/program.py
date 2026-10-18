"""Program: two-stage search for bipartite graphs with max degree d and diameter D.

Stage 1 (unchanged parent engine): voltage lifts over cyclic, metacyclic, matrix and abelian
groups with annealed voltage search. It produces a valid graph, the baseline.

Stage 2 (new engine, the bold change): start from the stage-1 graph and grow it by unstructured
local search. Each growth step removes d edges (a_i, b_i) and adds a new A-vertex x adjacent to
all b_i and a new B-vertex y adjacent to all a_i. This keeps every degree at exactly d and
keeps the graph bipartite. Degree-preserving 2-switches then anneal the number of vertex pairs
at distance more than D toward zero, using bitset BFS. A state with zero bad pairs is saved as
the new best and growth continues from it.

Safety: every engine output is checked with lib.is_valid. The engines print "0 0" on any
failure, which Python ignores. The best valid graph found so far is always returned.
Note: stage 2 is an untested heuristic. It may not beat the record, but it cannot return an
invalid graph.
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

/* Z_m x Z_k (direct product), element (a,b) coded as a*k+b. Non-cyclic when gcd(m,k) > 1. */
static int build_abel(int m, int k) {
    long n = (long)m * k;
    if (n > MAXN || n < 2) return 0;
    N = (int)n;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, dd = y % k;
            int aa = (a + c) % m;
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

/* type: 0 = metacyclic, 1 = matrix (SL/PSL), 2 = abelian non-cyclic */
typedef struct {
    int type;
    int q, psl, m, k, r, N, P;
    long V;        /* total vertices = 2 * P * N */
    double key;    /* priority: distance from the target order plus a type penalty */
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
        /* Metacyclic Z_m x| Z_k. */
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
        /* Non-cyclic abelian Z_m x Z_k with k <= m and gcd(m,k) > 1. */
        for (long k = 2; k * k <= Nv; k++) {
            if (Nv % k) continue;
            long m = Nv / k;
            if (gcd_l(m, k) == 1) continue;
            for (int Pp = 1; Pp <= MAXP; Pp++) {
                long V = 2L * Pp * Nv;
                if (V <= lowV || V > hiV || V > MOORE) continue;
                Cand c;
                memset(&c, 0, sizeof c);
                c.type = 2;
                c.m = (int)m;
                c.k = (int)k;
                c.N = (int)Nv;
                c.P = Pp;
                c.V = V;
                push_cand(&c);
            }
        }
    }
    for (int i = 0; i < nc; i++) {
        double pen = (CAND[i].type == 1) ? 0.0 : (CAND[i].type == 2 ? 0.25 : 0.5);
        CAND[i].key = fabs((double)CAND[i].V - (double)(REFV + 1)) + pen;
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

static int P = 1, half = 1, nd = 0;

static int apply_cand(const Cand *c) {
    int ok;
    if (c->type == 0) ok = build_meta(c->m, c->k, c->r);
    else if (c->type == 2) ok = build_abel(c->m, c->k);
    else ok = build_matrix(c->q, c->psl);
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

GROW_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 8
#define MAXGROW 400
#define ITERS 1500

static int d, D;
static long MOORE;
static double t_end;
static int cap, WS;
static int n;
static int *side, *deg, *adj;
static int *bside, *bdeg, *badj;
static int bn;
static uint64_t *RA, *RB;

static uint64_t rs = 0x243F6A8885A308D3ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
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

static void fail(void) {
    printf("0 0\n");
    exit(0);
}

static int slot_of(int v, int u) {
    for (int k = 0; k < deg[v]; k++)
        if (adj[v * MAXD + k] == u) return k;
    return -1;
}

static int has_edge(int a, int b) { return slot_of(a, b) >= 0; }

static void set_nb(int v, int old, int nw) {
    int k = slot_of(v, old);
    if (k >= 0) adj[v * MAXD + k] = nw;
}

static void apply_switch(int a1, int b1, int a2, int b2) {
    set_nb(a1, b1, b2);
    set_nb(b1, a1, a2);
    set_nb(a2, b2, b1);
    set_nb(b2, a2, a1);
}

static void revert_switch(int a1, int b1, int a2, int b2) {
    set_nb(a1, b2, b1);
    set_nb(b2, a1, a2);
    set_nb(a2, b1, b2);
    set_nb(b1, a2, a1);
}

/* Bad ordered-by-unordered pairs at distance > D, including unreachable pairs. */
static long bad_cost(void) {
    int Wn = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    for (int v = 0; v < n; v++) {
        uint64_t *row = cur + (size_t)v * WS;
        memset(row, 0, sizeof(uint64_t) * (size_t)Wn);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < D; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * WS;
            memcpy(o, cur + (size_t)v * WS, sizeof(uint64_t) * (size_t)Wn);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s = cur + (size_t)adj[v * MAXD + k] * WS;
                for (int w = 0; w < Wn; w++) o[w] |= s[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = cur + (size_t)v * WS;
        long pc = 0;
        for (int w = 0; w < Wn; w++) pc += __builtin_popcountll(row[w]);
        bad += (long)n - pc;
    }
    return bad / 2;
}

static void save_best(void) {
    bn = n;
    memcpy(bside, side, sizeof(int) * (size_t)n);
    memcpy(bdeg, deg, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(int) * (size_t)n * MAXD);
}

static void restore_best(void) {
    n = bn;
    memcpy(side, bside, sizeof(int) * (size_t)n);
    memcpy(deg, bdeg, sizeof(int) * (size_t)n);
    memcpy(adj, badj, sizeof(int) * (size_t)n * MAXD);
}

/* Add new A-vertex x and B-vertex y; remove d edges (a_i,b_i) and join x to all b_i, y to all a_i. */
static int grow(void) {
    if (n + 2 > cap) return 0;
    int ea[MAXD], eb[MAXD];
    int cnt = 0, tries = 0;
    while (cnt < d && tries < 100000) {
        tries++;
        int a = rndint(n);
        if (side[a] != 0) continue;
        int b = adj[a * MAXD + rndint(deg[a])];
        int ok = 1;
        for (int i = 0; i < cnt; i++)
            if (ea[i] == a || eb[i] == b) { ok = 0; break; }
        if (ok) { ea[cnt] = a; eb[cnt] = b; cnt++; }
    }
    if (cnt < d) return 0;
    int x = n, y = n + 1;
    side[x] = 0;
    side[y] = 1;
    deg[x] = d;
    deg[y] = d;
    for (int i = 0; i < d; i++) {
        set_nb(ea[i], eb[i], y);
        set_nb(eb[i], ea[i], x);
        adj[x * MAXD + i] = eb[i];
        adj[y * MAXD + i] = ea[i];
    }
    n += 2;
    return 1;
}

static void print_best(void) {
    long m = 0;
    for (int v = 0; v < bn; v++)
        if (bside[v] == 0) m += bdeg[v];
    printf("%d %ld\n", bn, m);
    for (int v = 0; v < bn; v++) {
        if (bside[v] != 0) continue;
        for (int k = 0; k < bdeg[v]; k++)
            printf("%d %d\n", v, badj[v * MAXD + k]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);

    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) fail();

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || n0 > 20000) fail();

    cap = n0 + MAXGROW;
    WS = (cap + 63) / 64;
    side = calloc((size_t)cap, sizeof(int));
    deg = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * MAXD, sizeof(int));
    bside = calloc((size_t)cap, sizeof(int));
    bdeg = calloc((size_t)cap, sizeof(int));
    badj = calloc((size_t)cap * MAXD, sizeof(int));
    RA = calloc((size_t)cap * WS, sizeof(uint64_t));
    RB = calloc((size_t)cap * WS, sizeof(uint64_t));
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *queue = malloc(sizeof(int) * (size_t)cap);
    if (!side || !deg || !adj || !bside || !bdeg || !badj || !RA || !RB || !eu || !ev || !queue) fail();

    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) fail();
    }

    n = n0;
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) fail();
        if (deg[u] >= d || deg[v] >= d) fail();
        if (has_edge(u, v)) fail();
        adj[u * MAXD + deg[u]++] = v;
        adj[v * MAXD + deg[v]++] = u;
    }
    for (int i = 0; i < n; i++)
        if (deg[i] != d) fail();

    /* Bipartition by BFS. */
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        int qh = 0, qt = 0;
        side[s] = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * MAXD + k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    queue[qt++] = v;
                } else if (side[v] == side[u]) {
                    fail();
                }
            }
        }
    }

    if (bad_cost() != 0) fail();   /* input must already be valid */
    save_best();

    MOORE = moore_bound();
    int stale = 0;
    while (now() < t_end) {
        restore_best();
        if (n + 2 > cap || (long)(n + 2) > MOORE) break;
        if (!grow()) {
            if (++stale > 50) break;
            continue;
        }
        long c = bad_cost();
        double T = 1.0 + 0.002 * (double)c;
        int it = 0;
        while (c > 0 && it < ITERS && now() < t_end) {
            it++;
            int a1, a2, b1, b2;
            do { a1 = rndint(n); } while (side[a1] != 0);
            do { a2 = rndint(n); } while (side[a2] != 0);
            if (a1 == a2) continue;
            b1 = adj[a1 * MAXD + rndint(deg[a1])];
            b2 = adj[a2 * MAXD + rndint(deg[a2])];
            if (b1 == b2) continue;
            if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
            apply_switch(a1, b1, a2, b2);
            long c2 = bad_cost();
            long delta = c2 - c;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                c = c2;
            } else {
                revert_switch(a1, b1, a2, b2);
            }
            T *= 0.997;
            if (T < 0.3) T = 0.3;
        }
        if (c == 0) {
            save_best();
            stale = 0;
        } else {
            stale++;
        }
    }

    print_best();
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
    deadline = time.monotonic() + 0.85 * time_limit - 1.5
    start = known_start(d, D)
    if start is None or not lib.is_valid(start[0], start[1], d, D):
        start = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    best = start
    if best[0] >= lib.moore_bound(d, D):
        return best                            # Moore graph: nothing to improve

    # Stage 1: parent voltage-lift search (the baseline that reaches the record).
    ref = REF_VERTICES.get((d, D), best[0])
    p1 = 0.6 * (deadline - time.monotonic())
    if p1 > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(p1, 3), ref], timeout=p1 + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback

    # Stage 2: grow the best graph by vertex insertion and annealed edge switches.
    p2 = deadline - time.monotonic() - 0.5
    if p2 > 1.0:
        try:
            text = lib.run_c(GROW_SOURCE, [d, D, seed + 1, round(p2, 3)],
                             stdin_graph=best, timeout=p2 + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback

    return best
