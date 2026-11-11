"""Program: bi-Cayley lifts over small metacyclic groups, searched near the target order.

Different construction from the parent. The parent searched a broad pool of
groups (SL/PSL and metacyclic) with greedy seeding. This version uses:
  * Only metacyclic groups Z_m x|_r Z_k with k <= 12 (cyclic k = 1 included),
    with the group order N fixed by the candidate, not by a table.
  * Two base vertices per side at most (P <= 2), so the lift has 2PN vertices.
  * Candidates are ordered by distance of 2PN from the record, nearest first,
    and a candidate is skipped once a valid graph at least that large exists.
  * Cost is the number of pairs left unreached within D from the representatives
    A(i,e) and B(j,e). Left multiplication is an automorphism, so this is zero
    iff the lift has diameter <= D.
  * Simulated annealing with sawtooth reheats, restarting the base permutations
    on some cycles.

Safety: the C engine prints K_{d,d} when nothing valid is found. Python checks
the output with lib.is_valid and keeps the best valid graph, falling back to the
known start or K_{d,d}.
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

#define MAXN 10000
#define MAXP 2
#define MAXDEG 8
#define MAXDART (MAXP * MAXDEG)
#define MAXV (2 * MAXP * MAXN)
#define MAXCAND 200000
#define MAXK 12
#define T_HI 20.0
#define T_LO 0.3
#define CYCLES 4.0

typedef struct {
    int P, m, k, r, N;
    long V;
    double key;
} Cand;

typedef struct {
    int P, m, k, r, N, nd;
    long V;
    int dI[MAXDART], dJ[MAXDART], vol[MAXDART];
} Snap;

static Cand CAND[MAXCAND];
static int nc = 0;
static Snap SN;
static int have = 0;
static long bestV = 0;

static int d, D;
static long MOORE, REF;
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int gM = 1, gK = 1, gR = 1, gN = 1;
static int pw[MAXK + 1];

static void set_group(int m, int k, int r) {
    gM = m;
    gK = k;
    gR = r;
    gN = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
}

/* (a,b)(c,d) = (a + r^b c, b + d); element (a,b) coded as a*k + b. */
static int gmul(int x, int y) {
    int a = x / gK, b = x % gK;
    int c = y / gK, dd = y % gK;
    int aa = (a + pw[b] * c) % gM;
    int bb = (b + dd) % gK;
    return aa * gK + bb;
}

/* (a,b)^{-1} = (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / gK, b = x % gK;
    int nb = (gK - b) % gK;
    long v = ((long)pw[nb] * a) % gM;
    v = (gM - v) % gM;
    return (int)v * gK + nb;
}

/* ------------------------------------------------------------ lift state */

static int P = 1, N = 1, half = 1;
static int nd = 0;
static int dI[MAXDART], dJ[MAXDART], vol[MAXDART], vinv[MAXDART], evol[MAXDART];
static int dA[MAXP][MAXDEG], dB[MAXP][MAXDEG];

static int stampArr[MAXV];
static int tick = 0;
static int qv[MAXV];

static int clash(int t, int g, int upto) {
    for (int s = 0; s < upto; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && vol[s] == g) return 1;
    return 0;
}

static void build_lists(void) {
    int ca[MAXP] = {0};
    int cb[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        dA[dI[t]][ca[dI[t]]++] = t;
        dB[dJ[t]][cb[dJ[t]]++] = t;
    }
}

static void setvol(int t, int g) {
    vol[t] = g;
    vinv[t] = ginv(g);
}

/* d random permutations on P points give a d-regular P x P multigraph of darts. */
static int gen_base(void) {
    int M[MAXP][MAXP];
    memset(M, 0, sizeof M);
    for (int c = 0; c < d; c++) {
        int perm[MAXP];
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
        int ok = 0, g = 0;
        for (int tries = 0; tries < 5000; tries++) {
            g = rndint(N);
            if (!clash(t, g, t)) { ok = 1; break; }
        }
        if (!ok) return 0;
        setvol(t, g);
    }
    return 1;
}

static void load_elite(void) {
    for (int t = 0; t < nd; t++) setvol(t, evol[t]);
}

/* BFS in the lift from a vertex; returns the number reached within dmax steps. */
static int ball(int src, int dmax) {
    if (++tick == 0x7fffffff) {
        memset(stampArr, 0, sizeof stampArr);
        tick = 1;
    }
    int head = 0, tail = 0;
    stampArr[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < half) {
                int i = v / N, x = v - i * N;
                for (int kk = 0; kk < d; kk++) {
                    int t = dA[i][kk];
                    int u = half + dJ[t] * N + gmul(x, vol[t]);
                    if (stampArr[u] != tick) { stampArr[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / N, y = w - j * N;
                for (int kk = 0; kk < d; kk++) {
                    int t = dB[j][kk];
                    int u = dI[t] * N + gmul(y, vinv[t]);
                    if (stampArr[u] != tick) { stampArr[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from the representatives A(i,e), B(j,e); 0 means valid. */
static long cost(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        c += (long)(2 * half - ball(i * N, D));
    for (int j = 0; j < P; j++)
        c += (long)(2 * half - ball(half + j * N, D));
    return c;
}

/* Simulated annealing over voltages; returns 1 with a valid lift left in place. */
static int climb(double until) {
    if (!gen_base()) return 0;
    long cur = cost();
    if (cur == 0) return 1;
    long best_c = cur;
    memcpy(evol, vol, sizeof(int) * (size_t)nd);
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    int cyc_prev = 0;
    double temp = T_HI;
    long it = 0;
    for (;;) {
        if ((++it & 31) == 0) {
            double tm = now();
            if (tm >= until) return 0;
            double ph = (tm - start) / span * CYCLES;
            int cyc = (int)floor(ph);
            double fr = ph - floor(ph);
            temp = T_HI * pow(T_LO / T_HI, fr);
            if (cyc != cyc_prev) {
                cyc_prev = cyc;
                if (rnd01() < 0.3) {
                    if (!gen_base()) return 0;
                    cur = cost();
                    if (cur == 0) return 1;
                    best_c = cur;
                    memcpy(evol, vol, sizeof(int) * (size_t)nd);
                } else {
                    load_elite();
                    cur = best_c;
                }
            }
        }
        int tn = rndint(nd);
        int g = rndint(N);
        if (g == vol[tn] || clash(tn, g, nd)) continue;
        int old = vol[tn], oldinv = vinv[tn];
        setvol(tn, g);
        long c2 = cost();
        long delta = c2 - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) {
            cur = c2;
            if (cur == 0) return 1;
            if (cur < best_c) {
                best_c = cur;
                memcpy(evol, vol, sizeof(int) * (size_t)nd);
            }
        } else {
            vol[tn] = old;
            vinv[tn] = oldinv;
        }
    }
}

/* ------------------------------------------------------------ candidates */

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->key < y->key) return -1;
    if (x->key > y->key) return 1;
    return 0;
}

static void push_cand(int Pp, int m, int k, int r) {
    if (nc >= MAXCAND) return;
    Cand c;
    c.P = Pp;
    c.m = m;
    c.k = k;
    c.r = r;
    c.N = m * k;
    c.V = 2L * Pp * c.N;
    double dist = fabs((double)c.V - (double)(REF + 1));
    if (c.V <= REF) dist += 0.5;   /* prefer candidates that beat the record */
    c.key = dist + 0.0001 * (double)(rnd() % 1000);
    CAND[nc++] = c;
}

static void gen_candidates(void) {
    long lowV = (long)(0.9 * (double)REF);
    if (lowV < 2) lowV = 2;
    long hiV = (long)(1.12 * (double)REF) + 50;
    if (hiV > MOORE) hiV = MOORE;
    nc = 0;
    for (int Pp = 1; Pp <= MAXP; Pp++) {
        long Nlo = lowV / (2L * Pp) + 1;
        long Nhi = hiV / (2L * Pp);
        if (Nhi > MAXN) Nhi = MAXN;
        if (Nlo < 3) Nlo = 3;
        for (long Nv = Nlo; Nv <= Nhi; Nv++) {
            push_cand(Pp, (int)Nv, 1, 1);   /* cyclic group Z_N */
            for (long k = 2; k <= MAXK; k++) {
                if (Nv % k) continue;
                long m = Nv / k;
                if (m < 3) continue;
                push_cand(Pp, (int)m, (int)k, 1);   /* abelian Z_m x Z_k */
                int found = 0;
                if (m <= 400) {
                    for (long r = 2; r < m && found < 2; r++) {
                        if (gcd_l(r, m) != 1 || powmod_l(r, k, m) != 1) continue;
                        push_cand(Pp, (int)m, (int)k, (int)r);
                        found++;
                    }
                } else {
                    for (int tries = 0; tries < 300 && found < 2; tries++) {
                        long r = 2 + (long)(rnd() % (uint64_t)(m - 2));
                        if (gcd_l(r, m) != 1 || powmod_l(r, k, m) != 1) continue;
                        push_cand(Pp, (int)m, (int)k, (int)r);
                        found++;
                    }
                }
            }
        }
    }
    qsort(CAND, (size_t)nc, sizeof(Cand), cmp_cand);
}

/* ------------------------------------------------------------ snapshot and output */

static void take_snapshot(void) {
    SN.P = P;
    SN.m = gM;
    SN.k = gK;
    SN.r = gR;
    SN.N = N;
    SN.nd = nd;
    SN.V = 2L * P * N;
    memcpy(SN.dI, dI, sizeof(int) * (size_t)nd);
    memcpy(SN.dJ, dJ, sizeof(int) * (size_t)nd);
    memcpy(SN.vol, vol, sizeof(int) * (size_t)nd);
    have = 1;
    bestV = SN.V;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_graph(void) {
    printf("%d %d\n", 2 * half, P * N * d);
    for (int i = 0; i < P; i++)
        for (int x = 0; x < N; x++)
            for (int kk = 0; kk < d; kk++) {
                int t = dA[i][kk];
                printf("%d %d\n", i * N + x, half + dJ[t] * N + gmul(x, vol[t]));
            }
}

/* ------------------------------------------------------------ main */

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
    REF = ref > 0 ? ref : 2L * d;

    gen_candidates();

    for (int i = 0; i < nc; i++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand *c = &CAND[i];
        if (c->V <= bestV) continue;
        double slice = usable * 0.03;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        set_group(c->m, c->k, c->r);
        P = c->P;
        N = gN;
        half = P * N;
        if (climb(now() + slice)) take_snapshot();
    }

    if (!have) { print_complete(); return 0; }
    set_group(SN.m, SN.k, SN.r);
    P = SN.P;
    N = SN.N;
    half = P * N;
    nd = SN.nd;
    memcpy(dI, SN.dI, sizeof(int) * (size_t)nd);
    memcpy(dJ, SN.dJ, sizeof(int) * (size_t)nd);
    memcpy(vol, SN.vol, sizeof(int) * (size_t)nd);
    build_lists();
    for (int t = 0; t < nd; t++) vinv[t] = ginv(vol[t]);
    if (cost() != 0) { print_complete(); return 0; }
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
            ref = REF_VERTICES.get((d, D), best[0])
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), ref],
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
