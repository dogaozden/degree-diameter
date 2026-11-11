"""Program: base-graph voltage lifts over metacyclic groups, with successive halving.

Construction:
  * A "base" bipartite multigraph has P vertices on each side and is d-regular. It is
    given by d permutations sig[k] (A-index -> B-index) and a voltage g[k][i] in a group G
    for each dart (k, i). The lift has 2*P*|G| vertices: (u, x) for base vertex u and x in G.
    Dart (k, i) joins (A_i, x) to (B_{sig[k][i]}, x * g[k][i]).
  * Left multiplication by G is an automorphism, so the diameter is <= D iff BFS from
    (u, e) reaches every vertex within D steps for each of the 2P base vertices u.
  * G is a metacyclic group Z_ma x|_r Z_kb (cyclic when kb = 1). Group operations are
    computed by formula, so no multiplication table is stored.
  * Candidates are (P, group) pairs whose order lies in a window around the target.
    They are searched by successive halving with simulated annealing over permutations
    and voltages. Duplicate darts are allowed and removed at output.

This differs from the earlier bi-Cayley search (P = 1, four darts into one B vertex):
it uses larger base graphs, which give more freedom at the same order.

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

#define MAXD 8
#define MAXP 8
#define PMAX 6
#define KMAX 12
#define MAXK 64
#define MAXGEN 20000
#define MAXKEEP 800
#define BIG_COST (1L << 60)
#define T_HI 3.0
#define T_LO 0.08
#define CYCLES 3.0
#define DI(k, i) ((k) * MAXP + (i))

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

/* ------------------------------------------------------------ group Z_ma x|_r Z_kb */

static int GMA = 1, GKB = 1, GM = 1;
static long PW[MAXK];   /* PW[b] = r^b mod ma */

static void set_group(int ma, int kb, int r) {
    GMA = ma;
    GKB = kb;
    GM = ma * kb;
    PW[0] = 1 % ma;
    for (int b = 1; b < kb; b++) PW[b] = PW[b - 1] * (long)r % ma;
}

/* element (a,b) coded a*kb+b; (a,b)(c,e) = (a + r^b c, b + e); identity code 0 */
static inline int gmul(int x, int y) {
    int a = x / GKB, b = x - a * GKB, c = y / GKB, e = y - c * GKB;
    long aa = ((long)a + PW[b] * (long)c) % GMA;
    int bb = (b + e) % GKB;
    return (int)aa * GKB + bb;
}

/* inverse of (a,b) is (-r^{-b} a, -b), and r^{-b} = r^{kb-b} since r^kb = 1 */
static inline int ginv(int x) {
    int a = x / GKB, b = x - a * GKB;
    int nb = (GKB - b) % GKB;
    long na = (GMA - PW[nb] % GMA) % GMA;
    long aa = na * a % GMA;
    return (int)aa * GKB + nb;
}

/* ------------------------------------------------------------ lift state */

static int P = 1, M = 1;
static int sig[MAXD][MAXP], isig[MAXD][MAXP];
static int gv[MAXD][MAXP], gvi[MAXD][MAXP];
static int bsig[MAXD][MAXP], bgv[MAXD][MAXP];
static int *R = NULL, *RI = NULL;  /* R[DI(k,i)*M + x] = x*g, RI[...] = x*g^{-1} */
static int *stamp = NULL, *qv = NULL;
static int tick = 0, maxV = 0;

static void set_dart(int k, int i) {
    int *Rp = R + (size_t)DI(k, i) * (size_t)M;
    int *RIp = RI + (size_t)DI(k, i) * (size_t)M;
    int g = gv[k][i], gi = gvi[k][i];
    for (int x = 0; x < M; x++) {
        Rp[x] = gmul(x, g);
        RIp[x] = gmul(x, gi);
    }
}

static void set_volt(int k, int i, int g) {
    gv[k][i] = g;
    gvi[k][i] = ginv(g);
    set_dart(k, i);
}

static void swap_sig(int k, int i1, int i2) {
    int a = sig[k][i1], b = sig[k][i2];
    sig[k][i1] = b;
    sig[k][i2] = a;
    isig[k][b] = i1;
    isig[k][a] = i2;
}

static void load_state(int S_[MAXD][MAXP], int G_[MAXD][MAXP]) {
    for (int k = 0; k < d; k++)
        for (int i = 0; i < P; i++) {
            sig[k][i] = S_[k][i];
            isig[k][sig[k][i]] = i;
        }
    for (int k = 0; k < d; k++)
        for (int i = 0; i < P; i++) set_volt(k, i, G_[k][i]);
}

static void randomize(void) {
    int perm[MAXP];
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < P; i++) {
            sig[k][i] = perm[i];
            isig[k][perm[i]] = i;
        }
        for (int i = 0; i < P; i++) set_volt(k, i, rndint(M));
    }
}

/* Number of vertices reached within dmax steps from src (vertex id = u*M + x). */
static long ball(int src, int dmax) {
    if (++tick == 0x7ffffff0) {
        memset(stamp, 0, sizeof(int) * (size_t)maxV);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            int u = v / M, x = v - u * M;
            if (u < P) {
                for (int k = 0; k < d; k++) {
                    int w = (P + sig[k][u]) * M + R[(size_t)DI(k, u) * M + x];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            } else {
                int j = u - P;
                for (int k = 0; k < d; k++) {
                    int i = isig[k][j];
                    int w = i * M + RI[(size_t)DI(k, i) * M + x];
                    if (stamp[w] != tick) { stamp[w] = tick; qv[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base vertices of the number of vertices not reached within D (0 = valid). */
static long cost_now(void) {
    int V = 2 * P * M;
    long c = 0;
    for (int u = 0; u < 2 * P; u++) c += V - ball(u * M, D);
    return c;
}

/* ------------------------------------------------------------ annealing */

static long last_min = BIG_COST;

static int climb(double until) {
    last_min = BIG_COST;
    if (M < 2) return 0;
    double start = now();
    double span = until - start;
    if (span <= 0.0) return 0;
    randomize();
    long cur = cost_now();
    long bestc = cur;
    memcpy(bsig, sig, sizeof sig);
    memcpy(bgv, gv, sizeof gv);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double f = (t - start) / span;
            double ph = f * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        if (P > 1 && rndint(2) == 0) {
            int k = rndint(d);
            int i1 = rndint(P), i2 = rndint(P - 1);
            if (i2 >= i1) i2++;
            swap_sig(k, i1, i2);
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) cur = nc;
            else swap_sig(k, i1, i2);
        } else {
            int k = rndint(d), i = rndint(P);
            int old = gv[k][i];
            set_volt(k, i, rndint(M));
            long nc = cost_now();
            long delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / temp)) cur = nc;
            else set_volt(k, i, old);
        }
        if (cur < bestc) {
            bestc = cur;
            memcpy(bsig, sig, sizeof sig);
            memcpy(bgv, gv, sizeof gv);
        }
    }
    last_min = bestc;
    if (bestc != 0) return 0;
    load_state(bsig, bgv);
    return 1;
}

/* ------------------------------------------------------------ candidates */

typedef struct { int p, ma, kb, r, V; } Cand;
static Cand *cand = NULL;
static int ncand = 0;

static void add_cand(int p, int ma, int kb, int r) {
    if (ncand >= MAXGEN) return;
    Cand c;
    c.p = p;
    c.ma = ma;
    c.kb = kb;
    c.r = r;
    c.V = 2 * p * ma * kb;
    cand[ncand++] = c;
}

static void add_cands(long lowV, long hiV) {
    for (int p = 1; p <= PMAX; p++) {
        long step = 2L * p;
        long mlo = (lowV + step - 1) / step, mhi = hiV / step;
        if (mlo < 3) mlo = 3;
        for (long m = mlo; m <= mhi && ncand < MAXGEN; m++) {
            for (int k = 1; k <= KMAX && k <= m; k++) {
                if (m % k) continue;
                int ma = (int)(m / k);
                if (ma < 2) continue;
                if (k == 1) { add_cand(p, ma, 1, 1); continue; }
                if (ma < 3) continue;
                int r0 = 1 + rndint(ma - 1), got = 0;
                for (int t = 0; t < ma - 1 && got < 2; t++) {
                    int r = 1 + (r0 - 1 + t) % (ma - 1);
                    if (gcd_l(r, ma) != 1) continue;
                    if (powmod_l(r, k, ma) != 1 % ma) continue;
                    add_cand(p, ma, k, r);
                    got++;
                }
            }
        }
    }
}

static void setup_cand(const Cand *c) {
    P = c->p;
    set_group(c->ma, c->kb, c->r);
    M = GM;
}

static int dupdart(int k, int i) {
    for (int l = 0; l < k; l++)
        if (sig[l][i] == sig[k][i] && gv[l][i] == gv[k][i]) return 1;
    return 0;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2 || ref < 8) { print_complete(); return 0; }

    long moore = moore_bound();
    long lowV = (long)(0.85 * (double)ref);
    long hiV = (long)(1.12 * (double)ref);
    if (hiV > moore) hiV = moore;
    if (hiV > 60000) hiV = 60000;
    if (lowV < 4) lowV = 4;
    if (hiV < lowV) { print_complete(); return 0; }

    size_t maxM = (size_t)hiV / 2 + 2;
    R = malloc(sizeof(int) * (size_t)MAXD * MAXP * maxM);
    RI = malloc(sizeof(int) * (size_t)MAXD * MAXP * maxM);
    maxV = (int)hiV + 8;
    stamp = calloc((size_t)maxV, sizeof(int));
    qv = malloc(sizeof(int) * (size_t)maxV);
    cand = malloc(sizeof(Cand) * MAXGEN);
    if (!R || !RI || !stamp || !qv || !cand) { print_complete(); return 0; }

    add_cands(lowV, hiV);
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    if (ncand > MAXKEEP) ncand = MAXKEEP;
    if (ncand == 0) { print_complete(); return 0; }

    int *alive = malloc(sizeof(int) * (size_t)ncand);
    long *cbest = malloc(sizeof(long) * (size_t)ncand);
    long *vals = malloc(sizeof(long) * (size_t)ncand);
    for (int i = 0; i < ncand; i++) { alive[i] = 1; cbest[i] = BIG_COST; }
    int nalive = ncand;

    double slice = usable * 0.3 / (double)ncand;
    if (slice < 0.01) slice = 0.01;
    double slice_cap = usable * 0.25;

    long bestV = 0;
    int have = 0;
    Cand bestc;
    memset(&bestc, 0, sizeof bestc);
    static int bestsig[MAXD][MAXP], bestgv[MAXD][MAXP];

    /* successive halving: every live candidate climbs once per round; the worse half
       (by lowest cost reached) is dropped, and survivors get twice the time */
    while (nalive > 0) {
        int stop = 0;
        for (int i = 0; i < ncand; i++) {
            if (!alive[i]) continue;
            if (cand[i].V <= bestV) { alive[i] = 0; nalive--; continue; }
            double remaining = t_end - now();
            if (remaining < 0.2) { stop = 1; break; }
            setup_cand(&cand[i]);
            double s = slice < remaining ? slice : remaining;
            if (climb(now() + s)) {
                have = 1;
                bestV = cand[i].V;
                bestc = cand[i];
                memcpy(bestsig, sig, sizeof sig);
                memcpy(bestgv, gv, sizeof gv);
                alive[i] = 0;
                nalive--;
            } else if (last_min < cbest[i]) {
                cbest[i] = last_min;
            }
        }
        if (stop) break;

        int m = 0;
        for (int i = 0; i < ncand; i++)
            if (alive[i]) vals[m++] = cbest[i];
        if (m > 1) {
            for (int a = 1; a < m; a++) {
                long x = vals[a];
                int b = a - 1;
                while (b >= 0 && vals[b] > x) { vals[b + 1] = vals[b]; b--; }
                vals[b + 1] = x;
            }
            long med = vals[(m - 1) / 2];
            for (int i = 0; i < ncand; i++) {
                if (alive[i] && cbest[i] > med) {
                    alive[i] = 0;
                    nalive--;
                }
            }
        }
        slice *= 2.0;
        if (slice > slice_cap) slice = slice_cap;
    }

    if (!have) { print_complete(); return 0; }

    setup_cand(&bestc);
    load_state(bestsig, bestgv);
    if (cost_now() != 0) { print_complete(); return 0; }

    int V = 2 * P * M;
    long E = 0;
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++)
            if (!dupdart(k, i)) E += M;

    printf("%d %ld\n", V, E);
    for (int i = 0; i < P; i++)
        for (int k = 0; k < d; k++) {
            if (dupdart(k, i)) continue;
            const int *Rp = R + (size_t)DI(k, i) * (size_t)M;
            int base = (P + sig[k][i]) * M;
            for (int x = 0; x < M; x++)
                printf("%d %d\n", i * M + x, base + Rp[x]);
        }
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
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
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
