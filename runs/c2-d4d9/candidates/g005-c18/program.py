"""Program: bi-Cayley / voltage-lift simulated annealing over groups, replacing hill-climbing over PSL/SL bi-Cayley graphs.

Construction (new):
  * Base graph with kb "A parts" and kb "B parts", each of degree d: dart t = (i, s) goes from A_i to
    B_{(i+s) mod kb}, s = 0..d-1. Every part has exactly d darts, so the base is d-regular bipartite.
  * Group G (order N) is either metacyclic Z_m x|_r Z_k (cyclic when k = 1) or PSL/SL(2,q).
    Each dart carries a voltage g_t in G. Lift: A_{i,x} -- B_{j, x*g_t}. The lift has 2*kb*N vertices,
    is bipartite, and has degree d. Darts sharing the same (i, j) pair need distinct voltages, so no
    edge is duplicated.
  * Left multiplication by G is an automorphism, so the diameter is at most D iff BFS from A_{i,e} and
    B_{j,e} for every part reaches all 2*kb*N vertices within D steps. Cost = total unreached pairs.
  * Simulated annealing over voltages (one dart changed per move, reheated every epoch).
  * Candidates: random metacyclic groups and PSL/SL(2,q) with 2*kb*N in [0.2, 0.36] of the Moore bound.
    Phase A tries SL(2,13) with kb = 1 (order 4368, the parent's graph), so a valid graph of that size
    is secured early. Phase B tries the rest in shuffled passes, requiring order above the best so far.

Safety: the C engine prints only graphs with cost 0, or K_{d,d} if nothing was found. Python checks
the result with lib.is_valid and keeps the largest valid graph, falling back to the known start or K_{d,d}.
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

#define MAXG 12200
#define KMAX 3
#define MAXD 8
#define MAXDART (KMAX * MAXD)
#define MAXV (2 * KMAX * MAXG)
#define MAXCAND 1200
#define SLICE 5.0

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
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

static int gtype;           /* 0: Z_m x| Z_k ; 1: SL/PSL(2,q) */
static int gm, gk, gr;      /* type 0 parameters */
static int pw[MAXG];        /* pw[b] = r^b mod m */
static int gq, gpsl;        /* type 1 parameters */
static int mat[MAXG][4];    /* type 1 matrix entries a,b,c,e */
static int *midx = NULL;
static int midx_cap = 0;
static int ORD;             /* group order */
static int gE;              /* identity index */

static int canon_key(int a, int b, int c, int e) {
    int q = gq;
    int k = ((a * q + b) * q + c) * q + e;
    if (!gpsl) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int lookup_m(int a, int b, int c, int e) { return midx[canon_key(a, b, c, e)]; }

static int build_matrix(int qq, int psl) {
    gq = qq;
    gpsl = psl;
    int ks = qq * qq * qq * qq;
    if (ks > midx_cap) {
        free(midx);
        midx = malloc(sizeof(int) * (size_t)ks);
        midx_cap = ks;
    }
    for (int i = 0; i < ks; i++) midx[i] = -1;
    int cnt = 0;
    for (int a = 0; a < qq; a++)
        for (int b = 0; b < qq; b++)
            for (int c = 0; c < qq; c++)
                for (int e = 0; e < qq; e++) {
                    if ((((a * e - b * c) % qq) + qq) % qq != 1) continue;
                    int own = ((a * qq + b) * qq + c) * qq + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXG) return 0;
                    mat[cnt][0] = a; mat[cnt][1] = b; mat[cnt][2] = c; mat[cnt][3] = e;
                    midx[own] = cnt;
                    cnt++;
                }
    ORD = cnt;
    gE = lookup_m(1, 0, 0, 1);
    return cnt;
}

static void build_meta(int m, int k, int r) {
    gm = m;
    gk = k;
    gr = r;
    ORD = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    gE = 0;
}

static int gmul0(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, dd = y - c * gk;
    int aa = (a + pw[b] * c) % gm;
    int bb = (b + dd) % gk;
    return aa * gk + bb;
}

static int ginv0(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    int aa = (gm - (int)((long)pw[nb] * a % gm)) % gm;
    return aa * gk + nb;
}

static int gmul1(int x, int y) {
    int q = gq;
    int *A = mat[x], *B = mat[y];
    int a = (A[0] * B[0] + A[1] * B[2]) % q;
    int b = (A[0] * B[1] + A[1] * B[3]) % q;
    int c = (A[2] * B[0] + A[3] * B[2]) % q;
    int e = (A[2] * B[1] + A[3] * B[3]) % q;
    return lookup_m(a, b, c, e);
}

static int ginv1(int x) {
    int q = gq;
    int *A = mat[x];
    return lookup_m(A[3] % q, (q - A[1]) % q, (q - A[2]) % q, A[0]);
}

static int gmul(int x, int y) { return gtype == 0 ? gmul0(x, y) : gmul1(x, y); }
static int ginv(int x) { return gtype == 0 ? ginv0(x) : ginv1(x); }

/* ------------------------------------------------------------------ base and voltages */

static int kb;                    /* number of parts per side */
static int V_;                    /* vertex count 2*kb*ORD */
static int tgt[MAXDART];          /* target part of dart t = i*d+s */
static int incl[KMAX][MAXD];      /* darts entering part j */
static int gv[MAXDART];           /* voltages */
static int Rt[MAXDART][MAXG];     /* Rt[t][x] = x * g_t */
static int Ri[MAXDART][MAXG];     /* Ri[t][y] = y * g_t^{-1} */
static int tmpR[MAXG], tmpI[MAXG];

static void setup_base(int k) {
    kb = k;
    V_ = 2 * kb * ORD;
    for (int i = 0; i < kb; i++)
        for (int s = 0; s < d; s++) tgt[i * d + s] = (i + s) % kb;
    int cnt[KMAX];
    for (int j = 0; j < KMAX; j++) cnt[j] = 0;
    for (int t = 0; t < kb * d; t++) {
        int j = tgt[t];
        incl[j][cnt[j]++] = t;
    }
}

static void set_dart(int t, int v) {
    gv[t] = v;
    int vi = ginv(v);
    for (int x = 0; x < ORD; x++) {
        Rt[t][x] = gmul(x, v);
        Ri[t][x] = gmul(x, vi);
    }
}

/* True if voltage v on dart t would duplicate an edge set with a dart t2 < upto (same part pair). */
static int clash(int t, int v, int upto) {
    for (int t2 = 0; t2 < upto; t2++) {
        if (t2 == t) continue;
        if (t2 / d == t / d && tgt[t2] == tgt[t] && gv[t2] == v) return 1;
    }
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
    int split = kb * ORD;
    int head = 0, tail = 0;
    stamp[src] = tick;
    qv[tail++] = src;
    for (int lvl = 0; lvl < dmax && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            if (v < split) {
                int i = v / ORD, x = v - i * ORD;
                for (int s = 0; s < d; s++) {
                    int t = i * d + s;
                    int u = split + tgt[t] * ORD + Rt[t][x];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            } else {
                int w = v - split;
                int j = w / ORD, y = w - j * ORD;
                for (int s = 0; s < d; s++) {
                    int t = incl[j][s];
                    int u = (t / d) * ORD + Ri[t][y];
                    if (stamp[u] != tick) { stamp[u] = tick; qv[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base representatives of unreached vertices within D steps; 0 means diameter <= D. */
static long cost(void) {
    long tot = 0;
    int split = kb * ORD;
    for (int i = 0; i < kb; i++) {
        tot += (long)(V_ - ball(i * ORD + gE, D));
        tot += (long)(V_ - ball(split + i * ORD + gE, D));
    }
    return tot;
}

static void random_init(void) {
    int nd = kb * d;
    for (int t = 0; t < nd; t++) {
        int v;
        do { v = rndint(ORD); } while (clash(t, v, t));
        set_dart(t, v);
    }
}

/* Simulated annealing over voltages. Returns 1 with gv valid (cost 0), 0 on timeout. */
static int sa_search(double until) {
    const long EPOCH = 4000;
    random_init();
    long cur = cost();
    long it = 0;
    int nd = kb * d;
    while (cur > 0) {
        if (((++it) & 15) == 0 && now() > until) return 0;
        int t = rndint(nd);
        int v = rndint(ORD);
        if (v == gv[t] || clash(t, v, nd)) continue;
        int old = gv[t];
        memcpy(tmpR, Rt[t], sizeof(int) * (size_t)ORD);
        memcpy(tmpI, Ri[t], sizeof(int) * (size_t)ORD);
        set_dart(t, v);
        long nc = cost();
        double T0 = cur * 0.05 > 2.0 ? cur * 0.05 : 2.0;
        double ph = (double)(it % EPOCH) / (double)EPOCH;
        double T = T0 * pow(0.1, ph);
        int accept = (nc <= cur) || (rnd01() < exp(-(double)(nc - cur) / T));
        if (accept) {
            cur = nc;
        } else {
            gv[t] = old;
            memcpy(Rt[t], tmpR, sizeof(int) * (size_t)ORD);
            memcpy(Ri[t], tmpI, sizeof(int) * (size_t)ORD);
        }
    }
    return 1;
}

/* ------------------------------------------------------------------ candidates */

typedef struct {
    int type;      /* 0 metacyclic, 1 matrix */
    int kb;
    int m, k, r;   /* type 0 */
    int q, psl;    /* type 1 */
    int ord;
    int V;
} Cand;

static Cand cands[MAXCAND];
static int ncand = 0;

static void add_cand(Cand c) {
    if (ncand < MAXCAND) cands[ncand++] = c;
}

static void setup_candidate(const Cand *c) {
    gtype = c->type;
    if (c->type == 1) build_matrix(c->q, c->psl);
    else build_meta(c->m, c->k, c->r);
    setup_base(c->kb);
}

static int best_V = 0;
static int have_best = 0;
static Cand bestC;
static int bestGv[MAXDART];

static void process(int c, double slice) {
    if (cands[c].V <= best_V) return;
    setup_candidate(&cands[c]);
    double until = now() + slice;
    if (until > t_end) until = t_end;
    if (sa_search(until)) {
        best_V = cands[c].V;
        bestC = cands[c];
        memcpy(bestGv, gv, sizeof(gv));
        have_best = 1;
    }
}

static void shuffle_cands(void) {
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = cands[i];
        cands[i] = cands[j];
        cands[j] = tmp;
    }
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    long moore = moore_bound();
    double lo = 0.2 * (double)moore, hi = 0.36 * (double)moore;

    midx = NULL;
    midx_cap = 0;

    /* Matrix-group candidates SL/PSL(2,q). */
    static const int primes[] = {5, 7, 11, 13, 17, 19, 23};
    for (unsigned pi = 0; pi < sizeof primes / sizeof primes[0]; pi++) {
        for (int psl = 0; psl < 2; psl++) {
            long q = primes[pi];
            long order = q * (q * q - 1);
            if (psl) order /= 2;
            for (int kbb = 1; kbb <= KMAX; kbb++) {
                double V = 2.0 * kbb * (double)order;
                if (V >= lo && V <= hi && order >= d + 1 && order <= MAXG) {
                    Cand c;
                    c.type = 1; c.kb = kbb; c.m = 0; c.k = 0; c.r = 0;
                    c.q = (int)q; c.psl = psl; c.ord = (int)order; c.V = (int)V;
                    add_cand(c);
                }
            }
        }
    }

    /* Metacyclic candidates Z_m x|_r Z_k with random sampling. */
    int tries = 0;
    while (ncand < MAXCAND && tries < 6000) {
        tries++;
        int kbb = 1 + rndint(KMAX);
        int Nlo = (int)(lo / (2.0 * kbb));
        int Nhi = (int)(hi / (2.0 * kbb)) + 1;
        if (Nhi > MAXG) Nhi = MAXG;
        if (Nhi < Nlo || Nlo < 1) continue;
        int N = Nlo + rndint(Nhi - Nlo + 1);
        int V = 2 * kbb * N;
        if (N < d + 1 || N > MAXG || (double)V < lo || (double)V > hi) continue;
        int divs[512];
        int nd = 0;
        for (int dv = 1; dv * dv <= N; dv++) {
            if (N % dv == 0) {
                divs[nd++] = dv;
                if (dv * dv != N && nd < 512) divs[nd++] = N / dv;
            }
        }
        int k1 = divs[rndint(nd)];
        int m = N / k1;
        if (m < 2) continue;
        int r = 1;
        if (k1 > 1 && m >= 3) {
            for (int tr = 0; tr < 300; tr++) {
                int rr = 2 + rndint(m - 2);
                if (gcd_i(rr, m) == 1 && powmod(rr, k1, m) == 1) { r = rr; break; }
            }
        }
        Cand c;
        c.type = 0; c.kb = kbb; c.m = m; c.k = k1; c.r = r;
        c.q = 0; c.psl = 0; c.ord = N; c.V = V;
        add_cand(c);
    }

    if (ncand == 0) { print_complete(); return 0; }

    shuffle_cands();

    /* Phase A: the parent's group SL(2,13), kb = 1 (order 4368), if present. */
    int sa = -1;
    for (int c = 0; c < ncand; c++) {
        if (cands[c].type == 1 && cands[c].q == 13 && cands[c].psl == 0 && cands[c].kb == 1) {
            sa = c;
            break;
        }
    }
    if (sa >= 0) {
        double ph = 0.3 * (t_end - now());
        if (ph < 0.5) ph = 0.5;
        process(sa, ph);
    }

    /* Phase B: shuffled passes over candidates larger than the best so far. */
    while (now() < t_end) {
        int attempted = 0;
        for (int c = 0; c < ncand && now() < t_end; c++) {
            if (cands[c].V <= best_V) continue;
            attempted++;
            process(c, SLICE);
        }
        if (!attempted) break;
        shuffle_cands();
    }

    if (!have_best) {
        print_complete();
        return 0;
    }

    setup_candidate(&bestC);
    memcpy(gv, bestGv, sizeof(gv));
    int kbb = bestC.kb;
    long V = 2L * kbb * ORD;
    long M = (long)kbb * d * ORD;
    printf("%ld %ld\n", V, M);
    int split = kbb * ORD;
    for (int i = 0; i < kbb; i++)
        for (int x = 0; x < ORD; x++)
            for (int s = 0; s < d; s++) {
                int t = i * d + s;
                int j = tgt[t];
                int a = i * ORD + x;
                int b = split + j * ORD + gmul(x, bestGv[t]);
                printf("%d %d\n", a, b);
            }
    return 0;
}
'''


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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
