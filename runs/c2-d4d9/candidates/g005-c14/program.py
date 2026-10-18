"""Program: bi-Cayley / voltage-lift search with simulated annealing (replaces the hill-climb).

Changes from the parent (bold, higher-risk):
  * Generalized voltage lifts. A base bipartite multigraph with B = 2*bA vertices
    (bA on each side, d-regular, parallel darts allowed) is lifted over a group G of
    order N. Lift vertex (u, x) is joined to (w, x*g) for each base edge u-w with
    voltage g. The lift has B*N vertices. B = 2 is the old bi-Cayley case.
  * Left multiplication is an automorphism, so the diameter is <= D iff a BFS from
    (u, e) reaches all B*N vertices within D steps, for every base vertex u.
  * Groups: PSL(2,q)/SL(2,q) for prime q (as before), and metacyclic groups
    Z_m x|_r Z_k (r^k = 1 mod m) of any order, sampled at random.
  * Search: simulated annealing over the voltages (cost = unreached pairs), with
    cooling cycles and restarts. The C engine keeps a ladder of targets, each
    strictly above the best order found so far.
  * Safety: the C engine starts from K_{d,d}, keeps the best verified-by-construction
    graph, and Python re-checks everything with lib.is_valid before returning.
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
#define MAXM 20000
#define MAXDEG 8
#define MAXB 16
#define MAXE 128
#define MAXOUT 80000

static int d, D;

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

/* ------------------------------------------------------------ groups */

static int GQ, gpsl, gtype, N, eid;
static int gm[MAXG][4];
static int idxt[331776];          /* 24^4 */
static int gmm, gmk;
static int powr[MAXG];
static int invt[MAXG];

static int canon_key(int a, int b, int c, int e) {
    int k = ((a * GQ + b) * GQ + c) * GQ + e;
    if (!gpsl) return k;
    int na = (GQ - a) % GQ, nb = (GQ - b) % GQ, nc = (GQ - c) % GQ, ne = (GQ - e) % GQ;
    int kn = ((na * GQ + nb) * GQ + nc) * GQ + ne;
    return k < kn ? k : kn;
}

static int mlookup(int a, int b, int c, int e) { return idxt[canon_key(a, b, c, e)]; }

static int build_matrix(int q, int psl) {
    GQ = q;
    gpsl = psl;
    gtype = 0;
    int ks = q * q * q * q;
    for (int i = 0; i < ks; i++) idxt[i] = -1;
    N = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (N >= MAXG) return 0;
                    gm[N][0] = a; gm[N][1] = b; gm[N][2] = c; gm[N][3] = e;
                    idxt[own] = N;
                    N++;
                }
    eid = mlookup(1, 0, 0, 1);
    for (int x = 0; x < N; x++)
        invt[x] = mlookup(gm[x][3], (q - gm[x][1]) % q, (q - gm[x][2]) % q, gm[x][0]);
    return N;
}

/* Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void build_meta(int m, int k, int r) {
    gtype = 1;
    gmm = m;
    gmk = k;
    N = m * k;
    eid = 0;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        powr[b] = (int)p;
        p = (p * r) % m;
    }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        long t = ((long)powr[nb] * a) % m;
        int ia = (int)((m - t) % m);
        invt[x] = ia * k + nb;
    }
}

static int gmul(int x, int y) {
    if (gtype == 1) {
        int a = x / gmk, b = x % gmk, c = y / gmk, dd = y % gmk;
        long fa = ((long)a + (long)powr[b] * c) % gmm;
        int fb = (b + dd) % gmk;
        return (int)fa * gmk + fb;
    }
    const int *X = gm[x], *Y = gm[y];
    return mlookup((X[0] * Y[0] + X[1] * Y[2]) % GQ, (X[0] * Y[1] + X[1] * Y[3]) % GQ,
                   (X[2] * Y[0] + X[3] * Y[2]) % GQ, (X[2] * Y[1] + X[3] * Y[3]) % GQ);
}

static int ginv(int x) { return invt[x]; }

static long pw_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

/* Uniformly pick a valid (m,k,r) with m*k = Nn. Returns 0 if none. */
static int pick_meta(long Nn, int *pm, int *pk, int *pr) {
    long total = 0;
    for (int pass = 0; pass < 2; pass++) {
        long target = -1;
        if (pass == 1) {
            if (total <= 0) return 0;
            target = (long)rndint((int)total);
        }
        long idx = 0;
        for (long k = 1; k <= Nn; k++) {
            if (Nn % k) continue;
            long m = Nn / k;
            if (m == 1) {
                if (pass == 0) total++;
                else if (idx++ == target) { *pm = 1; *pk = (int)k; *pr = 0; return 1; }
                continue;
            }
            for (long r = 1; r < m; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (pw_mod(r, k, m) != 1 % m) continue;
                if (pass == 0) total++;
                else if (idx++ == target) { *pm = (int)m; *pk = (int)k; *pr = (int)r; return 1; }
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ base graph and lift */

static int B, bA, E, M;
static int eu[MAXE], ew[MAXE], slA[MAXE], slB[MAXE], gv[MAXE];
static int inc[MAXB][MAXDEG];
static int NB[MAXM * MAXDEG];
static int stamp_[MAXM];
static int tick_ = 0;
static int qv[MAXM];

/* d-regular bipartite base with bA + bA vertices; A stubs matched to B stubs by a random permutation. */
static void build_base(int b) {
    B = b;
    bA = b / 2;
    E = bA * d;
    int perm[MAXE];
    for (int i = 0; i < E; i++) perm[i] = i;
    for (int i = E - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    for (int s = 0; s < E; s++) {
        int t = perm[s];
        int e = s;
        eu[e] = s / d;
        slA[e] = s % d;
        ew[e] = bA + t / d;
        slB[e] = t % d;
        inc[eu[e]][slA[e]] = e;
        inc[ew[e]][slB[e]] = e;
    }
}

/* Random voltages; parallel base edges (same endpoints) must carry distinct voltages. */
static int init_volt(void) {
    for (int e = 0; e < E; e++) {
        int ok = 0;
        for (int tries = 0; tries < 20000 && !ok; tries++) {
            int g = rndint(N);
            int clash = 0;
            for (int e2 = 0; e2 < e; e2++)
                if (eu[e2] == eu[e] && ew[e2] == ew[e] && gv[e2] == g) { clash = 1; break; }
            if (!clash) { gv[e] = g; ok = 1; }
        }
        if (!ok) return 0;
    }
    return 1;
}

static void fill_edge_nb(int e, int g) {
    int gi = ginv(g);
    int ea = eu[e], eb = ew[e];
    for (int x = 0; x < N; x++) {
        NB[(long)(ea * N + x) * d + slA[e]] = eb * N + gmul(x, g);
        NB[(long)(eb * N + x) * d + slB[e]] = ea * N + gmul(x, gi);
    }
}

static int ball(int src) {
    if (++tick_ == 0x7fffffff) {
        memset(stamp_, 0, sizeof stamp_);
        tick_ = 1;
    }
    int head = 0, tail = 0;
    stamp_[src] = tick_;
    qv[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qv[head];
            const int *nb = NB + (long)v * d;
            for (int j = 0; j < d; j++) {
                int u = nb[j];
                if (stamp_[u] != tick_) { stamp_[u] = tick_; qv[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Total number of (base representative, vertex) pairs at distance > D. 0 means valid. */
static long cost_now(void) {
    long c = 0;
    for (int u = 0; u < B; u++) c += (long)(M - ball(u * N + eid));
    return c;
}

/* Simulated annealing over the voltages. Returns 1 when the lift has diameter <= D. */
static int anneal(double until) {
    const long L = 40000;
    M = B * N;
    if (!init_volt()) return 0;
    for (int e = 0; e < E; e++) fill_edge_nb(e, gv[e]);
    long cur = cost_now();
    long it = 0;
    const double T0 = 2.5, T1 = 0.05;
    for (;;) {
        if (cur == 0) return 1;
        if ((it & 127) == 0 && now() > until) return 0;
        it++;
        long pos = it % L;
        if (pos == 0) {
            if (!init_volt()) return 0;
            for (int e = 0; e < E; e++) fill_edge_nb(e, gv[e]);
            cur = cost_now();
            continue;
        }
        double T = T0 * pow(T1 / T0, (double)pos / (double)L);
        int e = rndint(E);
        int g = rndint(N);
        if (g == gv[e]) continue;
        int bad = 0;
        for (int j = 0; j < d; j++) {
            int e2 = inc[eu[e]][j];
            if (e2 != e && ew[e2] == ew[e] && gv[e2] == g) { bad = 1; break; }
        }
        if (bad) continue;
        int old = gv[e];
        fill_edge_nb(e, g);
        gv[e] = g;
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            fill_edge_nb(e, old);
            gv[e] = old;
        }
    }
}

/* ------------------------------------------------------------ best solution and output */

#define MAXOUT_CHECK MAXOUT
static int bestCount = -1, bestMv = 0;
static int bestU[MAXOUT], bestV[MAXOUT];

static void save_best(void) {
    int c = 0;
    for (int e = 0; e < E; e++)
        for (int x = 0; x < N; x++) {
            if (c >= MAXOUT_CHECK) return;
            bestU[c] = eu[e] * N + x;
            bestV[c] = ew[e] * N + gmul(x, gv[e]);
            c++;
        }
    bestCount = c;
    bestMv = B * N;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

typedef struct { int b, q, psl; } MatCand;

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
    double t_end = t0 + limit * 0.88;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) {
        print_complete();
        return 0;
    }

    long mooreB = moore_bound();
    bestMv = 2 * d;
    bestCount = -1;

    /* 1. Explicit matrix-group candidates (secure fallback first). */
    static const MatCand mats[] = {
        {2, 13, 0},   /* SL(2,13), order 2184 -> 4368 */
        {4, 11, 0},   /* SL(2,11), order 1320 -> 5280 */
        {8, 11, 1},   /* PSL(2,11), order 660 -> 5280 */
        {2, 17, 1},   /* PSL(2,17), order 2448 -> 4896 */
        {2, 19, 1}    /* PSL(2,19), order 3420 -> 6840 */
    };
    for (unsigned i = 0; i < sizeof mats / sizeof mats[0]; i++) {
        int b = mats[i].b, q = mats[i].q, psl = mats[i].psl;
        long ord = (long)q * ((long)q * q - 1);
        if (psl) ord /= 2;
        long Mc = (long)b * ord;
        if (Mc <= bestMv || Mc > mooreB || Mc > MAXM) continue;
        double rem = t_end - now();
        if (rem < 0.5) break;
        double slice = rem < 4.0 ? rem : 4.0;
        if (build_matrix(q, psl) == 0) continue;
        build_base(b);
        if (anneal(now() + slice)) save_best();
    }

    /* 2. Ladder over metacyclic groups: each target strictly above the best so far. */
    static const int bchoices[] = {4, 4, 6, 6, 8, 2, 10};
    int nbch = (int)(sizeof bchoices / sizeof bchoices[0]);
    int fails = 0;
    for (;;) {
        double rem = t_end - now();
        if (rem < 0.5) break;
        int b = bchoices[rndint(nbch)];
        long Nmin = ((long)bestMv + b) / b;
        if (Nmin * b > mooreB || Nmin * b > MAXM) break;
        long span = Nmin / 8 + 2;
        long Nn = Nmin + (long)rndint((int)span);
        if (Nn * b > mooreB || Nn * b > MAXM || Nn > MAXG) Nn = Nmin;
        int m, k, r;
        if (!pick_meta(Nn, &m, &k, &r)) {
            if (++fails > 1000) break;
            continue;
        }
        build_meta(m, k, r);
        build_base(b);
        double slice = rem < 3.5 ? rem : 3.5;
        if (anneal(now() + slice)) save_best();
    }

    if (bestCount < 0) {
        print_complete();
        return 0;
    }
    printf("%d %d\n", bestMv, bestCount);
    for (int i = 0; i < bestCount; i++) printf("%d %d\n", bestU[i], bestV[i]);
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
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
