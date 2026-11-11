"""Bi-Cayley lift search (C) plus an unstructured bipartite search (C).

The first C run keeps the parent's bi-Cayley lift search. The second run
(mode 1) builds random d-regular bipartite graphs from d random perfect
matchings and anneals edge swaps to remove bad pairs. It binary-searches the
side size h, so a result is returned only when every pair is within D.
Each candidate is checked with lib.is_valid, and the best valid graph is returned.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search + unstructured bipartite annealing for degree-diameter graphs.
 *
 * Usage:  prog d D seed time_limit [mode] [h0]
 *   mode 0 (default): bi-Cayley lift search.  stdout: "n m" then m edge lines.
 *   mode 1: unstructured d-regular bipartite search with side size near h0.
 * stdin is read and ignored.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 4
#define MAXN 40000
#define MAXG 40000
#define MAXE (MAXN * MAXD / 2 + 8)
#define PEN 1000L

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
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

static long moore_bound(void) {
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------------- group */

static int GM, GK, G;
static int rp[64];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return ((a + rp[b] * c) % GM) * GK + (b + e) % GK;
}

static int ginv(int x) {
    int a = x / GK, b = x % GK, nb_ = (GK - b) % GK;
    int c = (int)(((long)rp[nb_] * a) % GM);
    return ((GM - c) % GM) * GK + nb_;
}

/* ---------------------------------------------------------------- lift state */

static int kb;
static int NN;
static int perm[MAXD][MAXK], pinv[MAXD][MAXK], S[MAXD][MAXK];
static int nb[MAXD][MAXN];
static uint8_t bufA[MAXN], bufB[MAXN];
static const uint8_t *last;

static int bestU[MAXE], bestV[MAXE], bestE, bestN;

static void set_dart(int l, int i) {
    int j = perm[l][i], s = S[l][i], si = ginv(s);
    int ba = i * G, bb = (kb + j) * G;
    for (int x = 0; x < G; x++) {
        nb[l][ba + x] = bb + gmul(x, s);
        nb[l][bb + x] = ba + gmul(x, si);
    }
}

static void swap_perm(int l, int i1, int i2) {
    int t = perm[l][i1];
    perm[l][i1] = perm[l][i2];
    perm[l][i2] = t;
    pinv[l][perm[l][i1]] = i1;
    pinv[l][perm[l][i2]] = i2;
}

static long evaluate(void) {
    uint8_t *cur = bufA, *nx = bufB;
    int N = NN, bits = 2 * kb;
    memset(cur, 0, N);
    for (int b = 0; b < bits; b++) cur[b * G] |= (uint8_t)(1u << b);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint8_t acc = cur[v];
            for (int l = 0; l < d; l++) acc |= cur[nb[l][v]];
            nx[v] = acc;
        }
        uint8_t *t = cur;
        cur = nx;
        nx = t;
    }
    long unr = (long)bits * N;
    for (int v = 0; v < N; v++) unr -= __builtin_popcount(cur[v]);
    last = cur;
    return unr;
}

static long full_cost(void) {
    long dup = 0;
    for (int i = 0; i < kb; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return evaluate() + PEN * dup;
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) perm[l][i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1), t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < kb; i++) {
            pinv[l][perm[l][i]] = i;
            S[l][i] = rndint(G);
        }
        for (int i = 0; i < kb; i++) set_dart(l, i);
    }
}

static int lift_trial(long iters, long patience) {
    random_lift();
    long cost = full_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_c = cost, last_imp = 0;
    int full = (1 << (2 * kb)) - 1;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > t_end) break;
        if (t - last_imp > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (kb >= 2 && rnd01() < 0.25) {
            int l = rndint(d), i1 = rndint(kb), i2 = rndint(kb - 1);
            if (i2 >= i1) i2++;
            swap_perm(l, i1, i2);
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best_c) { best_c = cost; last_imp = t; }
            } else {
                swap_perm(l, i1, i2);
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l, i;
        int v = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int u = rndint(NN);
                if (last[u] != full) { v = u; break; }
            }
        }
        if (v >= 0) {
            int blk = v / G;
            l = rndint(d);
            i = (blk < kb) ? blk : pinv[l][blk - kb];
        } else {
            l = rndint(d);
            i = rndint(kb);
        }
        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long c2 = full_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best_c) { best_c = cost; last_imp = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static void record_best(void) {
    int e = 0, half = kb * G;
    for (int u = 0; u < half; u++)
        for (int l = 0; l < d; l++) {
            bestU[e] = u;
            bestV[e] = nb[l][u];
            e++;
        }
    bestE = e;
    bestN = NN;
}

/* ---------------------------------------------------------------- unstructured mode */

#define UMAXH 4000
#define UMAXN (2 * UMAXH)
#define UMAXW ((UMAXN + 63) / 64)

static int UH, UN, UW;
static int usig[MAXD][UMAXH], usinv[MAXD][UMAXH];
static int unb2[UMAXN][MAXD];
static uint64_t *ua = NULL, *ub2 = NULL;
static int ubestH = 0;
static int ubestSig[MAXD][UMAXH];

/* Adjacency from the current permutations: A vertex i is i, B vertex j is UH+j. */
static void u_build(void) {
    for (int i = 0; i < UH; i++)
        for (int l = 0; l < d; l++) {
            unb2[i][l] = UH + usig[l][i];
            unb2[UH + i][l] = usinv[l][i];
        }
}

/* Unordered unreachable pairs within distance D (bitmask propagation). */
static long u_cost(void) {
    int N = UN, W = UW;
    uint64_t *cur = ua, *nx = ub2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nx + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int k = 0; k < d; k++) {
                const uint64_t *p = cur + (size_t)unb2[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= p[w];
            }
        }
        uint64_t *t = cur;
        cur = nx;
        nx = t;
    }
    long ones = 0;
    for (size_t i = 0; i < (size_t)N * W; i++) ones += __builtin_popcountll(cur[i]);
    long unr = (long)N * N - ones;
    return unr / 2;
}

static long u_full(void) {
    u_build();
    long dup = 0;
    for (int i = 0; i < UH; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (usig[l1][i] == usig[l2][i]) dup++;
    return u_cost() + 20L * dup;
}

/* Anneal toward a d-regular simple bipartite graph with side h and diameter <= D.
 * Returns 1 and stores the result in ubest* on success. */
static int u_run(int h, double deadline) {
    UH = h;
    UN = 2 * h;
    UW = (UN + 63) / 64;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < h; i++) usig[l][i] = i;
        for (int i = h - 1; i > 0; i--) {
            int j = rndint(i + 1), t = usig[l][i];
            usig[l][i] = usig[l][j];
            usig[l][j] = t;
        }
        for (int i = 0; i < h; i++) usinv[l][usig[l][i]] = i;
    }
    long cost = u_full();
    double start = now();
    double span = deadline - start;
    if (span < 0.01) return 0;
    double T0 = 20.0, T1 = 0.2;
    while (cost > 0) {
        double tn = now();
        if (tn > deadline) break;
        double frac = (tn - start) / span;
        if (frac > 1.0) frac = 1.0;
        double T = T0 * pow(T1 / T0, frac);
        int l = rndint(d);
        int i1 = rndint(h), i2 = rndint(h - 1);
        if (i2 >= i1) i2++;
        int a = usig[l][i1], b = usig[l][i2];
        usig[l][i1] = b;
        usig[l][i2] = a;
        usinv[l][b] = i1;
        usinv[l][a] = i2;
        long c2 = u_full();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            usig[l][i1] = a;
            usig[l][i2] = b;
            usinv[l][a] = i1;
            usinv[l][b] = i2;
        }
    }
    if (cost == 0) {
        ubestH = h;
        memcpy(ubestSig, usig, sizeof(usig));
        return 1;
    }
    return 0;
}

static void u_driver(int h0) {
    if (d < 2) {
        printf("0 0\n");
        return;
    }
    if (!ua) {
        ua = calloc((size_t)UMAXN * UMAXW, sizeof(uint64_t));
        ub2 = calloc((size_t)UMAXN * UMAXW, sizeof(uint64_t));
        if (!ua || !ub2) {
            printf("0 0\n");
            return;
        }
    }
    int lo = 0, hi = UMAXH + 1, h = h0;
    int found = 0;
    if (h > UMAXH) h = UMAXH;
    if (h < d) h = d;
    while (now() < t_end) {
        if (h <= lo) h = lo + 1;
        if (h >= hi) h = (lo + hi) / 2;
        if (hi - lo <= 1) break;
        double rem = t_end - now();
        double slice = rem * 0.4;
        if (u_run(h, now() + slice)) {
            found = 1;
            lo = h;
            if (hi > UMAXH) h = h + 1 + h / 100;
            else h = (lo + hi) / 2;
        } else {
            hi = h;
            h = (lo + hi) / 2;
        }
    }
    if (!found) {
        printf("0 0\n");
        return;
    }
    int hh = ubestH;
    printf("%d %d\n", 2 * hh, hh * d);
    for (int i = 0; i < hh; i++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", i, hh + ubestSig[l][i]);
}

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [mode] [h0] < start\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mode = argc > 5 ? atoi(argv[5]) : 0;
    int h0 = argc > 6 ? atoi(argv[6]) : 100;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    while (getchar() != EOF) {
    }

    if (D < 2 || d < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    if (mode == 1) {
        u_driver(h0);
        return 0;
    }

    long moore = moore_bound();
    (void)moore;
    bestN = 2 * d;
    bestE = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            bestU[bestE] = a;
            bestV[bestE] = d + b;
            bestE++;
        }

    static const int K2S[16] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 36};
    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < t_end) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        long Gt = bestN / (2L * k) + 1 + rndint((int)(bestN / (16L * 2 * k) + 2));
        int k2 = K2S[rndint(16)];
        long m = (Gt + k2 - 1) / k2;
        if (m < 1) m = 1;
        if (m > MAXG) continue;

        int r;
        if (m == 1) {
            r = 0;
        } else if (k2 == 1) {
            r = 1;
        } else {
            r = -1;
            if (k2 == 2 && rnd01() < 0.3 && gcd((int)m - 1, (int)m) == 1) r = (int)m - 1;
            for (int tr = 0; r < 0 && tr < 300; tr++) {
                int c = 1 + rndint((int)m - 1);
                if (gcd(c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) r = c;
            }
            if (r < 0) continue;
        }

        GM = (int)m;
        GK = k2;
        G = GM * GK;
        rp[0] = 1 % GM;
        for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * r % GM);
        kb = k;
        NN = 2 * kb * G;
        if (NN <= bestN || NN > moore || NN > MAXN) continue;

        trials[k]++;
        if (lift_trial(30000, 4000)) {
            wins[k]++;
            if (NN > bestN) record_best();
        }
    }

    printf("%d %d\n", bestN, bestE);
    for (int e = 0; e < bestE; e++) printf("%d %d\n", bestU[e], bestV[e]);
    return 0;
}
'''


def _exact(d, D):
    """Exact or record constructions Python builds directly (D = 3 only)."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D < 1 or d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    try:
        ex = _exact(d, D)
    except Exception:
        ex = None
    if ex is not None and lib.is_valid(ex[0], ex[1], d, D):
        if D == 3 and lib.is_prime_power(d - 1):
            return ex   # calibration: Moore graph, return instantly
        best = ex

    def remaining():
        return 0.85 * time_limit - 3.0 - (time.monotonic() - t0)

    budget = remaining()
    if budget <= 1.0:
        return best

    # Phase 1: bi-Cayley lift search (parent method), short share of the budget.
    b1 = 0.3 * budget
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(b1, 2)],
                         stdin_graph=None, timeout=max(1.0, b1 + 3.0))
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass

    # Phase 2: unstructured random-regular annealing, aiming above the current best.
    b2 = remaining() - 1.0
    if b2 > 1.0:
        h0 = best[0] // 2 + 1
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + 7, round(b2, 2), 1, h0],
                             stdin_graph=None, timeout=max(1.0, b2 + 3.0))
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass

    return best
