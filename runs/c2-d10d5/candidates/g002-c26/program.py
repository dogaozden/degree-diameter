"""Bi-Cayley lift search in C with 64-bit reach masks (base blocks up to 12 per side),
an iterated local search (elite-preserving ruin-and-recreate) on top of simulated annealing,
a bandit over base sizes and group orders, and exact constructions for D = 3."""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search for bipartite degree-diameter graphs.
 *
 * Usage:  prog d D seed time_limit   (stdin is read and ignored)
 * stdout: "n m" then m lines "u v" for the largest valid graph found.
 *
 * Model: group H = Z_M x|_r Z_K (order G = M*K, element a*K+b, (a,b)(c,e) = (a+r^b c, b+e)).
 * Base has kb blocks per side. A-vertex (i,x) = i*G+x, B-vertex (j,h) = (kb+j)*G+h.
 * Layer l pairs A-block i with B-block perm[l][i] through voltage S[l][i]:
 *   (i,x) ~ (perm, x*s). Each layer is a permutation, so the graph is d-regular.
 * Validity: left multiplication is an automorphism, so it suffices that every block
 * representative reaches all 2*kb*G vertices within D steps (64-bit mask per vertex,
 * one bit per representative), and no (block, block, voltage) triple is repeated.
 *
 * Search (new): iterated local search. Each round runs simulated annealing from the
 * current state; between rounds the elite (lowest-cost) state is reloaded and a
 * ruin-and-recreate step rerandomises roughly 1/6 of the darts, so the search keeps
 * exploring near good lifts instead of restarting from scratch.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXKB 12
#define MAXK 12
#define MAXN 40000
#define MAXG 40000
#define MAXE (MAXN * MAXD / 2 + 8)
#define PEN 1000L

typedef uint64_t mask_t;

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

static int GM, GK, G;        /* group Z_GM x| Z_GK, order G */
static int rp[64];           /* rp[b] = r^b mod GM */

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

static int kb, NN, bits;
static mask_t fullmask;
static int perm[MAXD][MAXKB], pinv[MAXD][MAXKB], S[MAXD][MAXKB];
static int nb[MAXD][MAXN];
static mask_t bufA[MAXN], bufB[MAXN];
static const mask_t *last;

static int sv_perm[MAXD][MAXKB], sv_S[MAXD][MAXKB];   /* best state of the current anneal */
static int gb_perm[MAXD][MAXKB], gb_S[MAXD][MAXKB];   /* elite state across ILS rounds */

static int bestU[MAXE], bestV[MAXE], bestE, bestN;

static void set_dart(int l, int i) {
    int j = perm[l][i], s = S[l][i], si = ginv(s);
    int ba = i * G, bb = (kb + j) * G;
    for (int x = 0; x < G; x++) {
        nb[l][ba + x] = bb + gmul(x, s);
        nb[l][bb + x] = ba + gmul(x, si);
    }
}

static void set_all_darts(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < kb; i++) set_dart(l, i);
}

static void swap_perm(int l, int i1, int i2) {
    int t = perm[l][i1];
    perm[l][i1] = perm[l][i2];
    perm[l][i2] = t;
    pinv[l][perm[l][i1]] = i1;
    pinv[l][perm[l][i2]] = i2;
}

static void save_sv(void) {
    memcpy(sv_perm, perm, sizeof perm);
    memcpy(sv_S, S, sizeof S);
}

static void load_from(int P[MAXD][MAXKB], int Sv[MAXD][MAXKB]) {
    memcpy(perm, P, sizeof perm);
    memcpy(S, Sv, sizeof S);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < kb; i++) pinv[l][perm[l][i]] = i;
    set_all_darts();
}

/* Unreached (representative, vertex) pairs. Sets `last` to the reach table. */
static long evaluate(void) {
    mask_t *cur = bufA, *nx = bufB;
    int N = NN;
    memset(cur, 0, sizeof(mask_t) * (size_t)N);
    for (int b = 0; b < bits; b++) cur[(long)b * G] |= (mask_t)1 << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            mask_t acc = cur[v];
            for (int l = 0; l < d; l++) acc |= cur[nb[l][v]];
            nx[v] = acc;
        }
        mask_t *t = cur;
        cur = nx;
        nx = t;
    }
    long unr = (long)bits * N;
    for (int v = 0; v < N; v++) unr -= __builtin_popcountll(cur[v]);
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
    }
    set_all_darts();
}

/* Simulated annealing from the current state. Leaves the best state seen in sv_*.
 * Returns the best cost. */
static long anneal(long iters, long patience) {
    long cost = full_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_c = cost, last_imp = 0;
    save_sv();
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > t_end) break;
        if (t - last_imp > patience) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (kb >= 2 && rnd01() < 0.2) {
            int l = rndint(d), i1 = rndint(kb), i2 = rndint(kb - 1);
            if (i2 >= i1) i2++;
            swap_perm(l, i1, i2);
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best_c) { best_c = cost; last_imp = t; save_sv(); }
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
                if (last[u] != fullmask) { v = u; break; }
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
            if (cost < best_c) { best_c = cost; last_imp = t; save_sv(); }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return best_c;
}

/* Iterated local search: anneal, then repeatedly reload the elite state, ruin part of it,
 * and anneal again. Returns 0 if a valid lift was found (its state is in sv_*), else the
 * best cost reached. */
static long lift_search(long iters, long patience, int rounds) {
    random_lift();
    long gbest = anneal(iters, patience);
    if (gbest == 0) return 0;
    memcpy(gb_perm, sv_perm, sizeof sv_perm);
    memcpy(gb_S, sv_S, sizeof sv_S);
    for (int r = 1; r < rounds && now() < t_end; r++) {
        load_from(gb_perm, gb_S);
        int nr = 1 + (d * kb) / 6;
        for (int q = 0; q < nr; q++) {
            int l = rndint(d), i = rndint(kb);
            if (rnd01() < 0.6) {
                S[l][i] = rndint(G);
            } else {
                int i2 = rndint(kb);
                if (i2 != i) swap_perm(l, i, i2);
            }
        }
        set_all_darts();
        long c = anneal(iters, patience);
        if (c == 0) return 0;
        if (c < gbest) {
            gbest = c;
            memcpy(gb_perm, sv_perm, sizeof sv_perm);
            memcpy(gb_S, sv_S, sizeof sv_S);
        }
    }
    return gbest;
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

/* ---------------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
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

    long moore = moore_bound();
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
        bits = 2 * kb;
        fullmask = (bits >= 64) ? ~(mask_t)0 : (((mask_t)1 << bits) - 1);
        NN = 2 * kb * G;
        if (NN <= bestN || NN > moore || NN > MAXN) continue;

        trials[k]++;
        if (lift_search(20000, 3000, 6) == 0) {
            wins[k]++;
            load_from(sv_perm, sv_S);
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

    budget = 0.85 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget > 1.0:
        timeout = max(1.0, time_limit - (time.monotonic() - t0) - 2.0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=timeout)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass

    return best
