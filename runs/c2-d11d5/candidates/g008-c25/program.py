"""Bi-Cayley lift search engine in C, with exact constructions as fallbacks.

Lifts: vertices A_{i,g} and B_{j,h} with g, h in a semidirect product Z_m x| Z_k of order G.
Layer l joins A-block i to B-block lay[l][i] with voltage vol[l][i] (A_{i,g} ~ B_{j,g*s}), so
every vertex gets degree d. The C engine anneals over layer permutations and voltages, and
grows the base size k with a bandit. Every returned graph is checked with lib.is_valid.
Fallbacks: K_{d,d}, PG(2,q), and the Araujo-Pardo/Lopez graph where applicable.
"""
import itertools
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

#define MAXD 40
#define MAXKB 8
#define MAXN 40000
#define PEN 1000L

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Group Z_gm x|_gr Z_gk; element a*gk + b; (a,b)(c,e) = (a + r^b c, b + e). */
static int gm, gk, gr, G;
static int pw[64];
static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24};
#define NK2 ((int)(sizeof(K2S) / sizeof(K2S[0])))

static int K;                       /* base blocks per side */
static int lay[MAXD][MAXKB];        /* A-block i -> B-block in layer l */
static int vol[MAXD][MAXKB];        /* voltage of A-block i in layer l */
static int nb[MAXD][MAXN];          /* neighbour of v in layer l */
static uint64_t reach[MAXN], nreach[MAXN], curreach[MAXN];
static int N;

static int best_K, best_gm, best_gk, best_gr;
static int best_lay[MAXD][MAXKB], best_vol[MAXD][MAXKB];
static long best_n;
static int has_best;

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}
static long powmod(long b, long e, long mod) {
    long r = 1 % mod;
    b %= mod;
    while (e) {
        if (e & 1) r = r * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return r;
}

static void build_pw(void) {
    pw[0] = 1 % gm;
    for (int t = 1; t < gk; t++) pw[t] = (int)((long)pw[t - 1] * gr % gm);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int t = (int)((long)pw[b] * c % gm);
    int s = a + t;
    if (s >= gm) s -= gm;
    int f = b + e;
    if (f >= gk) f -= gk;
    return s * gk + f;
}

static double moore_bound(void) {
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return 2.0 * s;
}

static uint64_t fullmask(void) {
    int b = 2 * K;
    return b >= 64 ? ~0ULL : ((1ULL << b) - 1);
}

static int sample_group(int target) {
    for (int tries = 0; tries < 300; tries++) {
        int k2 = K2S[rndint(NK2)];
        long mm = ((long)target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        int r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int t = 0; t < 60 && !found; t++) {
                long c;
                int pick = rndint(4);
                if (pick == 0) c = 1;
                else if (pick == 1) c = mm - 1;
                else c = (mm > 2) ? 2 + rndint((int)(mm - 2)) : 1;
                if (gcdl(c, mm) != 1) continue;
                if (powmod(c, k2, mm) != 1 % mm) continue;
                r = (int)c;
                found = 1;
            }
            if (!found) continue;
        }
        gm = (int)mm;
        gk = k2;
        gr = r;
        G = gm * gk;
        build_pw();
        return 1;
    }
    return 0;
}

/* Layer l: A_{i,g} ~ B_{j,g*s} with j = lay[l][i], s = vol[l][i]. */
static void set_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = lay[l][i], s = vol[l][i];
        int A = i * G, B = (K + j) * G;
        for (int g = 0; g < G; g++) {
            int h = gmul(g, s);
            nb[l][A + g] = B + h;
            nb[l][B + h] = A + g;
        }
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rndint(G);
        set_layer(l);
    }
}

static int find_block(int l, int j) {
    for (int i = 0; i < K; i++)
        if (lay[l][i] == j) return i;
    return 0;
}

/* Duplicate edges: same A-block, same B-block and same voltage in two layers. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && vol[l1][i] == vol[l2][i]) c++;
    return c;
}

/* Cost = (vertex, block) pairs at distance > D, plus penalty for duplicates.
 * By left-invariance, checking distances to block representatives from all vertices
 * is equivalent to diameter <= D. */
static long evaluate(void) {
    N = 2 * K * G;
    uint64_t full = fullmask();
    for (int v = 0; v < N; v++) reach[v] = 0;
    for (int b = 0; b < 2 * K; b++) reach[(size_t)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = reach[v];
            for (int l = 0; l < d; l++) x |= reach[nb[l][v]];
            nreach[v] = x;
            changed |= (x != reach[v]);
        }
        memcpy(reach, nreach, sizeof(uint64_t) * (size_t)N);
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++)
        unr += 2 * K - __builtin_popcountll(reach[v] & full);
    return unr + PEN * dupcount();
}

static long anneal(long iters, long patience, double deadline) {
    long cost = evaluate();
    memcpy(curreach, reach, sizeof(uint64_t) * (size_t)N);
    long best = cost, last = 0;
    double c0 = cost > 1 ? (double)cost : 1.0;
    uint64_t full = fullmask();
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 15) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.03 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.3) temp = 0.3;

        if (K >= 2 && rnd01() < 0.2) {
            /* Swap the B-targets of two A-blocks in one layer. */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_layer(l);
            long c2 = evaluate();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
                memcpy(curreach, reach, sizeof(uint64_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
                set_layer(l);
            }
            continue;
        }

        /* Change one voltage, targeting an unreached vertex half the time. */
        int l = rndint(d), i = -1, v = -1;
        if (rnd01() < 0.5) {
            for (int tr = 0; tr < 20; tr++) {
                int c = rndint(N);
                if (curreach[c] != full) { v = c; break; }
            }
        }
        if (v >= 0) {
            if (v < K * G) i = v / G;
            else i = find_block(l, v / G - K);
        } else {
            i = rndint(K);
        }
        int old = vol[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        vol[l][i] = nw;
        set_layer(l);
        long c2 = evaluate();
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
            cost = c2;
            memcpy(curreach, reach, sizeof(uint64_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            vol[l][i] = old;
            set_layer(l);
        }
    }
    return cost;
}

static void save_best(void) {
    best_K = K;
    best_gm = gm;
    best_gk = gk;
    best_gr = gr;
    memcpy(best_lay, lay, sizeof lay);
    memcpy(best_vol, vol, sizeof vol);
    best_n = 2L * K * G;
    has_best = 1;
}

static void emit_best(void) {
    K = best_K;
    gm = best_gm;
    gk = best_gk;
    gr = best_gr;
    G = gm * gk;
    build_pw();
    memcpy(lay, best_lay, sizeof lay);
    memcpy(vol, best_vol, sizeof vol);
    for (int l = 0; l < d; l++) set_layer(l);
    N = 2 * K * G;
    long m = (long)K * G * d;
    printf("%d %ld\n", N, m);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[l][v]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_n = argc > 5 ? atol(argv[5]) : 0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 3 || d >= MAXD || D < 3) { printf("0 0\n"); return 0; }

    double deadline = now() + limit * 0.95 - 0.3;
    double mb = moore_bound();
    best_n = min_n;
    has_best = 0;
    double goal = (double)best_n * 1.02;
    if (goal < 2.0 * d) goal = 2.0 * d;

    long trials[MAXKB + 1], wins[MAXKB + 1];
    memset(trials, 0, sizeof trials);
    memset(wins, 0, sizeof wins);

    while (now() < deadline) {
        int kk = 1 + rndint(MAXKB);
        if (rnd01() >= 0.2) {
            double bs = -1.0;
            for (int c = 1; c <= MAXKB; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; kk = c; }
            }
        }
        int target = (int)ceil(goal / (2.0 * kk)) + rndint(3);
        if (target < 2) target = 2;
        if (!sample_group(target)) { goal *= 0.99; continue; }
        long Nt = 2L * kk * G;
        if (Nt <= best_n) { goal = fmax(goal, best_n * 1.02); continue; }
        if (Nt > mb || Nt > MAXN) { goal *= 0.98; continue; }

        K = kk;
        trials[kk]++;
        random_state();
        double slice_end = now() + 8.0;
        if (slice_end > deadline) slice_end = deadline;
        long cost = anneal(6000, 1500, slice_end);
        if (cost == 0) {
            wins[kk]++;
            save_best();
            goal = fmax(goal, best_n * 1.03);
        } else {
            goal = fmax(best_n * 1.02, goal * 0.99);
        }
    }

    if (has_best) emit_best();
    else printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C bi-Cayley lift annealing seeded with the best exact order.
    total = max(1.0, 0.85 * time_limit - 1.5)
    budget = t0 + total - time.monotonic() - 2.0
    if d >= 3 and budget >= 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n],
                             timeout=budget + 5.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
