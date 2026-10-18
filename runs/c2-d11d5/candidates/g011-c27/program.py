"""Combined program: a C-native bi-Cayley voltage-lift annealer, plus exact constructions as fallbacks.

New helper (C side): orbit-reduced evaluation. A lift over Z_m x| Z_k2 is invariant under left
multiplication by the group, which acts regularly on every block. So the diameter test needs BFS from
only the 2k block representatives, not from all 2kG vertices. The neighbour table is updated
incrementally when one voltage or one layer pair changes, so each annealing step costs O(d*k*G)
instead of a full bitset closure. The whole search runs in C, which is far faster than the numpy loop.

Every returned graph is checked with lib.is_valid. K_{d,d} (or a known construction) is the fallback.
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

#define MAXD 32
#define MAXK 4
#define MAXN 40000
#define MAXG 20000
#define PEN 1000L
#define ITERS 20000L
#define PATIENCE 3000L

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
static long rndl(long k) { return (long)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

/* Group Z_GM x| Z_GK2 with action r: element a*GK2 + b, (a,b)*(c,e) = (a + r^b c, b + e). */
static long GM, GK2, GR, G;
static long pw[64];

static long gmul(long x, long y) {
    long a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    long A = (a + pw[b] * c) % GM;
    long B = (b + e) % GK2;
    return A * GK2 + B;
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

/* Lift state: A-block i, vertex i*G+g; B-block p, vertex (K+p)*G+h.
 * Layer l pairs A-block i with B-block layers[l][i] through voltage S[l][i]:
 * A_{i,g} ~ B_{p, g*s}. Every vertex has exactly one neighbour per layer. */
static int K;
static int layers[MAXD][MAXK];
static long S[MAXD][MAXK];
static long NV;
static int nb[MAXN * MAXD];      /* nb[v*d + l] */
static int bestNb[MAXN * MAXD];
static long bestN = 0, bestK = 0, bestG = 0;
static int found = 0;
static int queue_buf[MAXN];
static int seen[MAXN];
static int seen_stamp = 0;
static int mk[MAXK * MAXK * MAXG];
static int mk_stamp = 0;

/* Rewrite every neighbour entry of layer l that involves A-block i (and its B partner block). */
static void set_block(int l, int i) {
    long s = S[l][i];
    int p = layers[l][i];
    long A0 = (long)i * G, B0 = (long)(K + p) * G;
    for (long g = 0; g < G; g++) {
        long h = gmul(g, s);
        nb[(A0 + g) * d + l] = (int)(B0 + h);
        nb[(B0 + h) * d + l] = (int)(A0 + g);
    }
}

/* Number of vertices within distance D of src (BFS over the neighbour table). */
static long reach_count(long src) {
    seen_stamp++;
    int head = 0, tail = 0;
    queue_buf[tail++] = (int)src;
    seen[src] = seen_stamp;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int v = queue_buf[head++];
            const int *row = nb + (long)v * d;
            for (int l = 0; l < d; l++) {
                int u = row[l];
                if (seen[u] != seen_stamp) {
                    seen[u] = seen_stamp;
                    queue_buf[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Cost = unreached (representative, vertex) pairs + penalty per duplicate (i, p, s) triple.
 * By group transitivity on blocks, zero cost means every pair is within distance D. */
static long evaluate(void) {
    long cost = 0;
    for (int b = 0; b < 2 * K; b++) cost += NV - reach_count((long)b * G);
    mk_stamp++;
    long dup = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            long key = ((long)i * K + layers[l][i]) * G + S[l][i];
            if (mk[key] == mk_stamp) dup++;
            else mk[key] = mk_stamp;
        }
    return cost + PEN * dup;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = (int)rndl(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            layers[l][i] = perm[i];
            S[l][i] = rndl(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_block(l, i);
}

/* Simulated annealing with stagnation cutoff. Returns the final cost (0 = success). */
static long anneal(double deadline, long iters, long patience) {
    random_init();
    long cost = evaluate();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long last = 0, bestc = cost;
    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 15) == 0 && now() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (K >= 2 && rnd01() < 0.25) {
            int l = (int)rndl(d);
            int i1 = (int)rndl(K);
            int i2 = (int)rndl(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_block(l, i1);
            set_block(l, i2);
            c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_block(l, i1);
                set_block(l, i2);
            }
        } else {
            int l = (int)rndl(d);
            int i = (int)rndl(K);
            long old = S[l][i];
            long nw = rndl(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_block(l, i);
            c2 = evaluate();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                S[l][i] = old;
                set_block(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; }
    }
    return cost;
}

static const long CHOICES[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Sample Z_m x| Z_k2 with at least about target elements and 2*k*G <= cap. */
static int sample_group(long target, int k, long cap) {
    for (int att = 0; att < 300; att++) {
        long k2 = CHOICES[rndl(20)];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long g = m * k2;
        if (2L * k * g > cap || g > MAXG) continue;
        long r = 1;
        if (k2 > 1) {
            int ok = 0;
            for (int tr = 0; tr < 80 && !ok; tr++) {
                long c = 1 + rndl(m - 1);
                if (gcd_l(c, m) != 1) continue;
                if (powmod(c, k2, m) != 1 % m) continue;
                r = c;
                ok = 1;
            }
            if (!ok) r = 1; /* direct product Z_m x Z_k2 is always valid */
        }
        GM = m; GK2 = k2; GR = r; G = g;
        pw[0] = 1 % m;
        for (long b = 1; b < k2; b++) pw[b] = pw[b - 1] * r % m;
        return 1;
    }
    return 0;
}

static void print_best(void) {
    long nA = bestK * bestG;
    printf("%ld %ld\n", bestN, nA * d);
    for (long v = 0; v < nA; v++)
        for (int l = 0; l < d; l++)
            printf("%ld %d\n", v, bestNb[v * d + l]);
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
    long minN = argc > 5 ? atol(argv[5]) : 0;
    double t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 16; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    bestN = minN;
    found = 0;
    double goal = minN * 1.05 + 2.0;
    if (goal > cap) goal = (double)cap;

    long trials[MAXK + 1], wins[MAXK + 1];
    for (int c = 0; c <= MAXK; c++) { trials[c] = 0; wins[c] = 0; }

    while (now() < t_end) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + (int)rndl(MAXK);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        long target = (long)(goal / (2.0 * k)) + rndl(3);
        if (target < 2) target = 2;
        if (!sample_group(target, k, cap)) {
            double g2 = bestN * 1.02 + 2.0, g3 = goal * 0.99;
            goal = g2 > g3 ? g2 : g3;
            if (goal > cap) goal = (double)cap;
            continue;
        }
        if (2L * k * G <= bestN) {
            double g2 = bestN * 1.02 + 2.0;
            if (goal < g2) goal = g2;
            if (goal > cap) goal = (double)cap;
            continue;
        }
        K = k;
        NV = 2L * K * G;
        trials[k]++;
        long c = anneal(t_end, ITERS, PATIENCE);
        if (c == 0) {
            wins[k]++;
            if (NV > bestN) {
                memcpy(bestNb, nb, sizeof(int) * (size_t)(NV * d));
                bestN = NV;
                bestK = K;
                bestG = G;
                found = 1;
            }
            if (goal < NV * 1.04) goal = NV * 1.04;
            if (goal > cap) goal = (double)cap;
        } else {
            double g2 = bestN * 1.02 + 2.0, g3 = goal * 0.99;
            goal = g2 > g3 ? g2 : g3;
            if (goal > cap) goal = (double)cap;
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (fallbacks and calibration cases).
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

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main phase: the C annealer searches bi-Cayley lifts with more vertices than best_n.
    # The C budget leaves room for the compile step and for validation of the output.
    remaining = final - time.monotonic() - 2.0
    if D >= 2 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             timeout=remaining + 15)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
