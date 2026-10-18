"""Lift search with a C-native G-invariant annealer.

New routine: bi-Cayley lifts over semidirect groups Z_m x| Z_k2 are searched inside C.
Left multiplication by the group is an automorphism of every lift, so coverage only has to be
checked from the 2k block representatives. The cost is the number of missing (vertex, representative)
pairs, computed with 2k-bit reach masks in D rounds. Each evaluation is O(D*d*N) with no Python
overhead, so the annealer tries far more candidates than the Python search did.

Python builds the exact constructions (projective planes, GQ, Araujo-Pardo-Lopez) and gives the
rest of the time budget to the C lift search. Every returned graph is checked with lib.is_valid,
and K_{d,d} is the fallback.
"""
import itertools
import math
import time

import lib


LIFT_C = r'''
/* G-invariant bi-Cayley lift search.
 * Usage: prog d D seed time_limit base_n
 * Output: "n m" + edges of the best lift with n > base_n, or "0 0".
 *
 * Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h, with group elements g in [0,G).
 * Layer l pairs A_i with B_{perm[l][i]} through voltage Vol[l][i]: A_{i,g} ~ B_{p, g*s}.
 * Every layer is a permutation, so the graph is d-regular and left multiplication is an automorphism.
 * Coverage of all pairs is then equivalent to: every vertex reaches every block representative
 * i*G (i < 2K) within distance D. The cost is the number of missing (vertex, representative) pairs.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 20000
#define MAXD 24
#define MAXK 8

static int d, D;
static uint64_t rs = 0x2545F4914F6CDD1DULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

/* ---- semidirect group Z_m x| Z_k2; element a*k2+b; (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1+b2) ---- */
static int gm, gk2, gG, grr;
static int rp[64];

static int gmul(int x, int y) {
    int a1 = x / gk2, b1 = x % gk2, a2 = y / gk2, b2 = y % gk2;
    long long a = (a1 + (long long)rp[b1] * a2) % gm;
    int b = (b1 + b2) % gk2;
    return (int)a * gk2 + b;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Sample a group with order >= target (cyclic, direct, or semidirect). */
static int sample_group(long target) {
    static const int K2[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tr = 0; tr < 200; tr++) {
        int k2 = K2[rndint((int)(sizeof K2 / sizeof K2[0]))];
        long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = 1;
        if (k2 > 1 && m >= 3 && rnd01() < 0.75) {
            int ok = 0;
            for (int t = 0; t < 80 && !ok; t++) {
                int c = 2 + rndint((int)(m - 2));
                if (gcd_i(c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    ok = 1;
                }
            }
            if (!ok) continue;
        }
        gm = (int)m;
        gk2 = k2;
        gG = (int)m * k2;
        grr = r;
        long long pw = 1 % m;
        for (int b = 0; b < k2; b++) {
            rp[b] = (int)pw;
            pw = pw * r % m;
        }
        return 1;
    }
    return 0;
}

/* ---- lift state ---- */
static int K, G, N;
static int perm[MAXD][MAXK];
static int Vol[MAXD][MAXK];
static int nb[MAXN * MAXD];     /* nb[v*d + l]: neighbour of v in layer l */
static int bestNb[MAXN * MAXD];
static uint64_t bufA[MAXN], bufB[MAXN], init0[MAXN];
static unsigned char missA[MAXN], missB[MAXN];
static unsigned char *missCur = missA, *missTmp = missB;
static int bestN = 0;

static void swap_miss(void) {
    unsigned char *t = missCur;
    missCur = missTmp;
    missTmp = t;
}

/* Write layer l's darts for block i: A_{i,g} ~ B_{p, g*s}; B entries follow by bijectivity. */
static void set_dart(int l, int i) {
    int p = perm[l][i], s = Vol[l][i];
    int bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        nb[(size_t)(i * G + g) * d + l] = bb + h;
        nb[(size_t)(bb + h) * d + l] = i * G + g;
    }
}

/* Count missing (vertex, representative) pairs after D rounds of OR-propagation. */
static long eval_cost(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    memcpy(cur, init0, sizeof(uint64_t) * (size_t)N);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            const int *row = nb + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[row[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long total = 0;
    int full = 2 * K;
    for (int v = 0; v < N; v++) {
        int m = full - __builtin_popcountll(cur[v]);
        missTmp[v] = (unsigned char)m;
        total += m;
    }
    return total;
}

static int dup_block(int i) {
    for (int l = 0; l < d; l++)
        for (int l2 = l + 1; l2 < d; l2++)
            if (perm[l][i] == perm[l2][i] && Vol[l][i] == Vol[l2][i]) return 1;
    return 0;
}

static int dup_prefix(int l, int i) {
    for (int l2 = 0; l2 < l; l2++)
        if (perm[l][i] == perm[l2][i] && Vol[l][i] == Vol[l2][i]) return 1;
    return 0;
}

static int init_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int ok = 0;
            for (int t = 0; t < 200 && !ok; t++) {
                Vol[l][i] = rndint(G);
                if (!dup_prefix(l, i)) ok = 1;
            }
            if (!ok) return 0;
        }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
    return 1;
}

static int metropolis(long c2, long cost, double T) {
    if (c2 <= cost) return 1;
    return rnd01() < exp(-(double)(c2 - cost) / T);
}

/* One annealing run on the current (K, G). Returns 1 with nb valid on success. */
static int search_run(double deadline, long max_iters, long patience) {
    if (!init_state()) return 0;
    long cost = eval_cost();
    swap_miss();
    long best = cost, last = 0;
    double c0 = cost > 1 ? (double)cost : 1.0;
    for (long it = 0; it < max_iters && cost > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        if (it - last > patience) break;
        double T = 0.02 * c0 * (1.0 - (double)it / (double)max_iters);
        if (T < 0.3) T = 0.3;
        long c2;
        if (K >= 2 && rndint(100) < 15) {
            /* Move: swap the targets of two blocks inside one layer (voltages stay with blocks). */
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = t;
            if (dup_block(i1) || dup_block(i2)) {
                t = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = t;
                continue;
            }
            set_dart(l, i1);
            set_dart(l, i2);
            c2 = eval_cost();
            if (metropolis(c2, cost, T)) {
                cost = c2;
                swap_miss();
                if (cost < best) {
                    best = cost;
                    last = it;
                }
            } else {
                t = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            /* Move: change one voltage, biased toward an uncovered vertex half the time. */
            int l = rndint(d), i = rndint(K);
            if (rnd01() < 0.5) {
                int v = -1;
                for (int t = 0; t < 20 && v < 0; t++) {
                    int c = rndint(N);
                    if (missCur[c]) v = c;
                }
                if (v >= 0) {
                    int blk = v / G;
                    if (blk < K) {
                        i = blk;
                    } else {
                        for (int ii = 0; ii < K; ii++)
                            if (perm[l][ii] == blk - K) {
                                i = ii;
                                break;
                            }
                    }
                }
            }
            int old = Vol[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            Vol[l][i] = nw;
            if (dup_block(i)) {
                Vol[l][i] = old;
                continue;
            }
            set_dart(l, i);
            c2 = eval_cost();
            if (metropolis(c2, cost, T)) {
                cost = c2;
                swap_miss();
                if (cost < best) {
                    best = cost;
                    last = it;
                }
            } else {
                Vol[l][i] = old;
                set_dart(l, i);
            }
        }
    }
    return cost == 0;
}

static int pick_k(const long *wins, const long *trials) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit base_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long base_n = atol(argv[5]);
    double t0 = now();
    double deadline = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long wins[MAXK + 1] = {0}, trials[MAXK + 1] = {0};
    int found = 0;
    bestN = base_n > 0 ? (int)base_n : 0;
    double goal = bestN * 1.02 + 2.0;

    while (now() < deadline) {
        int k = pick_k(wins, trials);
        long cap = MAXN / (2L * k);
        long want = (long)ceil(goal / (2.0 * k)) + rndint(3);
        if (want < 2) want = 2;
        if (want > cap) want = cap;
        if (!sample_group(want)) continue;
        long Nc = 2L * k * gG;
        if (Nc > MAXN) continue;
        if (Nc <= bestN) {
            goal = bestN * 1.02 + 2.0;
            continue;
        }
        K = k;
        G = gG;
        N = (int)Nc;
        memset(init0, 0, sizeof(uint64_t) * (size_t)N);
        for (int b = 0; b < 2 * K; b++) init0[(size_t)b * G] = 1ULL << b;
        trials[k]++;
        if (search_run(deadline, 60000, 2500)) {
            wins[k]++;
            found = 1;
            bestN = N;
            memcpy(bestNb, nb, sizeof(int) * (size_t)N * d);
            goal = bestN * 1.03 + 2.0;
        } else {
            goal = fmax(bestN * 1.01 + 2.0, goal * 0.99);
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int half = bestN / 2;
    printf("%d %d\n", bestN, half * d);
    for (int u = 0; u < half; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, bestNb[u * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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
# Saturation: greedily add missing bipartite edges between deficient vertices.
# Distances only shrink, so validity is kept; callers still verify with lib.is_valid.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but fall back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

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
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
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

    # Main phase: the C annealer searches G-invariant lifts for the whole remaining budget.
    # Its output is always larger than best_n or "0 0", so consider() only keeps real gains.
    total = max(1.0, 0.9 * time_limit - 2.0)
    final = t0 + total
    remaining = final - time.monotonic()
    if d >= 2 and D >= 2 and remaining > 3.0:
        try:
            text = lib.run_c(LIFT_C, [d, D, seed, round(remaining, 2), best_n],
                             stdin_graph=None, timeout=remaining + 15.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
