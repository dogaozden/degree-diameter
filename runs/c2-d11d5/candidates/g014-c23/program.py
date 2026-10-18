"""Bi-Cayley lift search, with the core search moved into C.

The parent searched voltage lifts over semidirect products Z_m x| Z_k with numpy. This version
runs the whole lift search in a C engine: random base sizes K = 1..6, random semidirect groups
of order near a ratcheting goal, and simulated annealing over voltages and layer permutations.
Each candidate is a d-regular bipartite lift, so it is simple and bipartite by construction
(duplicate darts are penalised). Validity is checked by a bit-parallel reachability count over
block representatives, which is exact because the group acts by automorphisms.

Exact small constructions (projective planes, Araujo-Pardo/Lopez, generalized quadrangles) are
kept for the calibration cases. K_{d,d} is the fallback. Every returned graph is checked with
lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift search over Z_M x|_r Z_K2 with K base vertices per side.
 * Usage:  prog d D seed time_limit
 * Output: "n m" then m edges "u v" of the best valid d-regular bipartite lift found.
 *         "0 0" if nothing valid was found.
 *
 * Vertex A_{i,g} = i*G + g, B_{p,h} = (K+p)*G + h, where G = M*K2 and elements are a*K2+b.
 * Layer l joins A_i to B_{perm[l][i]} with voltage vol[l][i]: A_{i,g} ~ B_{p, g*s}.
 * Each layer is a perfect matching of blocks, so the graph is d-regular and bipartite.
 * Diameter <= D holds iff every vertex is within distance D of every block representative.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 6
#define MAXD 24
#define MAXG 8192
#define MAXN (2 * MAXK * MAXG)
#define MAXPW 16

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

/* Group state. */
static int M, K2, G;
static int pw[MAXPW];          /* pw[b] = r^b mod M */

static int gmul(int x, int y) {
    int a1 = x / K2, b1 = x % K2, a2 = y / K2, b2 = y % K2;
    int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % M);
    int b = (b1 + b2) % K2;
    return a * K2 + b;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int ia = (int)((M - ((long long)pw[nb] * a) % M) % M);
    return ia * K2 + nb;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcd_l(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void setgroup(long mm, int k2, long r) {
    M = (int)mm;
    K2 = k2;
    G = M * K2;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * r % M);
}

static int sample_group(double target) {
    static const int K2LIST[12] = {1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    for (int attempt = 0; attempt < 300; attempt++) {
        int k2 = K2LIST[rndint(12)];
        long mm = (long)ceil(target / k2) + rndint(3);
        if (mm < 2) mm = 2;
        if (mm > MAXG / k2) mm = MAXG / k2;
        if (mm < 2) continue;
        if (k2 == 1) {
            setgroup(mm, 1, 1);
            return 1;
        }
        for (int tries = 0; tries < 300; tries++) {
            long r;
            if (tries == 0 && k2 == 2) r = mm - 1;
            else r = 1 + rndint((int)(mm - 1));
            if (gcd_l(r, mm) != 1 || powmod_l(r, k2, mm) != 1 % mm) continue;
            setgroup(mm, k2, r);
            return 1;
        }
    }
    return 0;
}

/* Lift state. */
static int K;
static int perm[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN];
static int *bu = NULL, *bv = NULL;
static int bestN = 0;
static long bestM = 0;

static void set_dart(int l, int i) {
    int p = perm[l][i], s = vol[l][i];
    int si = ginv(s);
    int ai = i * G, bp = (K + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ai + g] = bp + gmul(g, s);
        nbr[l][bp + g] = ai + gmul(g, si);
    }
}

/* Number of (vertex, block representative) pairs at distance > D. */
static long count_unreached(void) {
    int N = 2 * K * G;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t r = cur[v];
            for (int l = 0; l < d; l++) r |= cur[nbr[l][v]];
            nxt[v] = r;
            changed |= (r != cur[v]);
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long have = 0;
    for (int v = 0; v < N; v++) have += __builtin_popcountll(cur[v]);
    return (long)(2 * K) * N - have;
}

/* Duplicate darts: same (block i, partner p, voltage s) in two layers. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && vol[l1][i] == vol[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    return count_unreached() + (long)(2 * K * G) * dup_count();
}

static void save_best(void) {
    int A = K * G;
    long m = 0;
    for (int l = 0; l < d; l++)
        for (int v = 0; v < A; v++) {
            bu[m] = v;
            bv[m] = nbr[l][v];
            m++;
        }
    bestM = m;
    bestN = 2 * A;
}

/* One annealing run from a random lift. Returns the final cost (0 means valid). */
static long sa_trial(long max_iter, long patience, double until) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            perm[l][i] = p[i];
            vol[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);

    long cost = full_cost();
    long best = cost, last = 0;
    for (long it = 0; it < max_iter && cost > 0; it++) {
        if ((it & 31) == 0 && now() > until) break;
        if (it - last > patience) break;
        double T = 0.3 + 0.02 * (double)cost * (1.0 - (double)it / (double)max_iter);

        if (K >= 2 && rnd01() < 0.35) {
            int l = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndint(d);
            int i = rndint(K);
            int old = vol[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[l][i] = nw;
            set_dart(l, i);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                vol[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < best) {
            best = cost;
            last = it;
        }
    }
    return cost;
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
    double t_end = now() + limit;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    bu = malloc(sizeof(int) * (size_t)MAXD * MAXK * MAXG);
    bv = malloc(sizeof(int) * (size_t)MAXD * MAXK * MAXG);
    if (!bu || !bv) {
        printf("0 0\n");
        return 0;
    }

    double moore = 0.0, pwr = 1.0;
    for (int i = 0; i < D; i++) {
        moore += pwr;
        pwr *= (d - 1);
        if (moore > 1e9) break;
    }
    moore *= 2.0;
    double goal = 0.12 * moore;

    int trials[MAXK + 1], wins[MAXK + 1];
    for (int c = 0; c <= MAXK; c++) {
        trials[c] = 0;
        wins[c] = 0;
    }

    while (now() < t_end - 0.2) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bsc = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bsc) {
                    bsc = sc;
                    k = c;
                }
            }
        }

        double tg = goal / (2.0 * k);
        if (!sample_group(tg)) {
            goal = fmax(goal * 0.99, bestN * 1.02);
            continue;
        }
        K = k;
        int N = 2 * K * G;
        if (N <= bestN) {
            goal = bestN * 1.02 + 1.0;
            continue;
        }
        trials[k]++;
        long c = sa_trial(20000, 3000, t_end);
        if (c == 0) {
            wins[k]++;
            save_best();
            goal = bestN * 1.04;
        } else {
            goal = fmax(goal * 0.99, bestN * 1.02);
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestN, bestM);
    for (long e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept for calibration cases and D = 3, 4).
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
# Saturation: add every legal missing edge between deficient opposite-side vertices.
# Distances only shrink, so validity is kept. Results are re-checked by callers.
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

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best
    best_n = best[0]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

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
    if D == 4 and d >= 3:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C bi-Cayley lift annealing over semidirect groups.
    # It runs under its own deadline, so the Python side only needs to parse and check.
    remaining = final - time.monotonic()
    if remaining > 6.0:
        c_budget = remaining - 4.0
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=None, timeout=remaining + 2.0)
            n, e = lib.parse_graph_text(text)
            if n > 0:
                consider_saturated(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
