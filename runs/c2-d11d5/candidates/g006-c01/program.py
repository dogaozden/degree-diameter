"""Bi-Cayley lift search in C: base blocks over a semidirect group Z_m x|_r Z_q.

Construction: nb base blocks per side, group H = Z_m x|_r Z_q of order ord. Vertices are
(side, block, h). Layer l (of d layers) joins A_{i,g} to B_{P_l(i), g*s_{l,i}}, where P_l is a
permutation of the blocks. Every vertex then has degree exactly d, and the graph is bipartite.

Vertex-transitivity: left multiplication by H is an automorphism, so the diameter is <= D iff
every block identity source reaches all vertices within D steps. That is 2*nb BFS runs per
evaluation, far cheaper than the all-pairs bitset check. Simulated annealing moves voltages
and block permutations. The target order is ratcheted upward after each success.

Fallbacks: K_{d,d}, the cycle C_{2D} for d = 2, and exact projective-plane / quadrangle /
Araujo-Lopez constructions where they apply. Every result is checked with lib.is_valid.
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
#define MAXB 8
#define MAXORD 32768
#define MAXN 65536

static int d, D, NB, ORD, NV;
static long moore;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

/* group Z_GM x|_GR Z_GQ, element code a*GQ + b */
static int GM, GQ, GR;
static int pw[16];
static int ga[MAXORD], gb[MAXORD];

static int P[MAXD][MAXB], PI[MAXD][MAXB];
static int S[MAXD][MAXB], SI[MAXD][MAXB];
static int bP[MAXD][MAXB], bS[MAXD][MAXB];
static int bNB, bM, bQ, bR, bN;
static int vis[MAXN], qu[MAXN];
static int vstamp = 0;

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

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Uniform random r in [2, M-1] with gcd(r, M) = 1 and r^Q = 1 mod M, or -1 if none. */
static int pick_r(int M, int Q) {
    int chosen = -1, cnt = 0;
    for (int r = 2; r < M; r++) {
        if (gcd_i(r, M) != 1) continue;
        if (pmod(r, Q, M) != 1 % M) continue;
        cnt++;
        if (rndint(cnt) == 0) chosen = r;
    }
    return chosen;
}

static void set_group(int M, int Q, int R) {
    GM = M;
    GQ = Q;
    GR = R;
    ORD = M * Q;
    pw[0] = 1 % M;
    for (int t = 1; t < Q; t++) pw[t] = (int)((long long)pw[t - 1] * R % M);
    for (int x = 0; x < ORD; x++) {
        ga[x] = x / Q;
        gb[x] = x % Q;
    }
}

static inline int gmul(int x, int y) {
    int a = ga[x], b = gb[x], c = ga[y], e = gb[y];
    int t = (int)(((long long)pw[b] * c) % GM);
    int aa = a + t;
    if (aa >= GM) aa -= GM;
    int bb = b + e;
    if (bb >= GQ) bb -= GQ;
    return aa * GQ + bb;
}

static int ginv(int x) {
    int a = ga[x], b = gb[x];
    int nb = (GQ - b) % GQ;
    int t = (int)(((long long)pw[nb] * a) % GM);
    int na = (t == 0) ? 0 : GM - t;
    return na * GQ + nb;
}

static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < NB; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (P[l][i] == P[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Number of vertices within distance D of src (BFS, level by level). */
static int reach_from(int src) {
    if (++vstamp == 0x7fffffff) {
        memset(vis, 0, sizeof(vis));
        vstamp = 1;
    }
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = vstamp;
    for (int lv = 0; lv < D && head < tail; lv++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            int blk = v / ORD, x = v - blk * ORD;
            if (blk < NB) {
                for (int l = 0; l < d; l++) {
                    int w = (NB + P[l][blk]) * ORD + gmul(x, S[l][blk]);
                    if (vis[w] != vstamp) {
                        vis[w] = vstamp;
                        qu[tail++] = w;
                    }
                }
            } else {
                int j = blk - NB;
                for (int l = 0; l < d; l++) {
                    int i = PI[l][j];
                    int w = i * ORD + gmul(x, SI[l][i]);
                    if (vis[w] != vstamp) {
                        vis[w] = vstamp;
                        qu[tail++] = w;
                    }
                }
            }
        }
    }
    return tail;
}

/* Cost = total unreached (source, vertex) pairs over all 2*NB block identities.
 * Duplicate edges are penalised above any reachability cost. */
static long full_cost(void) {
    int dup = dup_count();
    if (dup) return (long)2 * NB * NV + dup;
    long c = 0;
    for (int i = 0; i < 2 * NB; i++) c += NV - reach_from(i * ORD);
    return c;
}

static void rebuild_inv_layer(int l) {
    for (int i = 0; i < NB; i++) {
        PI[l][P[l][i]] = i;
        SI[l][i] = ginv(S[l][i]);
    }
}

/* One simulated-annealing run on the current group. Returns 1 on success (cost 0). */
static int try_group(double until) {
    NV = 2 * NB * ORD;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < NB; i++) P[l][i] = i;
        for (int i = NB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < NB; i++) S[l][i] = rndint(ORD);
        rebuild_inv_layer(l);
    }
    long cost = full_cost();
    long best = cost, last = 0;
    const long stall = 2500;
    for (long t = 0;; t++) {
        if (cost == 0) return 1;
        if ((t & 15) == 0 && now() > until) return 0;
        if (t - last > stall) return 0;
        double T = 0.3 + 0.02 * (double)cost;
        int l = rndint(d);
        if (NB > 1 && rnd01() < 0.3) {
            int i1 = rndint(NB), i2 = rndint(NB);
            if (i1 == i2) continue;
            int t1 = P[l][i1];
            P[l][i1] = P[l][i2];
            P[l][i2] = t1;
            rebuild_inv_layer(l);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                t1 = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = t1;
                rebuild_inv_layer(l);
            }
        } else {
            int i = rndint(NB);
            int s = rndint(ORD);
            if (s == S[l][i]) continue;
            int old = S[l][i], oldi = SI[l][i];
            S[l][i] = s;
            SI[l][i] = ginv(s);
            long c2 = full_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                S[l][i] = old;
                SI[l][i] = oldi;
            }
        }
    }
}

static void emit(void) {
    set_group(bM, bQ, bR);
    NB = bNB;
    NV = 2 * NB * ORD;
    memcpy(P, bP, sizeof(P));
    memcpy(S, bS, sizeof(S));
    for (int l = 0; l < d; l++) rebuild_inv_layer(l);
    long m = (long)NB * ORD * d;
    printf("%d %ld\n", NV, m);
    for (int i = 0; i < NB; i++)
        for (int g = 0; g < ORD; g++)
            for (int l = 0; l < d; l++)
                printf("%d %d\n", i * ORD + g,
                       (NB + P[l][i]) * ORD + gmul(g, S[l][i]));
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long startN = argc > 5 ? atol(argv[5]) : 0;
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        if (s > 1000000L) break;
        p *= (d - 1);
    }
    moore = 2 * s;

    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long base = startN;
    if (base < 2 * d + 2) base = 2 * d + 2;
    long bestN = 0;
    int fails = 0;
    static const int NBS[6] = {1, 1, 2, 2, 3, 4};
    static const int QS[11] = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};

    while (now() < t_end) {
        long tgt;
        if (bestN > 0) {
            tgt = (rnd01() < 0.5) ? bestN + 2 : (long)(bestN * 1.03) + 2;
        } else {
            tgt = base;
            if (fails > 0 && fails % 20 == 0) {
                base = base * 9 / 10;
                if (base < 2 * d + 2) base = 2 * d + 2;
            }
        }
        int nb = NBS[rndint(6)];
        int q = QS[rndint(11)];
        long ordT = (tgt + 2 * nb - 1) / (2 * nb);
        long m = (ordT + q - 1) / q + rndint(3);
        if (m < 2) m = 2;
        long ord = m * q;
        long N = 2 * nb * ord;
        if (N > moore || N > MAXN || ord > MAXORD || (long)nb * ord < d) {
            fails++;
            continue;
        }
        int r = pick_r((int)m, q);
        if (r < 0) r = 1;
        set_group((int)m, q, r);
        NB = nb;
        NV = (int)N;
        double until = now() + 8.0;
        if (until > t_end) until = t_end;
        if (try_group(until)) {
            bestN = N;
            bNB = nb;
            bM = (int)m;
            bQ = q;
            bR = r;
            memcpy(bP, P, sizeof(P));
            memcpy(bS, S, sizeof(S));
            fails = 0;
        } else {
            fails++;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    emit();
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

    # Safe fallback: K_{d,d} has diameter 2; for d = 2 the even cycle C_{2D} is optimal.
    if d == 2:
        n = 2 * D
        best = (n, [(i, (i + 1) % n) for i in range(n)])
    else:
        best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2 or D == 2:
        return best

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

    # Main search: bi-Cayley lifts over semidirect groups, searched in C.
    budget = final - time.monotonic() - 1.0
    if budget > 3.0:
        try:
            start_n = max(2 * d + 2, best_n + 2)
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), start_n],
                             timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
