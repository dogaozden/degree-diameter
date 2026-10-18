"""Bold change: bi-Cayley / voltage-lift search over abelian groups Z_a x Z_b, with C annealing.

Each graph has base vertices A_0..A_{k-1}, B_0..B_{k-1} and group G. Layer l joins A_i to
B_{P[l][i]} with voltage S[l][i]. Each layer is a permutation, so every vertex has degree d.
Group translations and the side swap sigma (A_g <-> B_{-g}) mean that for k = 1 one BFS
from A_0 decides validity. For k >= 2 the BFS runs from all 2k base vertices.
C runs simulated annealing on the voltages and permutations, with a bandit over k and a
ratcheting target order. Small exact constructions (PG(2,q), Araujo-Pardo-Lopez, W(q)) and
K_{d,d} are kept as fallbacks, and every output is checked with lib.is_valid.
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

#define MAXK 8
#define MAXD 32
#define MAXG 8192
#define MAXN (2 * MAXK * MAXG)

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, G, GA, GB, N;
static int gxv[MAXG], gyv[MAXG];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bestP[MAXD][MAXK], bestS[MAXD][MAXK];
static int bestK, bestG, bestGA, bestGB;
static long best_n;
static int nb[MAXN * MAXD];
static int queue_[MAXN];
static unsigned vis[MAXN];
static unsigned vstamp = 0;
static int tgt = -1;

static int addg(int x, int y) {
    int u = gxv[x] + gxv[y];
    if (u >= GA) u -= GA;
    int v = gyv[x] + gyv[y];
    if (v >= GB) v -= GB;
    return u * GB + v;
}
static int subg(int x, int y) {
    int u = gxv[x] - gxv[y];
    if (u < 0) u += GA;
    int v = gyv[x] - gyv[y];
    if (v < 0) v += GB;
    return u * GB + v;
}

static void set_group(int a, int b) {
    GA = a;
    GB = b;
    for (int x = 0; x < G; x++) {
        gxv[x] = x / GB;
        gyv[x] = x % GB;
    }
}

/* Rewrite the neighbour entries of layer l for base A_i (and the B vertices it touches). */
static void write_dart(int l, int i) {
    int p = P[l][i], s = S[l][i];
    int abase = i * G, bbase = (K + p) * G;
    for (int g = 0; g < G; g++) {
        int h = addg(g, s);
        nb[(abase + g) * d + l] = bbase + h;
        nb[(bbase + h) * d + l] = abase + g;
    }
}

static int ok_base(int i) {
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) return 0;
    return 1;
}

static int all_ok(void) {
    for (int i = 0; i < K; i++)
        if (!ok_base(i)) return 0;
    return 1;
}

static int dup_free_layer(int l, int i) {
    for (int l2 = 0; l2 < l; l2++)
        if (P[l2][i] == P[l][i] && S[l2][i] == S[l][i]) return 0;
    return 1;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int pm[MAXK];
        for (int i = 0; i < K; i++) pm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pm[i];
            pm[i] = pm[j];
            pm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            P[l][i] = pm[i];
            S[l][i] = rndint(G);
        }
    }
    for (int i = 0; i < K; i++)
        for (int l = 1; l < d; l++) {
            int tries = 0;
            while (!dup_free_layer(l, i) && tries < 2000) {
                S[l][i] = rndint(G);
                tries++;
            }
        }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) write_dart(l, i);
}

static void setup(int k, int g, int a, int b) {
    K = k;
    G = g;
    N = 2 * K * G;
    set_group(a, b);
    random_state();
}

/* Sum over base representatives of the number of vertices not within distance D.
   Zero iff the graph has diameter <= D. */
static long evaluate(void) {
    long cost = 0;
    tgt = -1;
    int nsrc = (K == 1) ? 1 : 2 * K;
    for (int si = 0; si < nsrc; si++) {
        int src = si * G;
        vstamp++;
        if (vstamp == 0) {
            memset(vis, 0, sizeof vis);
            vstamp = 1;
        }
        int head = 0, tail = 0;
        queue_[tail++] = src;
        vis[src] = vstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                const int *row = nb + (size_t)queue_[head++] * d;
                for (int l = 0; l < d; l++) {
                    int u = row[l];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        queue_[tail++] = u;
                    }
                }
            }
        }
        long un = N - tail;
        cost += un;
        if (un > 0 && tgt < 0) {
            int off = rndint(N);
            for (int t = 0; t < N; t++) {
                int v = off + t;
                if (v >= N) v -= N;
                if (vis[v] != vstamp) {
                    tgt = v;
                    break;
                }
            }
        }
    }
    return cost;
}

static int accept_move(long delta, double T) {
    if (delta <= 0) return 1;
    if (T <= 0) return 0;
    return rnd01() < exp(-(double)delta / T);
}

static long anneal_run(double t_start, double deadline) {
    long cost = evaluate();
    double span = deadline - t_start;
    if (span < 1e-3) span = 1e-3;
    double frac = 0.0;
    for (long it = 0; cost > 0; it++) {
        if ((it & 31) == 0) {
            double t = now();
            if (t >= deadline) break;
            frac = (t - t_start) / span;
        }
        double T = 0.2 + (0.05 * (double)cost + 2.0) * (1.0 - frac);
        int tsave = tgt;
        if (K >= 2 && rndint(100) < 25) {
            /* swap two base targets within one layer */
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int t = P[l][i1];
            P[l][i1] = P[l][i2];
            P[l][i2] = t;
            write_dart(l, i1);
            write_dart(l, i2);
            long nc = -1;
            if (ok_base(i1) && ok_base(i2)) nc = evaluate();
            if (nc >= 0 && accept_move(nc - cost, T)) {
                cost = nc;
            } else {
                t = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = t;
                write_dart(l, i1);
                write_dart(l, i2);
                tgt = tsave;
            }
        } else {
            int l, i;
            if (tgt >= 0 && rndint(100) < 60) {
                int c = tgt / G;
                l = rndint(d);
                if (c < K) {
                    i = c;
                } else {
                    int p = c - K;
                    i = 0;
                    for (int j = 0; j < K; j++)
                        if (P[l][j] == p) {
                            i = j;
                            break;
                        }
                }
            } else {
                l = rndint(d);
                i = rndint(K);
            }
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            write_dart(l, i);
            long nc = -1;
            if (ok_base(i)) nc = evaluate();
            if (nc >= 0 && accept_move(nc - cost, T)) {
                cost = nc;
            } else {
                S[l][i] = old;
                write_dart(l, i);
                tgt = tsave;
            }
        }
    }
    return cost;
}

static void store_best(int k, int g, int a, int b, long n) {
    bestK = k;
    bestG = g;
    bestGA = a;
    bestGB = b;
    best_n = n;
    memcpy(bestP, P, sizeof P);
    memcpy(bestS, S, sizeof S);
}

static void emit_best(void) {
    K = bestK;
    G = bestG;
    N = 2 * K * G;
    set_group(bestGA, bestGB);
    memcpy(P, bestP, sizeof P);
    memcpy(S, bestS, sizeof S);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) write_dart(l, i);
    if (!all_ok() || evaluate() != 0) {
        printf("0 0\n");
        return;
    }
    printf("%d %ld\n", N, (long)K * G * d);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v * d + l]);
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
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double tend = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    /* Fallback: K_{d,d} as K=1, G=d, voltages 0..d-1. */
    bestK = 1;
    bestG = d;
    bestGA = 1;
    bestGB = d;
    best_n = 2L * d;
    memset(bestP, 0, sizeof bestP);
    memset(bestS, 0, sizeof bestS);
    for (int l = 0; l < d; l++) bestS[l][0] = l;

    int trials[MAXK + 1], wins[MAXK + 1];
    memset(trials, 0, sizeof trials);
    memset(wins, 0, sizeof wins);
    double goal = 1.3 * (double)best_n;

    while (1) {
        double remaining = tend - now();
        if (remaining < 1.0) break;

        int k;
        if (rndint(100) < 25) {
            k = 1 + rndint(5);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= 5; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.05 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    k = c;
                }
            }
        }

        long Gt = (long)(goal / (2.0 * k)) + rndint(3);
        if (Gt < d) Gt = d;
        if (2L * k * Gt <= best_n) Gt = best_n / (2L * k) + 1;
        if (Gt > MAXG) Gt = MAXG;

        int a = 1;
        if (rnd01() < 0.4) {
            int cand[64];
            int nc = 0;
            for (long x = 1; x <= Gt && nc < 64; x++)
                if (Gt % x == 0) cand[nc++] = (int)x;
            a = cand[rndint(nc)];
        }
        int b = (int)(Gt / a);

        setup(k, (int)Gt, a, b);
        if (!all_ok()) continue;
        trials[k]++;

        double slice = remaining / 5.0;
        if (slice < 2.0) slice = 2.0;
        if (slice > 12.0) slice = 12.0;
        if (slice > remaining) slice = remaining;
        double ts = now();
        long c = anneal_run(ts, ts + slice);
        if (c == 0) {
            wins[k]++;
            long n = 2L * k * Gt;
            double el = now() - ts;
            store_best(k, (int)Gt, a, b, n);
            goal = (double)n * (el < 0.5 ? 1.3 : 1.03);
        } else {
            double floor_goal = 1.01 * (double)best_n;
            goal = goal * 0.98;
            if (goal < floor_goal) goal = floor_goal;
        }
    }

    emit_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (used as fallbacks and for the D = 3, 4 cases).
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

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best, best_n = (n, e), n
        except Exception:
            pass

    if D == 2:
        return best

    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    except Exception:
        pass

    if D == 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if lib.is_prime_power(d - 1):
            return best

    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main phase: abelian bi-Cayley voltage-lift annealing in C, using the remaining time.
    total = max(1.0, 0.8 * time_limit - 2.5)
    remaining = total - (time.monotonic() - t0)
    if remaining > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=None, timeout=remaining + 3.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
