"""Bi-Cayley lift search in C (direct annealing over voltages and layer permutations),
with exact constructions for D = 3 and D = 4 and a K_{d,d} / cycle fallback.

Each lift is a 2K-block graph over the semidirect group Z_M x| Z_K2 (order G = M*K2):
A_{i,g} ~ B_{j,g*s} for every layer l, where j = layers[l][i] and s = S[l][i].
Left multiplication by the group is an automorphism, so the graph is valid iff a BFS
from each of the 2K block representatives reaches every vertex within D steps.
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

#define MAXK 4
#define MAXD 24
#define MAXN 40000

static int d, D;
static int K, G, M, K2, R, N;
static int powr[64];
static int sinv[MAXN];
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int adj[MAXN][MAXD];
static int best_adj[MAXN][MAXD];
static int vis[MAXN];
static int qbuf[MAXN];
static int stamp_ = 0;
static uint64_t rs = 88172645463325252ULL;

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
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_cap(void) {
    if (D <= 0 || d <= 0) return 1;
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

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect group Z_M x| Z_K2, element a*K2+b, (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int A = (int)(((long)a + (long)powr[b] * c) % M);
    int B = (b + e) % K2;
    return A * K2 + B;
}

static void setup_group(long m, int k2, long r) {
    M = (int)m;
    K2 = k2;
    R = (int)r;
    G = M * K2;
    powr[0] = 1 % M;
    for (int b = 1; b < K2; b++) powr[b] = (int)((long)powr[b - 1] * R % M);
    for (int s = 0; s < G; s++) {
        int a = s / K2, b = s % K2;
        int nb = (K2 - b) % K2;
        int na = (int)((M - ((long)powr[nb] * a) % M) % M);
        sinv[s] = na * K2 + nb;
    }
}

static long pick_r(long m, int k2) {
    if (k2 == 1 || m < 3) return 1;
    if (rnd01() < 0.25) return 1;
    if (k2 % 2 == 0 && rnd01() < 0.3 && powmodl(m - 1, k2, m) == 1 % m) return m - 1;
    for (int t = 0; t < 300; t++) {
        long r = 2 + rndi((int)(m - 2));
        if (gcdl(r, m) == 1 && powmodl(r, k2, m) == 1 % m) return r;
    }
    return 1;
}

/* Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h. */
static void set_dart(int l, int i) {
    int j = layers[l][i], s = S[l][i];
    int Ab = i * G, Bb = (K + j) * G;
    int si = sinv[s];
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        adj[Ab + g][l] = Bb + h;
        adj[Bb + h][l] = Ab + gmul(h, si);
    }
}

/* Sum over the 2K block representatives of the number of vertices at distance > D. */
static long unreached_cost(void) {
    long total = 0;
    int nreps = 2 * K;
    for (int q = 0; q < nreps; q++) {
        int r0 = q * G;
        stamp_++;
        int head = 0, tail = 0;
        qbuf[tail++] = r0;
        vis[r0] = stamp_;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qbuf[head++];
                for (int l = 0; l < d; l++) {
                    int u = adj[v][l];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

/* Repeated (block, voltage) pairs for one base vertex give parallel edges. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

static long eval_cost(void) { return unreached_cost() + 1000L * dup_count(); }

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            layers[l][i] = p[i];
            S[l][i] = rndi(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int attempt(long iters, long patience, double t_stop) {
    random_state();
    long cost = eval_cost();
    long bestc = cost, last = 0;
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && now() > t_stop) break;
        if (it - last > patience) break;
        double frac = (double)it / (double)iters;
        double temp = 0.5 + 0.05 * (double)cost * (1.0 - frac);
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndi(d);
            int i1 = rndi(K), i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int t = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = t;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                t = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int l = rndi(d), i = rndi(K);
            int old = S[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = it; }
    }
    return cost == 0;
}

static const int K2S[24] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
                            14, 15, 16, 18, 20, 22, 24, 25, 27, 30, 32, 36};

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit target_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long target = atol(argv[5]);
    double t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 3 || D < 3 || d > MAXD) { printf("0 0\n"); return 0; }

    long cap = moore_cap();
    if (cap > MAXN) cap = MAXN;
    long goal = target;
    if (goal > cap) goal = cap;
    if (goal < 4) goal = 4;

    long bestN = 0;
    int trials[MAXK + 1], wins[MAXK + 1];
    memset(trials, 0, sizeof(trials));
    memset(wins, 0, sizeof(wins));

    while (now() < t_end) {
        if (bestN >= cap) break;
        int Kc;
        if (rnd01() < 0.2) {
            Kc = 1 + rndi(MAXK);
        } else {
            double bs = -1.0;
            Kc = 1;
            for (int k = 1; k <= MAXK; k++) {
                double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; Kc = k; }
            }
        }
        int k2 = K2S[rndi(24)];
        long want = (goal + 2L * Kc - 1) / (2L * Kc);
        long m = (want + k2 - 1) / k2 + rndi(3);
        if (m < 2) m = 2;
        long r = pick_r(m, k2);
        setup_group(m, k2, r);
        K = Kc;
        while (2L * K * G > cap && m > 2) {
            m--;
            r = pick_r(m, k2);
            setup_group(m, k2, r);
        }
        N = 2 * K * G;
        if (N > cap) {
            goal = goal > 5 ? goal - 1 : 4;
            continue;
        }
        if (N <= bestN) {
            goal = bestN + bestN / 100 + 1;
            if (goal > cap) goal = cap;
            continue;
        }
        trials[Kc]++;
        if (attempt(4000, 1000, t_end)) {
            wins[Kc]++;
            bestN = N;
            memcpy(best_adj, adj, sizeof(int) * (size_t)MAXD * (size_t)N);
            goal = N + N / 100 + 1;
            if (goal > cap) goal = cap;
        } else {
            long g2 = goal - goal * 3 / 100;
            long floor_ = bestN + bestN / 200 + 1;
            goal = g2 > floor_ ? g2 : floor_;
            if (goal > cap) goal = cap;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    long m = 0;
    for (long v = 0; v < bestN; v++)
        for (int l = 0; l < d; l++)
            if (v < best_adj[v][l]) m++;
    printf("%ld %ld\n", bestN, m);
    for (long v = 0; v < bestN; v++)
        for (int l = 0; l < d; l++)
            if (v < best_adj[v][l]) printf("%ld %d\n", v, best_adj[v][l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (used for D = 3 and D = 4).
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


def _cycle_graph(D):
    """Cycle on 2D vertices: bipartite, 2-regular, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n

    if d == 2:
        consider(*_cycle_graph(D))
        return best

    total = max(1.0, 0.85 * time_limit - 2.5)
    final = t0 + total

    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(*pg)
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

    # Main search: C bi-Cayley lift annealing, aimed above the current best.
    if D >= 3 and d >= 3:
        cap = lib.moore_bound(d, D)
        target = max(int(best_n * 1.02) + 1, int(0.2 * cap))
        remaining = final - time.monotonic() - 3.0
        if remaining > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), target],
                                 stdin_graph=None, timeout=remaining + 10)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
