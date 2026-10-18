"""Cyclic Haar-lift search: vertex-transitive bipartite graphs H(Z_m, S) with |S| = d.

Vertices a_i and b_j (i, j in Z_m); a_i ~ b_{i+s} for s in S. Translations and the side swap
a_i <-> b_{-i} are automorphisms, so the graph is vertex-transitive and the diameter check only
needs one BFS from a_0. The C engine runs simulated annealing over the connection set S for a
sequence of group orders m, using an implicit BFS (no stored graph). It keeps the largest m that
succeeds and prints the lift. Exact constructions (projective planes, Araujo-Lopez, generalized
quadrangle) are tried first, and K_{d,d} is the fallback. Every returned graph is checked with
lib.is_valid.
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

#define MAXM 12000
#define MAXDEG 32

static int d, D, m;
static int S[MAXDEG];
static unsigned char inS[MAXM];
static int dist[2 * MAXM];
static int qu[2 * MAXM];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Largest m allowed by the Moore bound (n = 2m <= 2 * sum_{i<D} (d-1)^i), capped at MAXM. */
static int moore_half(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 1;
    if (d == 2) return D < MAXM ? D : MAXM;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return s > MAXM ? MAXM : (int)s;
}

/* Number of vertices not within distance D of a_0 (vertex-transitive, so this decides the diameter). */
static int unreached(void) {
    int N = 2 * m;
    for (int i = 0; i < N; i++) dist[i] = -1;
    int h = 0, t = 0;
    dist[0] = 0;
    qu[t++] = 0;
    while (h < t) {
        int v = qu[h++];
        int dv = dist[v];
        if (dv >= D) continue;
        if (v < m) {
            for (int i = 0; i < d; i++) {
                int u = m + (v + S[i]) % m;
                if (dist[u] < 0) {
                    dist[u] = dv + 1;
                    qu[t++] = u;
                }
            }
        } else {
            int j = v - m;
            for (int i = 0; i < d; i++) {
                int u = (j - S[i] + m) % m;
                if (dist[u] < 0) {
                    dist[u] = dv + 1;
                    qu[t++] = u;
                }
            }
        }
    }
    return N - t;
}

static void random_set(void) {
    for (int i = 0; i < m; i++) inS[i] = 0;
    for (int i = 0; i < d; i++) {
        int s;
        do {
            s = rndint(m);
        } while (inS[s]);
        inS[s] = 1;
        S[i] = s;
    }
}

/* Simulated annealing over S for group order mm. Returns 1 with S valid, 0 on timeout. */
static int search(int mm, double deadline) {
    m = mm;
    random_set();
    int c = unreached();
    long it = 0;
    while (1) {
        if (c == 0) return 1;
        if ((it & 127) == 0 && now() > deadline) return 0;
        it++;
        double ph = (double)(it % 300000) / 300000.0;
        double T = 2.5 * pow(0.06, ph);
        int idx = rndint(d);
        int old = S[idx];
        int nw = rndint(m);
        if (inS[nw]) continue;
        S[idx] = nw;
        inS[old] = 0;
        inS[nw] = 1;
        int c2 = unreached();
        if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
            c = c2;
        } else {
            S[idx] = old;
            inS[nw] = 0;
            inS[old] = 1;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_m\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int start = atoi(argv[5]);
    double t0 = now();
    double t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 3 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }
    int cap = moore_half();
    if (cap < d + 1) {
        printf("0 0\n");
        return 0;
    }

    int lo = 0, hi = 0, best_m = 0;
    int bestS[MAXDEG];
    long step = 8;
    int mt = start;
    if (mt < d + 1) mt = d + 1;
    if (mt > cap) mt = cap;

    while (now() < t_end - 0.05) {
        double rem = t_end - now();
        double slice = rem * 0.3;
        if (slice < 3.0) slice = 3.0;
        if (slice > rem) slice = rem;
        int ok = search(mt, now() + slice);
        if (ok) {
            lo = mt;
            best_m = mt;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            if (lo >= cap) break;
            if (hi <= lo) {
                hi = 0;
                mt = lo + (int)step;
                if (step < 4096) step *= 2;
            } else {
                mt = (hi - lo > 1) ? (lo + hi) / 2 : hi;
            }
        } else {
            hi = mt;
            if (lo == 0) {
                mt = mt - 150;
            } else {
                mt = (hi - lo > 1) ? (lo + hi) / 2 : hi;
            }
        }
        if (mt > cap) mt = cap;
        if (mt < d + 1) mt = d + 1;
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    int mm = best_m;
    printf("%d %d\n", 2 * mm, mm * d);
    for (int i = 0; i < mm; i++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", i, mm + (i + bestS[j]) % mm);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept as alternative candidates).
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search: cyclic Haar lifts with simulated annealing over the connection set,
    # with a bisection-style search over the group order m.
    budget = max(1.0, 0.8 * time_limit - 4.0)
    moore = lib.moore_bound(d, D)
    start_m = max(d + 1, int(0.26 * moore / 2))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), start_m],
                         timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
