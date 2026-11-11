"""Voltage-lift search for the d=5, D=7 target, with a fallback start.

Changes from the parent:
  * The bi-Cayley, multi-fibre and greedy-growth engine is replaced. The new C engine lifts a bipartite
    base graph (the start, the split Cayley hexagon H(4) incidence graph with 2730 vertices, degree 5,
    diameter 6) by a cyclic group Z_m, with one voltage per base edge. Lifts preserve degree and
    bipartiteness. Z_m acts by translation, so one BFS per base vertex checks the whole lift exactly.
  * Voltages are annealed on an objective counting (sampled base source, lift vertex) pairs at distance
    more than D. Sources are added whenever a full check fails. Z_2 is tried first (5460 vertices for the
    target), then Z_3 (8190 vertices) with the remaining time. Any success is larger than the start.
  * Python keeps the algebraic start as a fallback, checks everything with lib.is_valid, and returns
    the start if the C run fails, times out, or produces an invalid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Cyclic voltage-lift search for bipartite degree-diameter graphs.
 * Usage:  prog d D seed time_limit < base_graph
 * stdin:  "n m" then m lines "u v" (bipartite base graph).
 * stdout: "n m" then m lines "u v" for the best lift found, or "0 0".
 * Lift by Z_M: base vertex u becomes u*M+g; base edge (tail u, head v, voltage a) joins
 * (u,g) to (v,(g+a) mod M) for all g.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 4096
#define MAXE 16384
#define MAXDEG 32
#define MAXV 16384
#define MAXSAMP 256

static int d, D;
static int nb, ne;
static int eu[MAXE], ev[MAXE];
static int side[MAXB];
static int deg[MAXB];
static int nbr[MAXB][MAXDEG];
static int nedge[MAXB][MAXDEG];
static unsigned char tailf[MAXB][MAXDEG];
static int va[MAXE];
static int best_va[MAXE];
static int keep_va[MAXE];
static int keepM = 0;
static int M;
static int stampv[MAXV], distv[MAXV], qv[MAXV];
static int cur_stamp = 0;
static int failsrc = -1;
static int samp[MAXSAMP];
static int K;
static uint64_t rs = 88172645463325252ULL;
static double tend;

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

static double moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2.0 * D;
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return 2.0 * s;
}

static int read_base(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXB || m <= 0 || m > MAXE) return 0;
    nb = n;
    ne = m;
    static int rdeg[MAXB];
    for (int v = 0; v < n; v++) rdeg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (rdeg[u] >= MAXDEG || rdeg[v] >= MAXDEG) return 0;
        rdeg[u]++;
        rdeg[v]++;
        eu[e] = u;
        ev[e] = v;
    }
    /* 2-colouring by relaxation over the edge list. */
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int e = 0; e < m; e++) {
                int u = eu[e], v = ev[e];
                if (side[u] >= 0 && side[v] < 0) { side[v] = 1 - side[u]; changed = 1; }
                else if (side[v] >= 0 && side[u] < 0) { side[u] = 1 - side[v]; changed = 1; }
            }
        }
    }
    for (int e = 0; e < m; e++) {
        if (side[eu[e]] == side[ev[e]]) return 0;
        if (side[eu[e]] == 1) {
            int t = eu[e];
            eu[e] = ev[e];
            ev[e] = t;
        }
    }
    return 1;
}

/* Adjacency of the base graph: tailf=1 means the owner is the tail (side 0) of edge e. */
static void build_adj(void) {
    for (int v = 0; v < nb; v++) deg[v] = 0;
    for (int e = 0; e < ne; e++) {
        int u = eu[e], w = ev[e];
        nbr[u][deg[u]] = w; nedge[u][deg[u]] = e; tailf[u][deg[u]] = 1; deg[u]++;
        nbr[w][deg[w]] = u; nedge[w][deg[w]] = e; tailf[w][deg[w]] = 0; deg[w]++;
    }
}

/* Number of lift vertices NOT within distance D of lift vertex (b,0). */
static int bfs_bad(int b) {
    int NV = nb * M;
    int head = 0, tail = 0;
    cur_stamp++;
    int src = b * M;
    stampv[src] = cur_stamp;
    distv[src] = 0;
    qv[tail++] = src;
    while (head < tail) {
        int x = qv[head++];
        int dx = distv[x];
        if (dx >= D) continue;
        int u = x / M;
        int g = x - u * M;
        for (int i = 0; i < deg[u]; i++) {
            int e = nedge[u][i];
            int c = tailf[u][i] ? va[e] : (M - va[e]) % M;
            int y = nbr[u][i] * M + (g + c) % M;
            if (stampv[y] != cur_stamp) {
                stampv[y] = cur_stamp;
                distv[y] = dx + 1;
                qv[tail++] = y;
            }
        }
    }
    return NV - tail;
}

static long objective(void) {
    long t = 0;
    for (int k = 0; k < K; k++) t += bfs_bad(samp[k]);
    return t;
}

/* Exact check. By translation symmetry, sources (b,0) for all base b suffice. */
static int full_check(void) {
    for (int b = 0; b < nb; b++) {
        if (bfs_bad(b) > 0) {
            failsrc = b;
            return 0;
        }
    }
    return 1;
}

/* Anneal the voltages of a Z_m lift. Returns 1 with best_va set when the lift is valid. */
static int search_M(int m, double until) {
    M = m;
    long NV = (long)nb * m;
    if (NV > MAXV || (double)NV > moore_bound()) return 0;
    K = nb < 24 ? nb : 24;
    for (int k = 0; k < K; k++) samp[k] = rndint(nb);
    for (int e = 0; e < ne; e++) va[e] = rndint(m);
    build_adj();
    long cur = objective();
    const double T0 = 6.0, T1 = 0.3;
    const long CYC = 4000;
    long step = 0;
    while (now() < until) {
        if (cur == 0) {
            if (full_check()) {
                memcpy(best_va, va, sizeof(int) * ne);
                return 1;
            }
            if (K < MAXSAMP) samp[K++] = failsrc;
            else samp[rndint(K)] = failsrc;
            cur = objective();
            continue;
        }
        int e = rndint(ne);
        int old = va[e];
        int nv = rndint(m - 1);
        if (nv >= old) nv++;
        va[e] = nv;
        long nw = objective();
        double T = T0 * pow(T1 / T0, (double)(step % CYC) / (double)CYC);
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) cur = nw;
        else va[e] = old;
        step++;
    }
    return 0;
}

static void print_lift(int m) {
    printf("%d %ld\n", nb * m, (long)ne * m);
    for (int e = 0; e < ne; e++)
        for (int g = 0; g < m; g++)
            printf("%d %d\n", eu[e] * m + g, ev[e] * m + (g + keep_va[e]) % m);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < base_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    tend = t0 + limit - 1.0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 1 || !read_base()) {
        printf("0 0\n");
        return 0;
    }
    double mid = t0 + 0.5 * (tend - t0);
    int got = 0;
    if (search_M(2, mid)) {
        memcpy(keep_va, best_va, sizeof(int) * ne);
        keepM = 2;
        got = 1;
    }
    if (search_M(3, tend)) {
        memcpy(keep_va, best_va, sizeof(int) * ne);
        keepM = 3;
        got = 1;
    }
    if (got) print_lift(keepM);
    else printf("0 0\n");
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    elapsed = time.monotonic() - t0
    budget = 0.85 * time_limit - elapsed - 1.0
    if budget <= 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
