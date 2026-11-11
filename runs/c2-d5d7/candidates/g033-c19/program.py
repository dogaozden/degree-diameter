"""d=5, D=7 target: multi-fibre semidirect-product lifts with an orbit-reduced diameter objective.

The parent searched single-fibre bi-Cayley lifts (2N vertices) with voltage annealing. This version
replaces that family. A lift has P fibres per side (P in {1,2,3}) over a group G = Z_m x|_r Z_k of
order N, with a random d-regular bipartite base multigraph on P+P vertices. The lift has 2PN vertices.
Its voltage state is annealed against the number of bad (source, vertex) pairs. Left multiplication
is an automorphism that is transitive on each fibre, so BFS from the identity of each of the 2P fibres
gives an exact objective. Any candidate is checked in full in C before it is accepted, and every
returned graph is checked again with lib.is_valid. The starting graph from the algebraic constructions
is the fallback, so the program always returns a valid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 8192
#define MAXD 8
#define MAXN 2048
#define MAXT 24
#define MAXP 3
#define STEPS 2500

static int d, D, P, N, M, K, RR, nd, V, best_n, best_V;
static int RP[MAXN];
static int MT[MAXN * MAXN];
static int dI[MAXT], dJ[MAXT], dG[MAXT], sA[MAXT], sB[MAXT];
static int nb[MAXV * MAXD];
static int best_nb[MAXV * MAXD];
static int dist[MAXV], que[MAXV];
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

static void setup_group(void) {
    for (int b = 0; b < K; b++)
        RP[b] = b == 0 ? 1 % M : (int)((long)RP[b - 1] * RR % M);
    for (int x = 0; x < N; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < N; y++) {
            int c = y / K, e = y % K;
            MT[x * N + y] = (int)(((a + (long)RP[b] * c) % M) * K + (b + e) % K);
        }
    }
}

/* Random admissible semidirect product Z_m x|_r Z_k with m*k = N; falls back to Z_N. */
static void choose_group(void) {
    int divs[MAXN], nds = 0;
    for (int m = 1; m <= N; m++) if (N % m == 0) divs[nds++] = m;
    for (int tries = 0; tries < 300; tries++) {
        int m = divs[rndint(nds)], k = N / m;
        int r = m > 1 ? 1 + rndint(m - 1) : 0;
        if (m > 1 && gcd(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        M = m; K = k; RR = r;
        setup_group();
        return;
    }
    M = N; K = 1; RR = 1;
    setup_group();
}

/* Random d-regular bipartite base multigraph on P+P vertices, connected; fills darts. */
static void make_base(void) {
    int cnt[MAXP][MAXP];
    for (;;) {
        memset(cnt, 0, sizeof cnt);
        for (int t = 0; t < d; t++) {
            int perm[MAXP] = {0, 1, 2};
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < P; i++) cnt[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1; st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * P; u++) {
                if (seen[u]) continue;
                int linked = v < P ? (u >= P && cnt[v][u - P] > 0) : (u < P && cnt[u][v - P] > 0);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * P) break;
    }
    nd = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < cnt[i][j]; c++) { dI[nd] = i; dJ[nd] = j; dG[nd] = 0; nd++; }
}

/* 1 if voltage g clashes with a dart u < upto (u != t) on the same (i, j) pair. */
static int clashes(int t, int g, int upto) {
    for (int u = 0; u < upto; u++)
        if (u != t && dI[u] == dI[t] && dJ[u] == dJ[t] && dG[u] == g) return 1;
    return 0;
}

static void init_volt(void) {
    for (int t = 0; t < nd; t++) {
        int g;
        do { g = rndint(N); } while (clashes(t, g, t));
        dG[t] = g;
    }
    for (int t = 0; t < nd; t++) {
        sA[t] = 0; sB[t] = 0;
        for (int u = 0; u < t; u++) {
            if (dI[u] == dI[t]) sA[t]++;
            if (dJ[u] == dJ[t]) sB[t]++;
        }
    }
}

/* Vertex ids: A fibre f, element x -> f*N + x; B fibre j -> (P+j)*N + x. */
static void build_nb(void) {
    V = 2 * P * N;
    for (int t = 0; t < nd; t++) {
        int g = dG[t];
        for (int x = 0; x < N; x++) {
            int y = MT[x * N + g];
            int A = dI[t] * N + x;
            int B = (P + dJ[t]) * N + y;
            nb[A * d + sA[t]] = B;
            nb[B * d + sB[t]] = A;
        }
    }
}

static long orbit_bad(void) {
    long total = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = s * N;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int h = 0, tl = 0;
        dist[src] = 0; que[tl++] = src;
        while (h < tl) {
            int v = que[h++];
            if (dist[v] >= D) continue;
            for (int k = 0; k < d; k++) {
                int u = nb[v * d + k];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; que[tl++] = u; }
            }
        }
        total += V - tl;
    }
    return total;
}

static int full_ok(void) {
    for (int s = 0; s < V; s++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int h = 0, tl = 0;
        dist[s] = 0; que[tl++] = s;
        while (h < tl) {
            int v = que[h++];
            if (dist[v] >= D) continue;
            for (int k = 0; k < d; k++) {
                int u = nb[v * d + k];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; que[tl++] = u; }
            }
        }
        if (tl < V) return 0;
    }
    return 1;
}

/* Returns 0 if a zero-objective voltage set was found, 1 if not, -1 on timeout. */
static int anneal(void) {
    build_nb();
    long bad = orbit_bad();
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) return -1;
        int t = rndint(nd), old = dG[t], g;
        do { g = rndint(N); } while (clashes(t, g, nd));
        dG[t] = g;
        build_nb();
        long nbad = orbit_bad();
        double T = pow(0.02, (double)s / STEPS);
        if (nbad <= bad || rnd01() < exp((double)(bad - nbad) / T)) bad = nbad;
        else dG[t] = old;
    }
    return bad == 0 ? 0 : 1;
}

int main(int argc, char **argv) {
    if (argc < 6) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    best_n = atoi(argv[5]);
    best_V = 0;
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 1) return 0;

    while (now() < t_end) {
        int r = rndint(10);
        P = r < 3 ? 1 : (r < 7 ? 2 : 3);
        int target = best_n + 2;
        int Nmin = (target + 2 * P - 1) / (2 * P);
        N = Nmin + rndint(4);
        if (N < d + 1) N = d + 1;
        if (N > MAXN || 2 * P * N > MAXV) continue;
        choose_group();
        make_base();
        init_volt();
        int res = anneal();
        if (res < 0) break;
        if (res == 0) {
            build_nb();
            if (V > best_n && full_ok()) {
                best_n = V;
                best_V = V;
                memcpy(best_nb, nb, sizeof(int) * V * d);
            }
        }
    }
    if (best_V) {
        long m = (long)(best_V / 2) * d;
        printf("%d %ld\n", best_V, m);
        for (int v = 0; v < best_V / 2; v++)
            for (int k = 0; k < d; k++)
                printf("%d %d\n", v, best_nb[v * d + k]);
    }
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

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so valid for D = 6 and D = 7.
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
            try:
                out.append(_gq_w(q))
            except Exception:
                pass
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 7 or best[0] >= lib.moore_bound(d, D):
        return best
    if not (d == 5 and D == 7):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 3.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0]],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
