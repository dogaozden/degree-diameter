"""Haar and voltage-lift search for the weakest target (d=4, D=7).

This version replaces the parent's PSL/PGL and semidirect-group lift search with a different construction.
Each candidate is a regular Z_G voltage lift over a base multigraph with P <= 4 fibres per side. The base
is the sum of d random permutation matrices, so every fibre vertex has degree d. Voltages are searched
by hill climbing on the number of vertex pairs at distance > D. The diameter check is exact: Z_G acts
regularly on each fibre, so BFS from the 2P fibre representatives covers all pairs.

Fallbacks: K_{d,d}, the projective-plane, Araujo-Pardo-Lopez and W(q) starts. Each is checked with
lib.is_valid. The C result is accepted only if it is larger and passes lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXDART 256
#define MAXP 4
#define MAXM 1024
#define EVALS 30000

static int d, D;
static double deadline;
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

static int P, G;                       /* P fibres per side, Z_G fibres */
static int nd;                         /* number of darts, nd = d*P */
static int di[MAXDART], dj[MAXDART], dg[MAXDART];
static int N;
static int adj[MAXN][MAXD], deg[MAXN];
static int dstamp[MAXN], dval[MAXN], qbuf[MAXN], stampv = 0;

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        pw *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* Lift: fibre f = i (A side, i < P) or P + j (B side); vertex f*G + x. */
static void build(void) {
    N = 2 * P * G;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < G; x++) {
            int u = di[t] * G + x;
            int v = (P + dj[t]) * G + (x + dg[t]) % G;
            adj[u][deg[u]++] = v;
            adj[v][deg[v]++] = u;
        }
}

/* Number of (representative, vertex) pairs at distance > D. Zero iff diameter <= D. */
static long bad_count(void) {
    long bad = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = s * G;
        stampv++;
        int head = 0, tail = 0;
        dstamp[src] = stampv;
        dval[src] = 0;
        qbuf[tail++] = src;
        while (head < tail) {
            int v = qbuf[head++];
            if (dval[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dstamp[u] != stampv) {
                    dstamp[u] = stampv;
                    dval[u] = dval[v] + 1;
                    qbuf[tail++] = u;
                }
            }
        }
        bad += N - tail;
    }
    return bad;
}

/* Would dart t with voltage g clash with a dart s < lim on the same fibre pair? */
static int clash(int t, int g, int lim) {
    for (int s = 0; s < lim; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

static void random_voltages(void) {
    for (int t = 0; t < nd; t++) {
        int g;
        do { g = rndint(G); } while (clash(t, g, t));
        dg[t] = g;
    }
}

/* Base multigraph: sum of d random permutation matrices on P + P vertices. Row and column sums are d. */
static void make_darts(void) {
    nd = 0;
    for (int k = 0; k < d; k++) {
        int pm[MAXP];
        for (int i = 0; i < P; i++) pm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = pm[i];
            pm[i] = pm[j];
            pm[j] = s;
        }
        for (int i = 0; i < P; i++) {
            di[nd] = i;
            dj[nd] = pm[i];
            nd++;
        }
    }
}

static int have = 0;
static int bP, bG, bnd;
static int bdi[MAXDART], bdj[MAXDART], bdg[MAXDART];

static void record(void) {
    have = 1;
    bP = P;
    bG = G;
    bnd = nd;
    memcpy(bdi, di, sizeof(int) * nd);
    memcpy(bdj, dj, sizeof(int) * nd);
    memcpy(bdg, dg, sizeof(int) * nd);
}

/* Hill climb on voltages. Returns 1 if a voltage assignment with diameter <= D was found. */
static int search(long maxevals) {
    random_voltages();
    build();
    long cur = bad_count();
    for (long e = 0; e < maxevals && cur > 0; e++) {
        if ((e & 255) == 0 && now() > deadline) break;
        int t = rndint(nd);
        int old = dg[t];
        int g;
        do { g = rndint(G); } while (clash(t, g, nd));
        dg[t] = g;
        build();
        long nb = bad_count();
        if (nb <= cur || rnd01() < 0.01) cur = nb;
        else dg[t] = old;
    }
    return cur == 0;
}

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
    double t0 = now();
    deadline = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 1 || d > MAXD - 1 || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long bestn = target;
    while (now() < deadline && bestn + 2 <= moore) {
        int p = 1 + rndint(MAXP);
        long mlo = bestn / (2L * p) + 1;
        if (mlo < d) mlo = d;
        long m = mlo + rndint((int)(3 + mlo / 40));
        long n = 2L * p * m;
        if (n > MAXN || m > MAXM || n > moore) continue;
        P = p;
        G = (int)m;
        make_darts();
        if (search(EVALS)) {
            bestn = n;
            record();
        }
    }

    if (have) {
        P = bP;
        G = bG;
        nd = bnd;
        memcpy(di, bdi, sizeof(int) * nd);
        memcpy(dj, bdj, sizeof(int) * nd);
        memcpy(dg, bdg, sizeof(int) * nd);
        build();
        long m = 0;
        for (int u = 0; u < N; u++)
            for (int i = 0; i < deg[u]; i++)
                if (u < adj[u][i]) m++;
        printf("%d %ld\n", N, m);
        for (int u = 0; u < N; u++)
            for (int i = 0; i < deg[u]; i++)
                if (u < adj[u][i]) printf("%d %d\n", u, adj[u][i]);
    } else {
        printf("0 0\n");
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 6)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
