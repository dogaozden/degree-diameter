"""Bi-Cayley climb: vertex-transitive lifts over semidirect products, searched in C.

Each candidate is a lift of a p-vertex base (d darts per vertex) over a group G of order N = m*k,
with A_{i,x} ~ B_{j, x*s}. The group acts on each side by left multiplication, so the diameter
only has to be checked from the 2p representatives A_{i,1} and B_{j,1}. The C engine anneals the
voltages for a fixed group until the graph is valid or its time slice ends. Python climbs the
order by jumps whose size adapts to recent success and failure.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift annealing with reference-only diameter checks.
# Usage: prog d D seed time_limit p M K R
# Group: Z_M x| Z_K, element a*K+b, (a,b)(c,e) = (a + R^b c mod M, b+e mod K), N = M*K.
# Vertices: A_{i,x} = i*N + x, B_{j,y} = (p+j)*N + y. Darts t: i = t/d, target j = J[t],
# voltage S[t]; edge A_{i,x} ~ B_{j, x*S[t]}. Each A_i owns d darts, each B_j receives d darts.
# Cost = unreached pairs from the 2p reference vertices + 1000 * duplicate darts.
# stdout: "n m" and edges on success, otherwise "0 0".
# ----------------------------------------------------------------------------

C_BICAYLEY = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 8192
#define MAXD 16
#define MAXP 4
#define MAXDART (MAXP * MAXD)
#define RESTART 60000

static int d, D, p, M, K, R, N, V;
static double t_end;
static int rp[MAXV];
static int Jv[MAXDART], Sv[MAXDART];
static int adj[MAXV][MAXD];
static int cnt[MAXV];
static int dist[MAXV], qu[MAXV];

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

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    return (int)(((long)a + (long)rp[b] * c) % M) * K + (b + e) % K;
}

static void build(void) {
    int P = p * d;
    for (int j = 0; j < p; j++)
        for (int y = 0; y < N; y++) cnt[(p + j) * N + y] = 0;
    for (int t = 0; t < P; t++) {
        int i = t / d, j = Jv[t], s = Sv[t];
        for (int x = 0; x < N; x++) {
            int a = i * N + x;
            int b = (p + j) * N + gmul(x, s);
            adj[a][t - i * d] = b;
            if (cnt[b] < d) adj[b][cnt[b]++] = a;
        }
    }
}

static int reach_from(int src) {
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, tl = 0;
    dist[src] = 0;
    qu[tl++] = src;
    while (h < tl) {
        int v = qu[h++];
        if (dist[v] >= D) continue;
        for (int k = 0; k < d; k++) {
            int u = adj[v][k];
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                qu[tl++] = u;
            }
        }
    }
    return tl;
}

static long evaluate(void) {
    int P = p * d;
    long dups = 0;
    for (int t = 0; t < P; t++)
        for (int u = 0; u < t; u++)
            if (t / d == u / d && Jv[t] == Jv[u] && Sv[t] == Sv[u]) dups++;
    long unreached = 0;
    for (int i = 0; i < p; i++) unreached += V - reach_from(i * N);
    for (int j = 0; j < p; j++) unreached += V - reach_from((p + j) * N);
    return unreached + 1000L * dups;
}

static void shuffle_J(void) {
    int P = p * d, idx = 0;
    for (int j = 0; j < p; j++)
        for (int c = 0; c < d; c++) Jv[idx++] = j;
    for (int t = P - 1; t > 0; t--) {
        int k = rndint(t + 1);
        int tmp = Jv[t];
        Jv[t] = Jv[k];
        Jv[k] = tmp;
    }
}

static void random_S(void) {
    int P = p * d;
    for (int t = 0; t < P; t++) Sv[t] = rndint(N);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D seed time_limit p M K R\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    p = atoi(argv[5]);
    M = atoi(argv[6]);
    K = atoi(argv[7]);
    R = atoi(argv[8]);

    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1 || p < 1 || p > MAXP || M < 1 || K < 1) {
        printf("0 0\n");
        return 0;
    }
    N = M * K;
    if (2L * p * N > MAXV) {
        printf("0 0\n");
        return 0;
    }
    V = 2 * p * N;

    rp[0] = 1 % M;
    for (int b = 1; b < K; b++) rp[b] = (int)((long)rp[b - 1] * R % M);

    int P = p * d;
    shuffle_J();
    random_S();
    build();
    long cost = evaluate();
    long bestc = cost;
    long last = 0, it = 0;
    double tstart = now();
    double span = t_end - tstart;
    if (span < 1e-3) span = 1e-3;
    double T = 5.0;

    while (cost > 0 && now() < t_end) {
        it++;
        if ((it & 63) == 0) {
            double frac = (now() - tstart) / span;
            if (frac > 1.0) frac = 1.0;
            T = 8.0 * (1.0 - frac) + 0.3;
            if (it - last > RESTART) {
                shuffle_J();
                random_S();
                build();
                cost = evaluate();
                bestc = cost;
                last = it;
                continue;
            }
        }
        int type = rnd01() < 0.6 ? 0 : 1;
        int t1 = rndint(P);
        if (type == 0) {
            int ns = rndint(N), os = Sv[t1];
            if (ns == os) continue;
            Sv[t1] = ns;
            build();
            long nc = evaluate();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                Sv[t1] = os;
                build();
            }
        } else {
            int t2 = rndint(P);
            if (Jv[t1] == Jv[t2]) continue;
            int tmp = Jv[t1];
            Jv[t1] = Jv[t2];
            Jv[t2] = tmp;
            build();
            long nc = evaluate();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = Jv[t1];
                Jv[t1] = Jv[t2];
                Jv[t2] = tmp;
                build();
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = it;
        }
    }

    if (cost == 0) {
        long m = 0;
        for (int v = 0; v < V; v++)
            for (int k = 0; k < d; k++)
                if (v < adj[v][k]) m++;
        printf("%d %ld\n", V, m);
        for (int v = 0; v < V; v++)
            for (int k = 0; k < d; k++)
                if (v < adj[v][k]) printf("%d %d\n", v, adj[v][k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python driver: group enumeration and adaptive climb.
# ----------------------------------------------------------------------------

def _groups_of_order(N):
    """All (M, K, R) with Z_M x| Z_K of order N, R^K = 1 mod M, gcd(R, M) = 1."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    return out


def _bicayley_phase(best, d, D, rng, deadline):
    """Climb the order with C bi-Cayley searches; jump size adapts to success and failure."""
    frac = 0.05
    errors = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        p = rng.choice([1, 1, 2, 2, 3])
        n_min = best[0] // (2 * p) + 1
        jump = int(n_min * frac)
        N = n_min + rng.randrange(0, jump + 1)
        groups = _groups_of_order(N)
        if not groups:
            continue
        M, K, R = rng.choice(groups)
        sl = min(4.0, remaining - 0.5)
        if sl < 0.5:
            break
        try:
            text = lib.run_c(C_BICAYLEY, [d, D, rng.randrange(1 << 31), round(sl, 2), p, M, K, R],
                             timeout=sl + 10)
            n, e = lib.parse_graph_text(text)
        except (RuntimeError, ValueError):
            errors += 1
            if errors > 3:
                break
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            frac = min(0.1, frac * 1.25)
        else:
            frac = max(0.0005, frac * 0.8)
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley climb in C.
    if D >= 2 and time.monotonic() < end - 1.0:
        best = _bicayley_phase(best, d, D, rng, end)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
