"""Bi-Cayley search: for D >= 3 (after exact constructions), search directly for
bipartite graphs A_x ~ B_{x s} over semidirect products Z_m x| Z_k, with diameter
checked exactly from two BFS roots (the group acts transitively on each side).
The C engine walks through group orders N = (best order)/2 + 1, 2, ... and
keeps the largest order for which a valid connection set is found."""
import itertools
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
# C engine: bi-Cayley search over semidirect groups Z_m x| Z_k of order N.
# Vertices A_x = x (0..N-1), B_y = N + y. Edges A_x ~ B_{x*s} for s in S (|S| = d).
# Left multiplication is an automorphism, so diameter <= D iff the BFS balls of
# radius D around A_e and B_e cover the whole graph. Simulated annealing on S.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64
#define MAXNN 300000
#define ITERS 60000
#define PATIENCE 4000

static int d, D;
static double t_end;
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

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long pwm(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Group Z_gm x| Z_gk, element a*gk+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gm, gk;
static int *rp = NULL;
static int rpcap = 0;

static void set_group(int m, int k, int r) {
    gm = m;
    gk = k;
    if (rpcap < k) {
        free(rp);
        rp = malloc(sizeof(int) * (size_t)k);
        rpcap = k;
    }
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    long v = ((long)a + (long)rp[b] * c) % gm;
    return (int)v * gk + (b + e) % gk;
}

static int ginv(int t) {
    int a = t / gk, b = t % gk;
    int nb = (gk - b) % gk;
    long na = (-(long)rp[nb] * a) % gm;
    if (na < 0) na += gm;
    return (int)na * gk + nb;
}

static int divs[4096];
static int ndiv = 0;

static void compute_divs(int N) {
    ndiv = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0 && ndiv < 4096) divs[ndiv++] = m;
}

static int pick_group(int N) {
    for (int tries = 0; tries < 2000; tries++) {
        int m = divs[rndint(ndiv)];
        int k = N / m;
        int r = m == 1 ? 0 : rndint(m);
        if (gcdi(r, m) != 1) continue;
        if (pwm(r, k, m) != 1 % m) continue;
        if (m > 1 && r == 1 && rnd01() < 0.85) continue;  /* prefer nonabelian */
        set_group(m, k, r);
        return 1;
    }
    return 0;
}

static int NN = 0;
static int *Rt = NULL, *Qt = NULL, *Sel = NULL, *vis = NULL, *que = NULL;
static int stampv = 0;

static void resize(int N) {
    free(Rt); free(Qt); free(Sel); free(vis); free(que);
    NN = N;
    Rt = malloc(sizeof(int) * (size_t)d * N);
    Qt = malloc(sizeof(int) * (size_t)d * N);
    Sel = malloc(sizeof(int) * (size_t)d);
    vis = calloc((size_t)2 * N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)2 * N);
    compute_divs(N);
}

/* Set generator i to t and refresh its right-multiplication and inverse tables. */
static void setrow(int i, int t) {
    Sel[i] = t;
    int *R = Rt + (size_t)i * NN, *Q = Qt + (size_t)i * NN;
    for (int x = 0; x < NN; x++) R[x] = gmul(x, t);
    int ti = ginv(t);
    for (int y = 0; y < NN; y++) Q[y] = gmul(y, ti);
}

/* Number of vertices within distance D of src. */
static int ball(int src) {
    int N = NN;
    stampv++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + Rt[(size_t)i * N + v];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = Qt[(size_t)i * N + y];
                    if (vis[u] != stampv) { vis[u] = stampv; que[tail++] = u; }
                }
            }
        }
        if (tail == 2 * N) break;
    }
    return tail;
}

static int cost_now(void) {
    return (2 * NN - ball(0)) + (2 * NN - ball(NN));
}

static int attempt(long iters, long patience) {
    int N = NN;
    for (int i = 0; i < d; i++) {
        int t;
        for (;;) {
            t = rndint(N);
            int dup = 0;
            for (int j = 0; j < i; j++) if (Sel[j] == t) { dup = 1; break; }
            if (!dup) break;
        }
        setrow(i, t);
    }
    int cost = cost_now();
    int best = cost;
    long last = 0;
    for (long it = 0; it < iters; it++) {
        if (cost == 0) return 1;
        if ((it & 127) == 0 && now() > t_end) return 0;
        if (it - last > patience) return 0;
        double T = 0.2 + 1.8 * (1.0 - (double)it / (double)iters);
        int i = rndint(d);
        int old = Sel[i];
        int t;
        for (;;) {
            t = rndint(N);
            int dup = 0;
            for (int j = 0; j < d; j++) if (Sel[j] == t) { dup = 1; break; }
            if (!dup) break;
        }
        setrow(i, t);
        int c2 = cost_now();
        int delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            cost = c2;
            if (cost < best) { best = cost; last = it; }
        } else {
            setrow(i, old);
        }
    }
    return cost == 0;
}

static int *bestE = NULL;
static long bestCap = 0;
static long bestM = 0;
static int bestV = 0;

static void save_graph(void) {
    long M = (long)NN * d;
    if (bestCap < M) {
        free(bestE);
        bestE = malloc(sizeof(int) * 2 * (size_t)M);
        bestCap = M;
    }
    long c = 0;
    for (int x = 0; x < NN; x++)
        for (int i = 0; i < d; i++) {
            bestE[2 * c] = x;
            bestE[2 * c + 1] = NN + Rt[(size_t)i * NN + x];
            c++;
        }
    bestM = M;
    bestV = 2 * NN;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 0) n = 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    int N = n / 2 + 1;
    if (N < d + 1) N = d + 1;
    int found = 0;
    while (now() < t_end) {
        if (2L * N > moore || N > MAXNN) break;
        if (N != NN) resize(N);
        if (!pick_group(N)) continue;
        if (attempt(ITERS, PATIENCE)) {
            save_graph();
            found = 1;
            N++;
        }
    }
    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %ld\n", bestV, bestM);
    for (long c = 0; c < bestM; c++) printf("%d %d\n", bestE[2 * c], bestE[2 * c + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.85 * time_limit - 2.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best

    def consider(n, e):
        """Replace best with (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions for D = 3 and D = 4 (unchanged behaviour).
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

    # Bold new search: bi-Cayley graphs over semidirect products, grown in C.
    remaining = end - time.monotonic() - 0.5
    if remaining > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 1.5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
