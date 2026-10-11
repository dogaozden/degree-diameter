import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (used as fallbacks and for the calibration case).
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
# C engine: generic (non-lift) bipartite graph search.
#
# The graph is kept as an explicit edge list between side-0 and side-1 vertices,
# so bipartiteness holds by construction. Max degree is kept <= Dd at all times.
# Cost = (ordered pairs at distance > DD) + LAM * (total degree deficit).
# Distances are computed with bitsets: reach_{t+1}(v) = OR of reach_t over N[v].
#
# Strategy: start from K_{d,d} (valid for DD >= 2), then repeatedly
#   anneal until valid, record the valid graph, and add vertex pairs.
# Moves: degree-preserving edge switch, "fill" (attach a deficient vertex to a
# non-neighbour, detaching one edge at a full endpoint), and rare edge removal.
# The best valid graph seen is always printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define MAXDEG 64
#define MAXE 40000
#define LAM 2
#define CHUNK 4000
#define FAILS_MAX 10

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double deadline = 0.0;
static int N = 0, E = 0, W = 1;
static int side[MAXN];
static int eu[MAXE], ev[MAXE];
static int bu[MAXE], bv[MAXE], bE = 0;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int lastbad = 0;
static int cur = 0;
static int outN = 0, outE = 0;
static int ou[MAXE], ov[MAXE], osd[MAXN];

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build_adj(void) {
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < E; i++) {
        int a = eu[i], b = ev[i];
        adj[a][deg[a]++] = b;
        adj[b][deg[b]++] = a;
    }
}

static int has_edge(int a, int b) {
    for (int i = 0; i < E; i++)
        if (eu[i] == a && ev[i] == b) return 1;
    return 0;
}

static int cost_eval(void) {
    build_adj();
    W = (N + 63) / 64;
    uint64_t (*X)[MAXW] = RA;
    uint64_t (*Y)[MAXW] = RB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) X[v][w] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DD; lvl++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) Y[v][w] = X[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) Y[v][w] |= X[u][w];
            }
            for (int w = 0; w < W; w++)
                if (Y[v][w] != X[v][w]) changed = 1;
        }
        uint64_t (*T)[MAXW] = X;
        X = Y;
        Y = T;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(X[v][w]);
        bad += N - c;
    }
    int def = 0;
    for (int v = 0; v < N; v++) def += Dd - deg[v];
    lastbad = (int)bad;
    return (int)bad + LAM * def;
}

static void save_state(void) {
    bE = E;
    memcpy(bu, eu, sizeof(int) * (size_t)E);
    memcpy(bv, ev, sizeof(int) * (size_t)E);
}

static void restore_state(void) {
    E = bE;
    memcpy(eu, bu, sizeof(int) * (size_t)E);
    memcpy(ev, bv, sizeof(int) * (size_t)E);
}

/* Remove a random edge having endpoint x (which = 0: x is eu side, 1: x is ev side). */
static void remove_random_at(int x, int which) {
    int cnt = 0;
    for (int i = 0; i < E; i++)
        if ((which ? ev[i] : eu[i]) == x) cnt++;
    if (cnt == 0) return;
    int k = rint_(cnt);
    for (int i = 0; i < E; i++) {
        if ((which ? ev[i] : eu[i]) == x) {
            if (k == 0) {
                E--;
                eu[i] = eu[E];
                ev[i] = ev[E];
                return;
            }
            k--;
        }
    }
}

/* Degree-preserving switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static int move_switch(void) {
    if (E < 2) return 0;
    int i = rint_(E), j = rint_(E);
    if (i == j || eu[i] == eu[j] || ev[i] == ev[j]) return 0;
    if (has_edge(eu[i], ev[j]) || has_edge(eu[j], ev[i])) return 0;
    int t = ev[i];
    ev[i] = ev[j];
    ev[j] = t;
    return 1;
}

/* Attach a deficient vertex p to a random non-neighbour on the other side.
   A full endpoint first gives up one random edge. */
static int move_fill(void) {
    static int L[MAXN];
    if (E + 2 >= MAXE) return 0;
    build_adj();
    int nl = 0;
    for (int v = 0; v < N; v++)
        if (deg[v] < Dd) L[nl++] = v;
    if (nl == 0) return 0;
    int p = L[rint_(nl)];
    int a = -1, b = -1;
    for (int t = 0; t < 30; t++) {
        int c = rint_(N);
        if (side[c] == side[p]) continue;
        int x = (side[p] == 0) ? p : c;
        int y = (side[p] == 0) ? c : p;
        if (!has_edge(x, y)) {
            a = x;
            b = y;
            break;
        }
    }
    if (a < 0) return 0;
    if (deg[a] >= Dd) remove_random_at(a, 0);
    if (deg[b] >= Dd) remove_random_at(b, 1);
    eu[E] = a;
    ev[E] = b;
    E++;
    return 1;
}

static int move_remove(void) {
    if (E < 1) return 0;
    int i = rint_(E);
    E--;
    eu[i] = eu[E];
    ev[i] = ev[E];
    return 1;
}

/* Returns 1 as soon as a valid state (lastbad == 0) is accepted, 0 otherwise. */
static int anneal(long iters, double T0, double T1) {
    for (long t = 0; t < iters; t++) {
        if ((t & 31) == 0 && now_s() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        save_state();
        double r = rdbl();
        int ok;
        if (r < 0.5)
            ok = move_switch();
        else if (r < 0.97)
            ok = move_fill();
        else
            ok = move_remove();
        if (!ok) continue;
        int c2 = cost_eval();
        if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            if (lastbad == 0) return 1;
        } else {
            restore_state();
        }
    }
    return 0;
}

static void grow(int pairs) {
    for (int k = 0; k < pairs; k++) {
        if (N + 2 > MAXN) return;
        if ((N + 2) * Dd / 2 + 4 > MAXE) return;
        side[N] = 0;
        side[N + 1] = 1;
        N += 2;
    }
}

static void record(void) {
    outN = N;
    outE = E;
    memcpy(ou, eu, sizeof(int) * (size_t)E);
    memcpy(ov, ev, sizeof(int) * (size_t)E);
    memcpy(osd, side, sizeof(int) * (size_t)N);
}

static void load_best(void) {
    N = outN;
    E = outE;
    memcpy(eu, ou, sizeof(int) * (size_t)E);
    memcpy(ev, ov, sizeof(int) * (size_t)E);
    memcpy(side, osd, sizeof(int) * (size_t)N);
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    if (Dd < 1 || Dd > MAXDEG || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    deadline = now_s() + tl;

    /* Start from K_{d,d}, which has diameter 2 and is valid for DD >= 2. */
    N = 2 * Dd;
    E = 0;
    for (int v = 0; v < N; v++) side[v] = (v >= Dd) ? 1 : 0;
    for (int a = 0; a < Dd; a++)
        for (int b = 0; b < Dd; b++) {
            eu[E] = a;
            ev[E] = Dd + b;
            E++;
        }
    cur = cost_eval();
    record();
    grow(1);
    cur = cost_eval();

    int fails = 0;
    while (now_s() < deadline) {
        if (anneal(CHUNK, 2.0, 0.2)) {
            cur = cost_eval();
            record();
            fails = 0;
            grow(1 + N / 200);
        } else {
            if (now_s() >= deadline) break;
            fails++;
            if (fails >= FAILS_MAX) {
                load_best();
                fails = 0;
                grow(1);
            }
        }
        cur = cost_eval();
    }

    if (outN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", outN, outE);
    for (int i = 0; i < outE; i++) printf("%d %d\n", ou[i], ov[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the generic C growth search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2 (and optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() - t0 < 0.5 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Generic search: grow a bipartite graph from K_{d,d} by annealing.
    elapsed = time.monotonic() - t0
    budget = min(0.85 * time_limit, time_limit - 8.0) - elapsed
    if budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            timeout=time_limit - 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
