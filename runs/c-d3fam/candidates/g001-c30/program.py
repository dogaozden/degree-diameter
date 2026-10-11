"""Bold variant for D = 3 targets: start from the Araujo-Pardo-Lopez record graph
(or a projective plane when that is Moore-extremal), then let a C annealer grow it
by one vertex at a time. Moves are degree-preserving 2-switches, endpoint rewires
that shift spare degree, and greedy edge fills. Every output is re-checked by
lib.is_valid, and a valid fallback is always kept.
"""
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define MAXD 64
#define MAXE 40000
#define CYC 40000

static int N, DEG_MAX, DIAM;
static int deg[MAXN];
static int adjl[MAXN][MAXD];
static int col[MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static int snapN = 0, snapM = 0;
static int snapU[MAXE], snapV[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int isadj(int a, int b) {
    int k;
    for (k = 0; k < deg[a]; k++) if (adjl[a][k] == b) return 1;
    return 0;
}
static void rep(int v, int old, int nw) {
    int k;
    for (k = 0; k < deg[v]; k++) if (adjl[v][k] == old) { adjl[v][k] = nw; return; }
}
static void rem(int v, int x) {
    int k;
    for (k = 0; k < deg[v]; k++) if (adjl[v][k] == x) {
        adjl[v][k] = adjl[v][deg[v] - 1];
        deg[v]--;
        return;
    }
}
static void addE(int v, int x) { adjl[v][deg[v]++] = x; }

/* Number of ordered pairs at distance > DIAM. Zero iff the graph has diameter <= DIAM. */
static long long cost_eval(void) {
    int n = N, W = (n + 63) >> 6, v, k, w, r;
    uint64_t (*cu)[MAXW] = bufA;
    uint64_t (*nx)[MAXW] = bufB;
    for (v = 0; v < n; v++) {
        for (w = 0; w < W; w++) cu[v][w] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        uint64_t (*t)[MAXW];
        for (v = 0; v < n; v++) {
            for (w = 0; w < W; w++) nx[v][w] = cu[v][w];
            for (k = 0; k < deg[v]; k++) {
                int u = adjl[v][k];
                for (w = 0; w < W; w++) nx[v][w] |= cu[u][w];
            }
        }
        t = cu; cu = nx; nx = t;
    }
    long long bad = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += popc(cu[v][w]);
        bad += n - c;
    }
    return bad;
}

static void snapshot(void) {
    int v, k;
    snapN = N;
    snapM = 0;
    for (v = 0; v < N; v++)
        for (k = 0; k < deg[v]; k++)
            if (adjl[v][k] > v && snapM < MAXE) {
                snapU[snapM] = v;
                snapV[snapM] = adjl[v][k];
                snapM++;
            }
}

/* Add every edge between opposite colour classes allowed by the degree cap. Never raises cost. */
static void fill_deficits(void) {
    int u, v;
    for (u = 0; u < N; u++) {
        if (deg[u] >= DEG_MAX) continue;
        for (v = u + 1; v < N && deg[u] < DEG_MAX; v++) {
            if (col[v] == col[u] || deg[v] >= DEG_MAX) continue;
            if (isadj(u, v)) continue;
            addE(u, v);
            addE(v, u);
        }
    }
}

/* 2-switch: edges a-b, c-e (a,c same colour) become a-e, c-b. Keeps all degrees. */
static int pick_switch(int *pa, int *pb, int *pc, int *pe) {
    int a = rndint(N), c = -1, t, tries, e, b;
    if (deg[a] == 0) return 0;
    b = adjl[a][rndint(deg[a])];
    for (tries = 0; tries < 8; tries++) {
        t = rndint(N);
        if (t != a && col[t] == col[a] && deg[t] > 0) { c = t; break; }
    }
    if (c < 0) return 0;
    e = adjl[c][rndint(deg[c])];
    if (b == e) return 0;
    if (isadj(a, e) || isadj(c, b)) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}
static void apply_switch(int a, int b, int c, int e) {
    rep(a, b, e); rep(e, c, a); rep(c, e, b); rep(b, a, c);
}
static void revert_switch(int a, int b, int c, int e) {
    rep(a, e, b); rep(b, c, a); rep(c, b, e); rep(e, a, c);
}

/* Rewire: edge a-b moves its endpoint a to a same-side vertex x with spare degree. */
static int cand[MAXN];
static int pick_rewire(int *pa, int *pb, int *px) {
    int a = rndint(N), b, nc = 0, t, tries, y;
    if (deg[a] == 0) return 0;
    b = adjl[a][rndint(deg[a])];
    for (t = 0; t < N; t++)
        if (t != a && col[t] == col[a] && deg[t] < DEG_MAX) cand[nc++] = t;
    if (nc == 0) return 0;
    for (tries = 0; tries < 8; tries++) {
        y = cand[rndint(nc)];
        if (!isadj(y, b)) {
            *pa = a; *pb = b; *px = y;
            return 1;
        }
    }
    return 0;
}
static void apply_rewire(int a, int b, int x) {
    rep(b, a, x); rem(a, b); addE(x, b);
}
static void revert_rewire(int a, int b, int x) {
    rem(x, b); addE(a, b); rep(b, x, a);
}

static void grow(void) {
    int x = N;
    N++;
    deg[x] = 0;
    col[x] = (int)(rnd64() & 1);
}

static long long on_valid(void) {
    snapshot();
    if (N < MAXN - 1) grow();
    return cost_eval();
}

int main(int argc, char **argv) {
    int d, D, n0, m0, i;
    unsigned long long seed;
    double tl;
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    tl = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    DEG_MAX = d;
    DIAM = D;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 <= 0 || n0 > MAXN - 2 || d < 1 || d >= MAXD - 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    for (i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX) continue;
        if (isadj(u, v)) continue;
        addE(u, v);
        addE(v, u);
    }
    /* Proper 2-colouring by BFS. */
    {
        static int stk[MAXN];
        for (i = 0; i < N; i++) col[i] = -1;
        for (i = 0; i < N; i++) {
            int sp = 0, k;
            if (col[i] >= 0) continue;
            col[i] = 0;
            stk[sp++] = i;
            while (sp) {
                int u = stk[--sp];
                for (k = 0; k < deg[u]; k++) {
                    int v = adjl[u][k];
                    if (col[v] < 0) { col[v] = 1 - col[u]; stk[sp++] = v; }
                }
            }
        }
    }

    snapshot();                      /* fallback: the input graph itself */
    long long cur = cost_eval();
    clock_t t0 = clock();
    long long it, since = 0;
    if (cur == 0) { cur = on_valid(); since = 0; }

    for (it = 0;; it++) {
        int a = 0, b = 0, c = 0, e = 0, x = 0, mt = 0;
        double T;
        if ((it & 255) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        since++;
        T = 2.0 * pow(0.02, (double)(since % CYC) / (double)CYC);
        if (rnd64() & 1) {
            if (pick_switch(&a, &b, &c, &e)) { apply_switch(a, b, c, e); mt = 1; }
        } else {
            if (pick_rewire(&a, &b, &x)) { apply_rewire(a, b, x); mt = 2; }
        }
        if (mt) {
            long long nc = cost_eval();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else if (mt == 1) {
                revert_switch(a, b, c, e);
            } else {
                revert_rewire(a, b, x);
            }
            if (cur == 0) { cur = on_valid(); since = 0; }
        }
        if (it % 200 == 0) {
            fill_deficits();
            cur = cost_eval();
            if (cur == 0) { cur = on_valid(); since = 0; }
        }
    }

    printf("%d %d\n", snapN, snapM);
    for (i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
    return 0;
}
"""


def _largest_valid(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def _pg_largest(d):
    """Incidence graph of PG(2,q) for the largest prime power q <= d-1 (degree q+1 <= d)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: always valid for D >= 2
    start = cands[0]

    if D == 3 and d >= 3:
        if lib.is_prime_power(d - 1):
            # Moore-extremal projective plane: nothing to grow.
            return _largest_valid([lib.projective_plane_incidence(d - 1)], d, D)
        # Start from the record construction, which is (d)-regular with d = q + 2.
        al = None
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                al = lib.araujo_lopez_graph(d - 2)
            except Exception:
                al = None
            if al is not None and lib.is_valid(al[0], al[1], d, D):
                cands.append(al)
                start = al
        if start is cands[0]:
            pg = _pg_largest(d)
            if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
                cands.append(pg)
                start = pg

    elapsed = time.monotonic() - t_start
    c_budget = 0.75 * time_limit - 2.0 - elapsed
    if c_budget >= 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                            stdin_graph=start, timeout=c_budget + 5.0)
            n, e = lib.parse_graph_text(out)
            cands.append((n, e))
        except (RuntimeError, ValueError):
            pass

    return _largest_valid(cands, d, D)
