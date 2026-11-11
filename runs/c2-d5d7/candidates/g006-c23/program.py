"""Two-phase search for the weakest cases (d = 5, D = 7 is the target).

Phase 1 is the bi-Cayley lift search from the parent. It uses semidirect groups Z_m x|_r Z_k and
hill-climbs the voltages for orders above half the start graph. It gets about half the time budget.

Phase 2 is new. It starts from the phase-1 graph, or from the start graph if phase 1 found nothing,
and grows it by one vertex pair at a time:
  * Vertex-pair insertion: remove d-1 edges with distinct endpoints, add a pair u (side A) and w
    (side B), join u-w, u to the d-1 freed B endpoints, and w to the d-1 freed A endpoints. Every
    degree is preserved, so the graph stays bipartite with max degree d.
  * Evaluation: a bitset-parallel BFS of depth D computes all pairs within distance D. It costs
    about a few milliseconds at n around 3000.
  * Repair: after a growth step, annealed double-edge switches try to bring the count of bad pairs
    to zero. A failed attempt is undone, and the last valid graph is kept.

Every phase keeps the last valid graph, so the output is never worse than the start graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Phase 1: bi-Cayley lift search over semidirect groups Z_m x|_r Z_k (parent's method).
 * Phase 2: vertex-pair insertion with degree-preserving edge removal, bitset BFS evaluation,
 *          annealed double-edge-switch repair, and undo on failure.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  the best valid graph found (never worse than the start graph).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 2048
#define MAXD 16
#define MAXE 200000
#define MAXCAND 512
#define STEPS 8000
#define SPAN 40
#define ATTEMPTS 3
#define MAXN 8192
#define MAXW (MAXN / 64)
#define REPAIR 300

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
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

/* ---------------- phase 1: bi-Cayley lift search (parent's method) ---------------- */

static int enum_groups(int N, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < MAXCAND) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < MAXCAND) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static Grp pick_group(const Grp *c, int cnt) {
    for (int tries = 0; tries < 8; tries++) {
        Grp g = c[rndint(cnt)];
        if (g.m > 1 && g.r != 1) return g;
    }
    return c[rndint(cnt)];
}

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int RP[MAXH];
static int NN;

static void setup_group(int N, Grp G) {
    NN = N;
    int m = G.m, k = G.k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            row[y] = (int)((((long)a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

static int used_upto(const int *gv, int cnt, int v) {
    for (int i = 0; i < cnt; i++)
        if (gv[i] == v) return 1;
    return 0;
}

static int dist_[2 * MAXH], seen_[2 * MAXH], q_[2 * MAXH];
static int stamp_ = 0;

static long eval_bad(const int *gv) {
    int N = NN, V = 2 * N;
    int gi[MAXD];
    for (int t = 0; t < d; t++) gi[t] = INVT[gv[t]];
    long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        int head = 0, tail = 0;
        stamp_++;
        seen_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int v = q_[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = MTAB + (size_t)v * N;
                for (int t = 0; t < d; t++) {
                    int u = N + row[gv[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            } else {
                const int *row = MTAB + (size_t)(v - N) * N;
                for (int t = 0; t < d; t++) {
                    int u = row[gi[t]];
                    if (seen_[u] != stamp_) {
                        seen_[u] = stamp_;
                        dist_[u] = dv + 1;
                        q_[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static long climb(int *gv, double until) {
    long bad = eval_bad(gv);
    double T = 2.0;
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = 1 + rndint(d - 1);
        int old = gv[t], nv;
        do { nv = rndint(NN); } while (used_upto(gv, d, nv));
        gv[t] = nv;
        long nb = eval_bad(gv);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else gv[t] = old;
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
    }
    return bad;
}

/* Returns 1 and fills OU/OV (edges of the best lift, a-side x, b-side N+y) if a lift was found. */
static int lift_phase(int sn, int *bestN_out, int *OU, int *OV, int *ne_out) {
    int found = 0, bestN = 0, ne = 0;
    *bestN_out = 0;
    *ne_out = 0;
    if (!(d >= 3 && d <= MAXD && D >= 2)) return 0;
    long moore = moore_bound();
    long Nlo_l = sn / 2 + 1;
    if (Nlo_l < d + 1) Nlo_l = d + 1;
    long Nmax_l = moore / 2;
    if (Nmax_l > MAXH) Nmax_l = MAXH;
    int Nlo = (int)Nlo_l, Nmax = (int)Nmax_l;
    static Grp cand[MAXCAND];
    int gv[MAXD];

    while (now() < t_end && Nlo <= Nmax) {
        int span = Nmax - Nlo + 1;
        if (span > SPAN) span = SPAN;
        double u = rnd01();
        int N = Nlo + (int)(u * u * span);
        if (N > Nmax) N = Nmax;
        int cnt = enum_groups(N, cand);
        if (cnt <= 0) continue;
        int ok = 0;
        for (int att = 0; att < ATTEMPTS && !ok && now() < t_end; att++) {
            Grp G = pick_group(cand, cnt);
            setup_group(N, G);
            gv[0] = 0;
            for (int t = 1; t < d; t++) {
                do { gv[t] = rndint(N); } while (used_upto(gv, t, gv[t]));
            }
            long bad = climb(gv, t_end);
            if (bad == 0) {
                ok = 1;
                found = 1;
                bestN = N;
                Nlo = N + 1;
                ne = 0;
                for (int x = 0; x < N; x++)
                    for (int t = 0; t < d; t++) {
                        OU[ne] = x;
                        OV[ne] = N + MTAB[(size_t)x * N + gv[t]];
                        ne++;
                    }
            }
        }
    }
    *bestN_out = bestN;
    *ne_out = ne;
    return found;
}

/* ---------------- phase 2: vertex-pair insertion + annealed repair ---------------- */

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Gr;

static Gr CUR, WRK, BEST;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

static void g_add(Gr *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

static void g_del_one(Gr *g, int a, int b) {
    int *row = g->adj[a];
    int dg = g->deg[a];
    for (int i = 0; i < dg; i++)
        if (row[i] == b) {
            row[i] = row[dg - 1];
            g->deg[a]--;
            return;
        }
}

static void g_remove(Gr *g, int a, int b) {
    g_del_one(g, a, b);
    g_del_one(g, b, a);
}

static int g_has(const Gr *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++)
        if (g->adj[a][i] == b) return 1;
    return 0;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D (bitset BFS from every vertex). */
static long g_bad(const Gr *g) {
    int n = g->n;
    int W = (n + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s2 = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) tot += popc(row[w]);
    }
    return ((long)n * n - tot) / 2;
}

static int pick_side0(const Gr *g) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(g->n);
        if (g->side[v] == 0 && g->deg[v] > 0) return v;
    }
    return -1;
}

/* Remove d-1 edges with distinct endpoints; add pair u (side 0), w (side 1), u-w,
 * u to the freed side-1 endpoints, w to the freed side-0 endpoints. Degrees are preserved. */
static int g_grow(Gr *g) {
    int k = d - 1;
    int ea[MAXD], eb[MAXD];
    int cnt = 0;
    if (k < 1) return 0;
    for (int tries = 0; tries < 4000 && cnt < k; tries++) {
        int a = pick_side0(g);
        if (a < 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        int ok = 1;
        for (int i = 0; i < cnt; i++)
            if (ea[i] == a || eb[i] == b) { ok = 0; break; }
        if (!ok) continue;
        ea[cnt] = a;
        eb[cnt] = b;
        cnt++;
    }
    if (cnt < k) return 0;
    if (g->n + 2 > MAXN) return 0;
    for (int i = 0; i < k; i++) g_remove(g, ea[i], eb[i]);
    int u = g->n, w = g->n + 1;
    g->n += 2;
    g->deg[u] = 0;
    g->deg[w] = 0;
    g->side[u] = 0;
    g->side[w] = 1;
    g_add(g, u, w);
    for (int i = 0; i < k; i++) {
        g_add(g, u, eb[i]);
        g_add(g, w, ea[i]);
    }
    return 1;
}

/* Double-edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1); keeps degrees and bipartiteness. */
static int g_switch(Gr *g, int *q) {
    for (int t = 0; t < 100; t++) {
        int a1 = pick_side0(g), a2 = pick_side0(g);
        if (a1 < 0 || a2 < 0 || a1 == a2) continue;
        int b1 = g->adj[a1][rndint(g->deg[a1])];
        int b2 = g->adj[a2][rndint(g->deg[a2])];
        if (b1 == b2) continue;
        if (g_has(g, a1, b2) || g_has(g, a2, b1)) continue;
        g_remove(g, a1, b1);
        g_remove(g, a2, b2);
        g_add(g, a1, b2);
        g_add(g, a2, b1);
        q[0] = a1;
        q[1] = b1;
        q[2] = a2;
        q[3] = b2;
        return 1;
    }
    return 0;
}

static void g_unswitch(Gr *g, const int *q) {
    g_remove(g, q[0], q[3]);
    g_remove(g, q[2], q[1]);
    g_add(g, q[0], q[1]);
    g_add(g, q[2], q[3]);
}

/* Load a bipartite graph with max degree d. Returns 0 on any violation. */
static int load_graph(Gr *g, int n, const int *U, const int *V, int m) {
    static int Q[MAXN];
    if (n <= 0 || n > MAXN) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 2;
    }
    for (int e = 0; e < m; e++) {
        int a = U[e], b = V[e];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) return 0;
        if (g->deg[a] >= d || g->deg[b] >= d) return 0;
        if (g_has(g, a, b)) return 0;
        g_add(g, a, b);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 2) continue;
        g->side[s] = 0;
        int h = 0, t = 0;
        Q[t++] = s;
        while (h < t) {
            int v = Q[h++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 2) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    Q[t++] = u;
                } else if (g->side[u] == g->side[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_graph(const Gr *g) {
    long m = 0;
    for (int v = 0; v < g->n; v++)
        if (g->side[v] == 0) m += g->deg[v];
    printf("%d %ld\n", g->n, m);
    for (int v = 0; v < g->n; v++) {
        if (g->side[v] != 0) continue;
        for (int i = 0; i < g->deg[v]; i++) printf("%d %d\n", v, g->adj[v][i]);
    }
}

static void phase2(double until) {
    BEST = CUR;
    while (now() < until) {
        if (CUR.n + 2 > MAXN) break;
        WRK = CUR;
        if (!g_grow(&WRK)) continue;
        long bad = g_bad(&WRK);
        for (int s = 0; s < REPAIR && bad > 0 && now() < until; s++) {
            int q[4];
            if (!g_switch(&WRK, q)) continue;
            long nb = g_bad(&WRK);
            double T = 0.4 + 2.0 * (1.0 - (double)s / REPAIR);
            if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
                bad = nb;
            } else {
                g_unswitch(&WRK, q);
            }
        }
        if (bad == 0) {
            CUR = WRK;
            if (CUR.n > BEST.n) BEST = CUR;
        }
    }
}

static Gr *base_buf;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static int SU[MAXE], SV[MAXE];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0 || sm > MAXE) { sn = 0; sm = 0; }
    int got = 0;
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) break;
        got++;
    }
    if (got != sm) { sn = 0; sm = 0; }

    static int OU[MAXH * MAXD], OV[MAXH * MAXD];
    int bestN = 0, ne = 0;
    int lifted = 0;
    int usable = (d >= 3 && d <= MAXD);
    (void)base_buf;

    if (usable) {
        t_end = t0 + 0.5 * limit;
        lifted = lift_phase(sn, &bestN, OU, OV, &ne);
    }

    int base_ok = 0;
    if (usable) {
        if (lifted) base_ok = load_graph(&CUR, 2 * bestN, OU, OV, ne);
        if (base_ok && g_bad(&CUR) != 0) base_ok = 0;
        if (!base_ok) base_ok = load_graph(&CUR, sn, SU, SV, sm);
        if (base_ok && g_bad(&CUR) != 0) base_ok = 0;
    }

    if (base_ok) {
        phase2(t0 + 0.92 * limit);
        print_graph(&BEST);
    } else {
        printf("%d %d\n", sn, sm);
        for (int e = 0; e < sm; e++) printf("%d %d\n", SU[e], SV[e]);
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

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
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

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
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
            # Points of the line: x, and t*x + y for t in GF(q).
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

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
