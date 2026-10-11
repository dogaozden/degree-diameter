import time

import lib


# ----------------------------------------------------------------------------
# Two-phase C engine (one program, selected by argv[5]).
#
# Mode 0 (lift): random voltage lifts of semidirect products Z_m x| Z_k2 over a
#   base of K A-blocks and K B-blocks, annealed on the number of bad vertex pairs.
#   It keeps the largest zero-cost lift it finds.
#
# Mode 1 (repair): an UNSTRUCTURED search. It reads a regular bipartite graph
#   from stdin (A = vertices [0,N), B = [N,2N)) and grows it one vertex per side
#   at a time. Each growth step splices a new A-vertex and a new B-vertex into
#   d edges, which keeps every degree at d. Then double-edge swaps (which keep
#   the graph bipartite and regular) are annealed until the bad-pair count reaches
#   zero. Failed attempts are rolled back.
#
# Distances are computed with bitsets: reach[v] holds every vertex within
# distance D of v, so bad pairs = sum over v of (2N - |reach[v]|) / 2.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 1600
#define MAXW 26
#define MAXD 16
#define BIG 1000000000LL
#define LIFT_IT 3000
#define REP_IT 2500

static int d, D, N, have = 0, bestN = 0;
static int *nb, *bestnb, *sv, *cntv;
static uint64_t *R1, *R2;
static uint64_t rs[2];
static struct timespec T0;
static double DL;
static int K, K2, M, RR, G, T;
static int dI[64], dJ[64], dS[64];
static int rp[64];

static uint64_t sm(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static uint64_t rnd(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}
static int ri(int n) { return (int)(rnd() % (uint64_t)n); }
static double ru(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double el(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return (double)(t.tv_sec - T0.tv_sec) + 1e-9 * (double)(t.tv_nsec - T0.tv_nsec);
}
static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powm(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) { if (e & 1) r = r * x % m; x = x * x % m; e >>= 1; }
    return (int)r;
}

/* Number of bad unordered pairs (distance > D) in the graph on 2N vertices. */
static long long cost(void) {
    int V = 2 * N, W = (V + 63) / 64;
    for (int v = 0; v < V; v++) {
        for (int w = 0; w < W; w++) R1[(size_t)v * W + w] = 0;
        R1[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    }
    for (int lv = 0; lv < D; lv++) {
        for (int v = 0; v < V; v++) {
            uint64_t *o = R2 + (size_t)v * W;
            memcpy(o, R1 + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *p = nb + (size_t)v * d;
            for (int k = 0; k < d; k++) {
                const uint64_t *s = R1 + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = R1; R1 = R2; R2 = t;
    }
    long long tot = 0;
    for (int v = 0; v < V; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(R1[(size_t)v * W + w]);
        tot += V - c;
    }
    return tot / 2;
}

static void rep(int v, int old, int nw) {
    int *p = nb + (size_t)v * d;
    for (int k = 0; k < d; k++) if (p[k] == old) { p[k] = nw; return; }
}
static int has(int v, int u) {
    const int *p = nb + (size_t)v * d;
    for (int k = 0; k < d; k++) if (p[k] == u) return 1;
    return 0;
}
/* Edges a1-b1 and a2-b2 become a1-b2 and a2-b1. Calling it again with (a1,b2,a2,b1) undoes it. */
static void xswap(int a1, int b1, int a2, int b2) {
    rep(a1, b1, b2); rep(b1, a1, a2); rep(a2, b2, b1); rep(b2, a2, a1);
}

static void save_best(void) {
    memcpy(bestnb, nb, sizeof(int) * (size_t)2 * N * d);
    bestN = N;
    have = 1;
}

/* ---------------- mode 0: voltage lifts over semidirect products ---------------- */

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)rp[b] * c) % M);
    return ra * K2 + (b + e) % K2;
}

static long long lift_eval(void) {
    T = d * K; G = M * K2; N = K * G;
    for (int t1 = 0; t1 < T; t1++)
        for (int t2 = t1 + 1; t2 < T; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) return BIG;
    for (int v = 0; v < 2 * N; v++) cntv[v] = 0;
    for (int t = 0; t < T; t++)
        for (int g = 0; g < G; g++) {
            int a = dI[t] * G + g, b = N + dJ[t] * G + gmul(g, dS[t]);
            nb[(size_t)a * d + cntv[a]++] = b;
            nb[(size_t)b * d + cntv[b]++] = a;
        }
    return cost();
}

static void lift_mode(void) {
    static const int kc[3] = {1, 2, 3};
    while (el() < DL) {
        int k = kc[ri(3)];
        int gmin = bestN / k + 1;
        int g = gmin + ri(gmin / 6 + 2);
        if (g < 2) g = 2;
        int opts[12], no = 0;
        for (int c = 1; c <= 12; c++) if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int c2 = opts[ri(no)], m = g / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found && m >= 2; tr++) {
                int cand = 1 + ri(m - 1);
                if (gcd_i(cand, m) == 1 && powm(cand, c2, m) == 1 % m) { r = cand; found = 1; }
            }
            if (!found) { c2 = 1; m = g; r = 1; }
        }
        if (k * g > MAXV / 2) continue;
        K = k; K2 = c2; M = m; RR = r;
        rp[0] = 1 % M;
        for (int b = 1; b < K2; b++) rp[b] = (int)((long long)rp[b - 1] * RR % M);
        G = M * K2;
        for (int l = 0; l < d; l++) {
            int p[4];
            for (int i = 0; i < K; i++) p[i] = i;
            for (int i = K - 1; i > 0; i--) { int j = ri(i + 1); int tmp = p[i]; p[i] = p[j]; p[j] = tmp; }
            for (int i = 0; i < K; i++) {
                int t = l * K + i;
                dI[t] = i; dJ[t] = p[i]; dS[t] = ri(G);
            }
        }
        long long c = lift_eval();
        for (int it = 0; it < LIFT_IT && c > 0; it++) {
            if ((it & 31) == 0 && el() > DL) break;
            double tmp = 1.0 * (1.0 - (double)it / LIFT_IT) + 0.05;
            if (K > 1 && ru() < 0.3) {
                int l = ri(d), i1 = ri(K), i2 = ri(K);
                if (i1 == i2) continue;
                int t1 = l * K + i1, t2 = l * K + i2;
                int sw = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = sw;
                long long cv = lift_eval();
                if (cv <= c || ru() < exp(-(double)(cv - c) / tmp)) c = cv;
                else { sw = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = sw; lift_eval(); }
            } else {
                int t = ri(T), old = dS[t], nw = ri(G);
                if (nw == old) continue;
                dS[t] = nw;
                long long cv = lift_eval();
                if (cv <= c || ru() < exp(-(double)(cv - c) / tmp)) c = cv;
                else { dS[t] = old; lift_eval(); }
            }
        }
        if (c == 0) save_best();
    }
}

/* ---------------- mode 1: unstructured growth and repair ---------------- */

/* Add one A-vertex (id o) and one B-vertex (id o+1 + o, i.e. 2o+1), spliced into d edges. */
static void grow(void) {
    int o = N;
    memmove(nb + (size_t)(o + 1) * d, nb + (size_t)o * d, sizeof(int) * (size_t)o * d);
    for (int v = 0; v < o; v++)
        for (int k = 0; k < d; k++)
            if (nb[(size_t)v * d + k] >= o) nb[(size_t)v * d + k]++;
    N = o + 1;
    int na = o, nbB = 2 * o + 1;
    int xs[MAXD], ys[MAXD], nx = 0;
    while (nx < d) {
        int x = ri(o), k = ri(d);
        int y = nb[(size_t)x * d + k];
        int ok = 1;
        for (int i = 0; i < nx; i++) if (xs[i] == x || ys[i] == y) { ok = 0; break; }
        if (ok) { xs[nx] = x; ys[nx] = y; nx++; }
    }
    for (int i = 0; i < d; i++) {
        int x = xs[i], y = ys[i];
        rep(x, y, nbB);
        rep(y, x, na);
        nb[(size_t)na * d + i] = y;
        nb[(size_t)nbB * d + i] = x;
    }
}

static void repair_mode(void) {
    while (el() < DL && N < MAXV / 2) {
        int o = N;
        memcpy(sv, nb, sizeof(int) * (size_t)2 * o * d);
        grow();
        long long c = cost();
        for (int it = 0; it < REP_IT && c > 0; it++) {
            if ((it & 31) == 0 && el() > DL) break;
            double tmp = 1.2 * (1.0 - (double)it / REP_IT) + 0.05;
            int a1 = ri(N), k1 = ri(d), a2 = ri(N), k2 = ri(d);
            int b1 = nb[(size_t)a1 * d + k1], b2 = nb[(size_t)a2 * d + k2];
            if (a1 == a2 || b1 == b2 || has(a1, b2) || has(a2, b1)) continue;
            xswap(a1, b1, a2, b2);
            long long cv = cost();
            if (cv <= c || ru() < exp(-(double)(cv - c) / tmp)) c = cv;
            else xswap(a1, b2, a2, b1);
        }
        if (c == 0) save_best();
        else { N = o; memcpy(nb, sv, sizeof(int) * (size_t)2 * o * d); }
    }
}

static int read_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 2 || n % 2 || n > MAXV || m < 0) return 0;
    N = n / 2;
    for (int v = 0; v < n; v++) cntv[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u >= N && v < N) { int t = u; u = v; v = t; }
        if (!(u >= 0 && u < N && v >= N && v < n)) return 0;
        if (cntv[u] >= d || cntv[v] >= d) return 0;
        for (int k = 0; k < cntv[u]; k++) if (nb[(size_t)u * d + k] == v) return 0;
        nb[(size_t)u * d + cntv[u]++] = v;
        nb[(size_t)v * d + cntv[v]++] = u;
    }
    for (int v = 0; v < n; v++) if (cntv[v] != d) return 0;
    return cost() == 0;
}

static void output(void) {
    if (!have) { printf("0 0\n"); return; }
    printf("%d %d\n", 2 * bestN, bestN * d);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", v, bestnb[(size_t)v * d + k]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time mode [startN]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10) * 2654435761ULL + 12345ULL;
    rs[0] = sm(&sd);
    rs[1] = sm(&sd);
    DL = atof(argv[4]);
    int mode = atoi(argv[5]);
    int startN = argc > 6 ? atoi(argv[6]) : 0;
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    nb = malloc(sizeof(int) * (size_t)MAXV * MAXD);
    bestnb = malloc(sizeof(int) * (size_t)MAXV * MAXD);
    sv = malloc(sizeof(int) * (size_t)MAXV * MAXD);
    cntv = malloc(sizeof(int) * (size_t)MAXV);
    R1 = malloc(sizeof(uint64_t) * (size_t)MAXV * MAXW);
    R2 = malloc(sizeof(uint64_t) * (size_t)MAXV * MAXW);
    if (mode == 0) {
        bestN = startN;
        lift_mode();
    } else if (read_graph()) {
        save_best();
        repair_mode();
    }
    output();
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    # Reserve covers the C compile(s), parsing and validation.
    remaining = 0.90 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 4.0:
        lift_t = 0.35 * remaining
        rep_t = remaining - lift_t
        # Phase 1: lift search for a large regular bipartite start graph.
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{lift_t:.2f}", 0, best_n // 2],
                            timeout=lift_t + 6.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass
        # Phase 2: unstructured splice-and-repair growth from the best graph so far.
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{rep_t:.2f}", 1],
                            stdin_graph=best, timeout=rep_t + 6.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
