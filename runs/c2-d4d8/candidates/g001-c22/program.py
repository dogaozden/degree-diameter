"""Bi-Cayley search over nonabelian groups (replaces the voltage-lift and grow-by-two engine).

Construction: pick a group G = Z_m x| Z_k (order N), a connection set S of d distinct elements,
and join A_g to B_{g*s} for every s in S. This graph is bipartite, d-regular, and has 2N vertices.
Left multiplication is an automorphism, so the diameter test only needs BFS from A_1 and B_1.
C hill-climbs over S (replacing one element at a time) to minimise the unreached pairs, then
grows the group order N. The engine ignores the start graph; build() keeps the best valid graph
of {start, engine output}, so a weak engine run cannot lower the score.

Risk: this family is untested against the 2184 record for d=4, D=8. If it finds nothing above
the start graph, build() returns the start graph (K_{4,4} for that case).
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 16

typedef struct { int m, k, r; int rp[MAXN]; } Grp;   /* rp[b] = r^b mod m */

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

static int gcd_i(int a, int b) {
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

/* Group Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_rp(Grp *G) {
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++)
        G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
}

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long na = (G->m - (long)G->rp[nb] * a % G->m) % G->m;
    return (int)na * G->k + nb;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r,m) = 1, r^k = 1 mod m. */
static int random_group(int N, Grp *G) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) {
                G->m = m; G->k = k; G->r = r;
                found = 1;
            }
        }
    }
    if (!found) return 0;
    set_rp(G);
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley core */

static int S[MAXD], Si[MAXD];
static int bestS[MAXD];
static Grp bestG;
static int bestN;
static int dist_[2 * MAXN], que_[2 * MAXN];

/* BFS from src in the bi-Cayley graph on 2N vertices (A_g = g, B_h = N + h).
 * Returns how many vertices lie within distance D of src. */
static int bfs_reach(const Grp *G, int N, int src) {
    int tot = 2 * N, h = 0, t = 0, reached = 1;
    for (int i = 0; i < tot; i++) dist_[i] = -1;
    dist_[src] = 0;
    que_[t++] = src;
    while (h < t) {
        int v = que_[h++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + gmul(G, v, S[i]);
                if (dist_[u] < 0) { dist_[u] = dv + 1; que_[t++] = u; reached++; }
            }
        } else {
            int hv = v - N;
            for (int i = 0; i < d; i++) {
                int u = gmul(G, hv, Si[i]);
                if (dist_[u] < 0) { dist_[u] = dv + 1; que_[t++] = u; reached++; }
            }
        }
    }
    return reached;
}

/* Number of (vertex, far vertex) incidences from A_1 and B_1. Zero means valid. */
static int evalbad(const Grp *G, int N) {
    return (2 * N - bfs_reach(G, N, 0)) + (2 * N - bfs_reach(G, N, N));
}

static void init_S(int N) {
    for (int i = 0; i < d; i++) {
        int c, ok;
        do {
            c = rndint(N);
            ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == c) { ok = 0; break; }
        } while (!ok);
        S[i] = c;
    }
}

/* Hill-climb on S: replace one element at a time. Returns 1 if bad == 0 before the deadline. */
static int climb(const Grp *G, int N, double deadline) {
    for (int i = 0; i < d; i++) Si[i] = ginv(G, S[i]);
    int bad = evalbad(G, N);
    for (long it = 0; bad > 0; it++) {
        if ((it & 127) == 0 && now() > deadline) break;
        int idx = rndint(d), old = S[idx];
        int c, ok;
        do {
            c = rndint(N);
            ok = 1;
            for (int j = 0; j < d; j++) if (S[j] == c) { ok = 0; break; }
        } while (!ok);
        S[idx] = c;
        Si[idx] = ginv(G, c);
        int nb = evalbad(G, N);
        if (nb <= bad || rndint(1000) < 3) {
            bad = nb;
        } else {
            S[idx] = old;
            Si[idx] = ginv(G, old);
        }
    }
    return bad == 0;
}

/* Full check on the explicit graph: every vertex must reach all 2N within D steps. */
static int adjl[2 * MAXN][MAXD];
static int degl[2 * MAXN];
static int dd[2 * MAXN], qq[2 * MAXN];

static int verify_full(const Grp *G, int N, const int *Sarr) {
    int tot = 2 * N;
    for (int v = 0; v < tot; v++) degl[v] = 0;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) {
            int a = g, b = N + gmul(G, g, Sarr[i]);
            if (degl[a] >= MAXD || degl[b] >= MAXD) return 0;
            adjl[a][degl[a]++] = b;
            adjl[b][degl[b]++] = a;
        }
    for (int s = 0; s < tot; s++) {
        for (int v = 0; v < tot; v++) dd[v] = -1;
        int h = 0, t = 0, reached = 1;
        dd[s] = 0;
        qq[t++] = s;
        while (h < t) {
            int v = qq[h++];
            if (dd[v] >= D) continue;
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[t++] = u; reached++; }
            }
        }
        if (reached != tot) return 0;
    }
    return 1;
}

static void print_best(void) {
    int N = bestN;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + gmul(&bestG, g, bestS[i]));
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    int ch;
    while ((ch = getchar()) != EOF) {}   /* start graph ignored */

    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    long moore = moore_bound();

    /* Baseline K_{d,d} = bi-Cayley over Z_d with S = Z_d. */
    static Grp G;
    bestN = d;
    bestG.m = d; bestG.k = 1; bestG.r = 1; set_rp(&bestG);
    for (int i = 0; i < d; i++) bestS[i] = i;

    long attempt = 0;
    while (now() < t_end) {
        int Nt = bestN + 1 + (int)(attempt % 3);
        attempt++;
        if (2L * Nt > moore || Nt > MAXN) {
            Nt = bestN + 1;
            if (2L * Nt > moore || Nt > MAXN) break;
        }
        if (!random_group(Nt, &G)) continue;
        init_S(Nt);
        double left = t_end - now();
        double slice = left / 25.0;
        if (slice < 0.3) slice = 0.3;
        double dl = now() + slice;
        if (dl > t_end) dl = t_end;
        if (climb(&G, Nt, dl)) {
            bestN = Nt;
            bestG = G;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
    }

    if (!verify_full(&bestG, bestN, bestS)) {
        /* Should not happen; fall back to K_{d,d} if it does. */
        bestN = d;
        bestG.m = d; bestG.k = 1; bestG.r = 1; set_rp(&bestG);
        for (int i = 0; i < d; i++) bestS[i] = i;
        if (!verify_full(&bestG, bestN, bestS)) { printf("0 0\n"); return 0; }
    }
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    if best[0] >= lib.moore_bound(d, D):
        return best   # Moore graph: nothing to search for

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the fallback
    return best
