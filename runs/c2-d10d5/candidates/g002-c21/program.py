"""Two-engine search for large bipartite graphs with max degree d and diameter D.

Stage A: the bi-Cayley lift annealer from the previous version (C engine), which
builds structured lifts over Z_m x| Z_k2.

Stage B (new): a general-graph engine that starts from the best valid graph and
grows it by inserting vertex pairs, then repairs diameter violations with
degree-preserving double-edge switches. Distances are checked by bit-parallel
reach masks on the full graph, and every accepted state is valid. The last
valid graph is returned, so the output is always valid.

Python handles exact constructions (PG, GQ, cycle, K_{d,d}) and validates every
output with lib.is_valid. The best valid graph found is always returned.
"""
import itertools
import time

import lib


C_BICAYLEY = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Bi-Cayley lift annealer over Z_m x| Z_k2.
 * Vertices: A_{i,g} = i*G+g (i<K), B_{j,h} = (K+j)*G+h, G = Z_m x| Z_k2 order.
 * Layer l: A_{i,g} ~ B_{lay[l][i], g*vol[l][i]}. Each layer is a perfect matching
 * between A-blocks and B-blocks, so degree is exactly L unless duplicate darts occur
 * (penalised). Left multiplication is an automorphism, so diameter <= D is equivalent
 * to: every vertex is within D of every block identity. That is checked with
 * bit-parallel reach masks (bit b of reach[v] = identity of block b within distance t).
 */

#define KMAX 4
#define PEN 1000.0
#define ITERS 12000L
#define PATIENCE 2500L

static uint64_t rs = 1;
static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t0;
static double budget_s;
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int dd, Dd;          /* degree and diameter */
static int gm, gk2, Gord;   /* group Z_gm x| Z_gk2, order Gord = gm*gk2 */
static int *pw;             /* pw[b] = r^b mod gm */
static int K, NV, L;
static int *lay, *ilay, *vol, *nbr;
static uint32_t *stR, *candR, *scrA, *scrB;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;
static int trials[KMAX + 1], wins[KMAX + 1];

static int popc32(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555u);
    x = (x & 0x33333333u) + ((x >> 2) & 0x33333333u);
    x = (x + (x >> 4)) & 0x0F0F0F0Fu;
    return (int)((x * 0x01010101u) >> 24);
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*k2+b. */
static int gmul(int x, int y) {
    int a1 = x / gk2, b1 = x % gk2, a2 = y / gk2, b2 = y % gk2;
    int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % gm);
    int b = (b1 + b2) % gk2;
    return a * gk2 + b;
}

/* Inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long t = ((long long)pw[nb] * a) % gm;
    int na = (int)((gm - t) % gm);
    return na * gk2 + nb;
}

static void sample_group(int target, int *om, int *ok2, int *orr) {
    static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int att = 0; att < 200; att++) {
        int k2 = K2S[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = (m >= 3) ? m - 1 : 1;   /* dihedral: (m-1)^2 = 1 mod m always */
        } else {
            r = -1;
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    int c = 2 + rndint(m - 2);
                    if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            }
            if (r < 0) continue;
        }
        *om = m; *ok2 = k2; *orr = r;
        return;
    }
    *om = (target < 2) ? 2 : target;
    *ok2 = 1;
    *orr = 1;
}

static void setup_group(int m, int k2, int r, int k) {
    gm = m; gk2 = k2; Gord = m * k2;
    K = k; L = dd; NV = 2 * K * Gord;
    pw = (int *)malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    lay = (int *)malloc(sizeof(int) * (size_t)(L * K));
    ilay = (int *)malloc(sizeof(int) * (size_t)(L * K));
    vol = (int *)malloc(sizeof(int) * (size_t)(L * K));
    nbr = (int *)malloc(sizeof(int) * (size_t)L * (size_t)NV);
    stR = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
    candR = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
    scrA = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
    scrB = (uint32_t *)malloc(sizeof(uint32_t) * (size_t)NV);
}

static void free_group(void) {
    free(pw); free(lay); free(ilay); free(vol); free(nbr);
    free(stR); free(candR); free(scrA); free(scrB);
    pw = NULL; lay = NULL; ilay = NULL; vol = NULL; nbr = NULL;
    stR = NULL; candR = NULL; scrA = NULL; scrB = NULL;
}

/* Write layer l neighbours of A-block i and B-block lay[l][i] from voltage vol[l][i]. */
static void set_dart(int l, int i) {
    int j = lay[l * K + i], s = vol[l * K + i];
    int *nb = nbr + (size_t)l * NV;
    int is = ginv(s);
    for (int g = 0; g < Gord; g++) {
        nb[i * Gord + g] = (K + j) * Gord + gmul(g, s);
        nb[(K + j) * Gord + g] = i * Gord + gmul(g, is);
    }
}

static void swap_lay(int l, int i1, int i2) {
    int *lp = lay + l * K;
    int *ip = ilay + l * K;
    int j1 = lp[i1], j2 = lp[i2];
    lp[i1] = j2; lp[i2] = j1;
    ip[j2] = i1; ip[j1] = i2;
}

static void random_init(void) {
    int *perm = (int *)malloc(sizeof(int) * (size_t)K);
    for (int l = 0; l < L; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            lay[l * K + i] = perm[i];
            ilay[l * K + perm[i]] = i;
            vol[l * K + i] = rndint(Gord);
        }
    }
    free(perm);
    for (int l = 0; l < L; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < L; l1++)
            for (int l2 = l1 + 1; l2 < L; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i]) c++;
    return c;
}

static double total_cost(const uint32_t *r) {
    long long s = 0;
    for (int v = 0; v < NV; v++) s += 2 * K - popc32(r[v]);
    return (double)s + PEN * (double)dupcount();
}

/* Reach masks after Dd rounds, written to out. */
static void compute_reach(uint32_t *out) {
    uint32_t *X = scrA, *Y = scrB;
    memset(X, 0, sizeof(uint32_t) * (size_t)NV);
    for (int b = 0; b < 2 * K; b++) X[(size_t)b * Gord] = 1u << b;
    for (int t = 0; t < Dd; t++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint32_t x = X[v];
            for (int l = 0; l < L; l++) x |= X[nbr[(size_t)l * NV + v]];
            Y[v] = x;
            changed |= (x != X[v]);
        }
        uint32_t *tmp = X; X = Y; Y = tmp;
        if (!changed) break;
    }
    memcpy(out, X, sizeof(uint32_t) * (size_t)NV);
}

static int accept(double c2, double c, double temp) {
    if (c2 <= c) return 1;
    return rnd01() < exp(-(c2 - c) / temp);
}

/* One annealing run from a random lift. Returns 1 when the lift is valid (state kept). */
static int sa_run(void) {
    random_init();
    compute_reach(stR);
    double cost = total_cost(stR);
    double c0 = cost > 1.0 ? cost : 1.0;
    double bestc = cost;
    long last = 0;
    uint32_t full = (uint32_t)((1ull << (2 * K)) - 1ull);

    for (long t = 0; t < ITERS; t++) {
        if (cost == 0.0) break;
        if (t - last > PATIENCE) break;
        if ((t & 31) == 0 && elapsed() > budget_s) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            int l = rndint(L);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_lay(l, i1, i2);
            set_dart(l, i1);
            set_dart(l, i2);
            compute_reach(candR);
            double c2 = total_cost(candR);
            if (accept(c2, cost, temp)) {
                uint32_t *tmp = stR; stR = candR; candR = tmp;
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                swap_lay(l, i1, i2);
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int off = rndint(NV);
            for (int q = 0; q < NV; q++) {
                int v = off + q;
                if (v >= NV) v -= NV;
                if (stR[v] != full) {
                    int b = v / Gord;
                    l = rndint(L);
                    if (b < K) i = b;
                    else i = ilay[l * K + (b - K)];
                    break;
                }
            }
        }
        if (l < 0) {
            l = rndint(L);
            i = rndint(K);
        }
        int old = vol[l * K + i];
        int nw = rndint(Gord);
        if (nw == old) continue;
        vol[l * K + i] = nw;
        set_dart(l, i);
        compute_reach(candR);
        double c2 = total_cost(candR);
        if (accept(c2, cost, temp)) {
            uint32_t *tmp = stR; stR = candR; candR = tmp;
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            vol[l * K + i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0.0;
}

static int pick_K(void) {
    if (rnd01() < 0.2) return 1 + rndint(KMAX);
    int bk = 1;
    double bs = -1.0;
    for (int k = 1; k <= KMAX; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

static void store_current(void) {
    int m = K * Gord * L;
    int *e = (int *)malloc(sizeof(int) * 2 * (size_t)m);
    int c = 0;
    for (int u = 0; u < K * Gord; u++)
        for (int l = 0; l < L; l++) {
            e[2 * c] = u;
            e[2 * c + 1] = nbr[(size_t)l * NV + u];
            c++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = NV;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    Dd = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_s = atof(argv[4]);
    rs = seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 > 0 && m0 > 0) {
        best_e = (int *)malloc(sizeof(int) * 2 * (size_t)m0);
        int c = 0;
        for (int q = 0; q < m0; q++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            best_e[2 * c] = u;
            best_e[2 * c + 1] = v;
            c++;
        }
        best_n = n0;
        best_m = c;
    }

    if (dd >= 1 && Dd >= 1) {
        while (elapsed() < budget_s) {
            int k = pick_K();
            int base = best_n / (2 * k);
            int spread = base / 8 + 1;
            if (spread < 2) spread = 2;
            int target = base + 1 + rndint(spread);
            if (target < 2) target = 2;
            int m, k2, r;
            sample_group(target, &m, &k2, &r);
            if (2LL * k * m * k2 <= best_n) continue;
            trials[k]++;
            setup_group(m, k2, r, k);
            int ok = sa_run();
            if (ok) {
                wins[k]++;
                if (NV > best_n) store_current();
            }
            free_group();
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int q = 0; q < best_m; q++) printf("%d %d\n", best_e[2 * q], best_e[2 * q + 1]);
    return 0;
}
"""


C_SWITCH = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* General bipartite graph engine: grow a valid graph by inserting vertex pairs,
 * repair by degree-preserving double-edge switches, keep the last valid state.
 * Vertex sides: side 0 (A) and side 1 (B); every edge is stored as (A, B).
 * Validity: reach masks after Dd rounds give every pair within distance Dd.
 */

#define CAP 10240
#define WC (CAP / 64)
#define ANNEAL_IT 400L

static uint64_t rs = 1;
static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t0;
static double budget_s;
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int dd, Dd;
static int N, M;
static unsigned char side[CAP];
static int deg[CAP];
static int *adj, *EA, *EB, *flagrm, *SA, *SB;
static int SN = 0, SM = -1;
static unsigned char *mat;
static uint64_t *R1, *R2;

static inline int isadj(int u, int v) {
    size_t k = (size_t)u * CAP + (size_t)v;
    return (mat[k >> 3] >> (k & 7)) & 1;
}
static inline void setbit(int u, int v, int x) {
    size_t k = (size_t)u * CAP + (size_t)v;
    if (x) mat[k >> 3] |= (unsigned char)(1u << (k & 7));
    else   mat[k >> 3] &= (unsigned char)~(1u << (k & 7));
}
static inline void setadj(int u, int v, int x) { setbit(u, v, x); setbit(v, u, x); }

static void adj_add(int v, int w) {
    adj[(size_t)v * dd + deg[v]] = w;
    deg[v]++;
}

static void adj_replace(int v, int old, int nw) {
    int *p = adj + (size_t)v * dd;
    for (int k = 0; k < deg[v]; k++) {
        if (p[k] == old) { p[k] = nw; return; }
    }
}

static void rebuild(void) {
    memset(deg, 0, sizeof(deg));
    memset(mat, 0, (size_t)CAP * CAP / 8);
    for (int i = 0; i < M; i++) {
        int a = EA[i], b = EB[i];
        adj_add(a, b);
        adj_add(b, a);
        setadj(a, b, 1);
    }
}

static void add_edge(int a, int b) {
    EA[M] = a; EB[M] = b; M++;
    adj_add(a, b);
    adj_add(b, a);
    setadj(a, b, 1);
}

/* Edges i=(a,b), j=(c,e) with a in A, c in A: replace by (a,e), (c,b). Self-inverse. */
static int try_switch(int i, int j) {
    int a = EA[i], b = EB[i], c = EA[j], e = EB[j];
    if (a == c || b == e) return 0;
    if (isadj(a, e) || isadj(c, b)) return 0;
    adj_replace(a, b, e);
    adj_replace(b, a, c);
    adj_replace(c, e, b);
    adj_replace(e, c, a);
    setadj(a, b, 0);
    setadj(c, e, 0);
    setadj(a, e, 1);
    setadj(c, b, 1);
    EB[i] = e;
    EB[j] = b;
    return 1;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Sum over vertices of the number of vertices NOT within distance Dd (0 iff valid). */
static long compute_cost(void) {
    int Wn = (N + 63) / 64;
    uint64_t *X = R1, *Y = R2;
    for (int v = 0; v < N; v++) {
        uint64_t *x = X + (size_t)v * WC;
        for (int w = 0; w < Wn; w++) x[w] = 0;
        x[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < Dd; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *x = X + (size_t)v * WC;
            uint64_t *y = Y + (size_t)v * WC;
            for (int w = 0; w < Wn; w++) y[w] = x[w];
            int *p = adj + (size_t)v * dd;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *z = X + (size_t)p[k] * WC;
                for (int w = 0; w < Wn; w++) y[w] |= z[w];
            }
            for (int w = 0; w < Wn; w++) {
                if (y[w] != x[w]) { changed = 1; break; }
            }
        }
        uint64_t *tmp = X; X = Y; Y = tmp;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) {
        uint64_t *x = X + (size_t)v * WC;
        int c = 0;
        for (int w = 0; w < Wn; w++) c += popc64(x[w]);
        cost += N - c;
    }
    return cost;
}

/* Insert a new A vertex x = N and new B vertex y = N+1. Remove dd-1 edges with
 * pairwise distinct endpoints (a_t, b_t); add (x, b_t), (a_t, y), and (x, y).
 * Every degree stays <= dd; a_t and b_t keep their degree. */
static void insert_pair(void) {
    int chosen[64], ca[64], cb[64];
    int nc = 0, want = dd - 1;
    if (want < 1) want = 1;
    if (want > 60) want = 60;
    int tries = 0;
    while (nc < want && M > 0 && tries < 20000) {
        tries++;
        int i = rndint(M);
        int ok = 1;
        for (int t = 0; t < nc; t++) {
            int c = chosen[t];
            if (EA[c] == EA[i] || EB[c] == EB[i]) { ok = 0; break; }
        }
        if (ok) chosen[nc++] = i;
    }
    for (int t = 0; t < nc; t++) {
        ca[t] = EA[chosen[t]];
        cb[t] = EB[chosen[t]];
    }
    for (int i = 0; i < M; i++) flagrm[i] = 0;
    for (int t = 0; t < nc; t++) flagrm[chosen[t]] = 1;
    int x = N, y = N + 1;
    side[x] = 0;
    side[y] = 1;
    int m2 = 0;
    for (int i = 0; i < M; i++) {
        if (!flagrm[i]) {
            EA[m2] = EA[i];
            EB[m2] = EB[i];
            m2++;
        }
    }
    for (int t = 0; t < nc; t++) {
        EA[m2] = x; EB[m2] = cb[t]; m2++;
        EA[m2] = ca[t]; EB[m2] = y; m2++;
    }
    EA[m2] = x; EB[m2] = y; m2++;
    N += 2;
    M = m2;
    rebuild();
}

/* Add edges between A and B vertices with spare degree (never increases distances). */
static void fill_greedy(void) {
    for (int a = 0; a < N; a++) {
        if (side[a] != 0 || deg[a] >= dd) continue;
        for (int b = 0; b < N && deg[a] < dd; b++) {
            if (side[b] != 1 || deg[b] >= dd || isadj(a, b)) continue;
            add_edge(a, b);
        }
    }
}

static int anneal(long maxit) {
    long cost = compute_cost();
    for (long it = 0; it < maxit && cost > 0; it++) {
        if ((it & 15) == 0 && elapsed() > budget_s) break;
        if (M < 2) break;
        double T = 1.5 * (1.0 - (double)it / (double)maxit) + 0.05;
        int i = rndint(M), j = rndint(M);
        if (i == j) continue;
        if (!try_switch(i, j)) continue;
        long c2 = compute_cost();
        long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = c2;
        } else {
            try_switch(i, j);
        }
    }
    return cost == 0;
}

static void save_snapshot(void) {
    SN = N;
    SM = M;
    memcpy(SA, EA, sizeof(int) * (size_t)M);
    memcpy(SB, EB, sizeof(int) * (size_t)M);
}

static void restore_snapshot(void) {
    N = SN;
    M = SM;
    memcpy(EA, SA, sizeof(int) * (size_t)M);
    memcpy(EB, SB, sizeof(int) * (size_t)M);
    rebuild();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    Dd = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_s = atof(argv[4]);
    rs = seed * 0x2545F4914F6CDD1DULL + 0x7654321ULL;
    t0 = clock();

    if (dd < 2 || dd > 60 || Dd < 2 || Dd > 60) {
        printf("0 0\n");
        return 0;
    }

    adj = malloc(sizeof(int) * (size_t)CAP * dd);
    EA = malloc(sizeof(int) * (size_t)CAP * dd);
    EB = malloc(sizeof(int) * (size_t)CAP * dd);
    flagrm = malloc(sizeof(int) * (size_t)CAP * dd);
    SA = malloc(sizeof(int) * (size_t)CAP * dd);
    SB = malloc(sizeof(int) * (size_t)CAP * dd);
    mat = calloc((size_t)CAP * CAP / 8, 1);
    R1 = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    R2 = malloc(sizeof(uint64_t) * (size_t)CAP * WC);
    if (!adj || !EA || !EB || !flagrm || !SA || !SB || !mat || !R1 || !R2) {
        printf("0 0\n");
        return 0;
    }

    N = 0;
    M = 0;
    int n0 = 0, m0 = 0;
    int usable = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && n0 <= CAP - 2 && m0 >= 0) {
        int *RU = malloc(sizeof(int) * (size_t)(m0 + 1));
        int *RV = malloc(sizeof(int) * (size_t)(m0 + 1));
        int kept = 0;
        N = n0;
        for (int q = 0; q < m0; q++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
            if (isadj(u, v) || deg[u] >= dd || deg[v] >= dd) continue;
            adj_add(u, v);
            adj_add(v, u);
            setadj(u, v, 1);
            RU[kept] = u;
            RV[kept] = v;
            kept++;
        }
        int *col = malloc(sizeof(int) * (size_t)n0);
        int *qu = malloc(sizeof(int) * (size_t)n0);
        for (int v = 0; v < n0; v++) col[v] = -1;
        int ok = 1;
        for (int s = 0; s < n0 && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            qu[qt++] = s;
            while (qh < qt && ok) {
                int v = qu[qh++];
                int *p = adj + (size_t)v * dd;
                for (int k = 0; k < deg[v]; k++) {
                    int w = p[k];
                    if (col[w] < 0) {
                        col[w] = 1 - col[v];
                        qu[qt++] = w;
                    } else if (col[w] == col[v]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
        if (ok) {
            for (int i = 0; i < kept; i++) {
                if (col[RU[i]] == col[RV[i]]) { ok = 0; break; }
            }
        }
        if (ok) {
            for (int v = 0; v < n0; v++) side[v] = (unsigned char)col[v];
            M = 0;
            for (int i = 0; i < kept; i++) {
                int u = RU[i], v = RV[i];
                if (side[u] == 0) { EA[M] = u; EB[M] = v; }
                else              { EA[M] = v; EB[M] = u; }
                M++;
            }
            N = n0;
            rebuild();
            usable = 1;
        }
        free(RU);
        free(RV);
        free(col);
        free(qu);
    }
    if (!usable) {
        N = 2 * dd;
        M = 0;
        for (int v = 0; v < N; v++) side[v] = (unsigned char)(v < dd ? 0 : 1);
        for (int a = 0; a < dd; a++)
            for (int b = dd; b < 2 * dd; b++) {
                EA[M] = a;
                EB[M] = b;
                M++;
            }
        rebuild();
    }

    long c0 = compute_cost();
    if (c0 > 0) {
        anneal(3000);
        c0 = compute_cost();
    }
    if (c0 == 0) save_snapshot();

    int step = 1;
    while (SM >= 0 && elapsed() < budget_s && N + 2 <= CAP - 2) {
        for (int k = 0; k < step && N + 2 <= CAP - 2; k++) insert_pair();
        fill_greedy();
        if (anneal(ANNEAL_IT)) {
            save_snapshot();
            int cap = N / 40 + 1;
            if (step * 2 <= cap) step *= 2;
        } else {
            restore_snapshot();
            if (step > 1) step /= 2;
        }
    }

    if (SM < 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", SN, SM);
    for (int i = 0; i < SM; i++) printf("%d %d\n", SA[i], SB[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (Python).
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t_start)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: degree 2, diameter D, bipartite
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe baseline: K_{d,d}, diameter 2.
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

    if D >= 4 and time.monotonic() - t_start < 0.4 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage A: bi-Cayley lift annealer, started from the best graph so far.
    budget_a = min(0.35 * time_limit, left() - 12.0)
    if budget_a >= 2.0:
        try:
            text = lib.run_c(
                C_BICAYLEY,
                [d, D, int(seed) % (1 << 31), round(budget_a, 2)],
                stdin_graph=best,
                timeout=max(1.0, left() - 2.0),
            )
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    # Stage B: grow the best valid graph with the general switch engine.
    budget_b = left() - 8.0
    if budget_b >= 3.0:
        try:
            text = lib.run_c(
                C_SWITCH,
                [d, D, int(seed) % (1 << 31), round(budget_b, 2)],
                stdin_graph=best,
                timeout=max(1.0, left() - 2.0),
            )
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
