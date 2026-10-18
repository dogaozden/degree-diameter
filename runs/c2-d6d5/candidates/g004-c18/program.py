import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine: bi-Cayley (voltage-lift) search over semidirect groups.
# Kept from the parent. It provides a strong d-regular starting graph.
# ----------------------------------------------------------------------------

C_BICAYLEY = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 6
#define GMAX 2000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0, haveBest = 0;
static int trials[MAXK + 1], wins[MAXK + 1];

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    G_ = G;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pw = malloc(sizeof(int) * k2);
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    /* RS[s][h] = g with g*s = h. */
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pw);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * N);
    tmpr = malloc(sizeof(u64) * N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

static int search(double tend, int iters, int patience) {
    int k = K_, d = d_, G = G_, N = N_;
    u64 full = (1ULL << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            setdart(l, i, lay[l][i], VS[l][i]);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    int last = 0;
    for (int t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > tend) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.4) temp = 0.4;
        if (k >= 2 && rndu() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            setdart(l, i1, t2, VS[l][i1]);
            setdart(l, i2, t1, VS[l][i2]);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                setdart(l, i1, t1, VS[l][i1]);
                setdart(l, i2, t2, VS[l][i2]);
            }
        } else {
            int l = rndi(d), i = rndi(k);
            /* Defect-targeted choice: aim at a random unreached vertex (heuristic, cost stays exact). */
            if (rndu() < 0.4) {
                int v = -1;
                for (int tr = 0; tr < 8; tr++) {
                    int c = rndi(N);
                    if (rch[c] != full) { v = c; break; }
                }
                if (v >= 0) {
                    int blk = v / G;
                    if (blk < k) i = blk;
                    else {
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == blk - k) { i = ii; break; }
                    }
                }
            }
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            setdart(l, i, lay[l][i], nw);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                VS[l][i] = old;
                setdart(l, i, lay[l][i], old);
            }
        }
    }
    return cost == 0;
}

static int pick_k(void) {
    if (rndu() < 0.2) return 1 + rndi(MAXK);
    double bs = -1.0;
    int bk = 1;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rndu();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = (argc > 5) ? atoi(argv[5]) : 2;
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static const int K2s[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    static int cand[GMAX + 5];

    bestN = minN - 1;   /* accept only graphs with more vertices than this */

    while (now() < tend) {
        int k = pick_k();
        int base = bestN / (2 * k);
        int Gmin = base + 1 + rndi(base / 8 + 2);
        if (Gmin < 2) Gmin = 2;
        int k2 = K2s[rndi(20)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        if (2 * k * m * k2 <= bestN) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        K_ = k;
        alloc_state(2 * k * G_);
        trials[k]++;
        int ok = search(tend, 20000, 3000);
        if (ok) {
            wins[k]++;
            if (N_ > bestN) {
                int kG = K_ * G_;
                int cnt = kG * d_;
                int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
                int p = 0;
                for (int u = 0; u < kG; u++)
                    for (int l = 0; l < d_; l++) {
                        ne[2 * p] = u;
                        ne[2 * p + 1] = nb[l * N_ + u];
                        p++;
                    }
                free(bE);
                bE = ne;
                bEc = cnt;
                bestN = N_;
                haveBest = 1;
            }
        }
    }

    if (!haveBest) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Stage 2 engine (new): annealed growth on general d-regular bipartite graphs.
#   - Start from the input graph (must be d-regular bipartite) or K_{d,d}.
#   - Cost = number of unordered vertex pairs at distance > D (bitset BFS).
#   - Moves = bipartite double-edge swaps (preserve degrees and bipartiteness).
#   - Growth = insert two new vertices x (side A), y (side B) by rewiring a
#     matching of d edges through them; then anneal back to cost 0.
#   - Output the largest graph reached with cost 0.
# ----------------------------------------------------------------------------

C_ANNEAL = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXV 1600
#define MAXW ((MAXV + 63) / 64)
#define MAXD 16
#define MAXIT 6000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, N_, nA_, nB_;
static int *nb, *col, *Av, *Bv;
static u64 *R0, *R1;
static int *outE = NULL, outEc = 0, outN = 0, haveOut = 0;

static int adjq(int u, int x) {
    for (int j = 0; j < d_; j++) if (nb[u * d_ + j] == x) return 1;
    return 0;
}

static void repl(int v, int oldv, int newv) {
    for (int j = 0; j < d_; j++)
        if (nb[v * d_ + j] == oldv) { nb[v * d_ + j] = newv; return; }
}

/* Number of unordered pairs at distance > D_. */
static long long eval_cost(void) {
    int n = N_, d = d_;
    int W = (n + 63) >> 6;
    memset(R0, 0, sizeof(u64) * (size_t)n * W);
    for (int v = 0; v < n; v++) R0[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = R1 + (size_t)v * W;
            const u64 *src = R0 + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int j = 0; j < d; j++) {
                const u64 *s2 = R0 + (size_t)nb[v * d + j] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *sw = R0; R0 = R1; R1 = sw;
    }
    long long cnt = 0;
    size_t total = (size_t)n * W;
    for (size_t i = 0; i < total; i++) cnt += popc(R0[i]);
    long long ordered_bad = (long long)n * n - cnt;
    return ordered_bad / 2;
}

/* Annealing with bipartite double-edge swaps. Returns 1 if cost reaches 0. */
static int anneal(int maxit, double tend) {
    int d = d_;
    long long cur = eval_cost();
    if (cur == 0) return 1;
    for (int it = 0; it < maxit; it++) {
        if ((it & 31) == 0 && now() > tend) return 0;
        double frac = (double)it / (double)maxit;
        double T = 0.15 + 1.2 * (1.0 - frac);
        int u = Av[rndi(nA_)], u2 = Av[rndi(nA_)];
        if (u == u2) continue;
        int j = rndi(d), j2 = rndi(d);
        int v = nb[u * d + j], v2 = nb[u2 * d + j2];
        if (adjq(u, v2) || adjq(u2, v)) continue;
        nb[u * d + j] = v2;
        nb[u2 * d + j2] = v;
        repl(v, u, u2);
        repl(v2, u2, u);
        long long c2 = eval_cost();
        if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            if (cur == 0) return 1;
        } else {
            nb[u * d + j] = v;
            nb[u2 * d + j2] = v2;
            repl(v, u2, u);
            repl(v2, u, u2);
        }
    }
    return cur == 0;
}

/* Insert two vertices x (side A) and y (side B) by rewiring a matching of d edges. */
static int grow_once(void) {
    int d = d_, n = N_;
    if (n + 2 > MAXV) return 0;
    int x = n, y = n + 1;
    int as[MAXD], bs[MAXD], js[MAXD];
    int ok = 0;
    for (int tr = 0; tr < 50 && !ok; tr++) {
        int cnt = 0;
        for (int t2 = 0; t2 < 4000 && cnt < d; t2++) {
            int a = Av[rndi(nA_)];
            int dup = 0;
            for (int k = 0; k < cnt; k++) if (as[k] == a) { dup = 1; break; }
            if (dup) continue;
            int j = rndi(d);
            int b = nb[a * d + j];
            for (int k = 0; k < cnt; k++) if (bs[k] == b) { dup = 1; break; }
            if (dup) continue;
            as[cnt] = a; bs[cnt] = b; js[cnt] = j; cnt++;
        }
        ok = (cnt == d);
    }
    if (!ok) return 0;
    for (int i = 0; i < d; i++) {
        nb[as[i] * d + js[i]] = y;   /* a_i now adjacent to y instead of b_i */
        repl(bs[i], as[i], x);       /* b_i now adjacent to x instead of a_i */
        nb[x * d + i] = bs[i];
        nb[y * d + i] = as[i];
    }
    col[x] = 0; col[y] = 1;
    Av[nA_++] = x;
    Bv[nB_++] = y;
    N_ = n + 2;
    return 1;
}

static void save_best(void) {
    int n = N_, d = d_;
    free(outE);
    outE = malloc(sizeof(int) * 2 * (size_t)(n * d / 2 + 1));
    outEc = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] != 0) continue;
        for (int j = 0; j < d; j++) {
            outE[2 * outEc] = v;
            outE[2 * outEc + 1] = nb[v * d + j];
            outEc++;
        }
    }
    outN = n;
    haveOut = 1;
}

static void print_out(void) {
    if (!haveOut) { printf("0 0\n"); return; }
    printf("%d %d\n", outN, outEc);
    for (int p = 0; p < outEc; p++) printf("%d %d\n", outE[2 * p], outE[2 * p + 1]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 2 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    int d = d_;

    nb = malloc(sizeof(int) * (size_t)MAXV * d);
    col = malloc(sizeof(int) * MAXV);
    Av = malloc(sizeof(int) * MAXV);
    Bv = malloc(sizeof(int) * MAXV);
    R0 = malloc(sizeof(u64) * (size_t)MAXV * MAXW);
    R1 = malloc(sizeof(u64) * (size_t)MAXV * MAXW);
    double tend = now() + tl;

    /* Optional start graph on stdin: must be d-regular and bipartite. */
    int n0 = 0, m0 = 0;
    int loaded = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && m0 > 0 && n0 <= MAXV - 2 &&
        (long long)2 * m0 == (long long)n0 * d) {
        int *eu = malloc(sizeof(int) * m0);
        int *ev = malloc(sizeof(int) * m0);
        int *fill = calloc(n0, sizeof(int));
        int *cq = malloc(sizeof(int) * n0);
        int good = 1;
        for (int i = 0; i < m0 && good; i++) {
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) good = 0;
            else if (eu[i] < 0 || ev[i] < 0 || eu[i] >= n0 || ev[i] >= n0 || eu[i] == ev[i]) good = 0;
        }
        if (good) {
            for (int i = 0; i < m0 && good; i++) {
                int u = eu[i], v = ev[i];
                if (fill[u] >= d || fill[v] >= d) { good = 0; break; }
                nb[u * d + fill[u]++] = v;
                nb[v * d + fill[v]++] = u;
            }
        }
        if (good) for (int v = 0; v < n0; v++) if (fill[v] != d) good = 0;
        if (good) {
            for (int v = 0; v < n0 && good; v++)
                for (int j = 0; j < d && good; j++)
                    for (int l = 0; l < j; l++)
                        if (nb[v * d + j] == nb[v * d + l]) { good = 0; break; }
        }
        if (good) {
            for (int v = 0; v < n0; v++) col[v] = -1;
            for (int s = 0; s < n0; s++) {
                if (col[s] >= 0) continue;
                col[s] = 0;
                int head = 0, tail = 0;
                cq[tail++] = s;
                while (head < tail) {
                    int u = cq[head++];
                    for (int j = 0; j < d; j++) {
                        int w = nb[u * d + j];
                        if (col[w] < 0) { col[w] = 1 - col[u]; cq[tail++] = w; }
                        else if (col[w] == col[u]) good = 0;
                    }
                }
            }
        }
        if (good) {
            nA_ = nB_ = 0;
            for (int v = 0; v < n0; v++) {
                if (col[v] == 0) Av[nA_++] = v;
                else Bv[nB_++] = v;
            }
            if (nA_ != nB_ || nA_ < d) good = 0;
        }
        if (good) { N_ = n0; loaded = 1; }
        free(eu); free(ev); free(fill); free(cq);
    }

    if (!loaded) {
        /* Start from K_{d,d}. */
        N_ = 2 * d;
        nA_ = nB_ = d;
        for (int a = 0; a < d; a++) {
            col[a] = 0;
            Av[a] = a;
            for (int j = 0; j < d; j++) nb[a * d + j] = d + j;
        }
        for (int b = 0; b < d; b++) {
            col[d + b] = 1;
            Bv[b] = d + b;
            for (int j = 0; j < d; j++) nb[(d + b) * d + j] = j;
        }
    }

    if (!anneal(MAXIT, tend)) { print_out(); return 0; }
    save_best();

    int *bk = malloc(sizeof(int) * (size_t)MAXV * d);
    while (now() < tend) {
        int n = N_;
        memcpy(bk, nb, sizeof(int) * (size_t)n * d);
        int savedNA = nA_, savedNB = nB_;
        int success = 0;
        for (int att = 0; att < 3 && now() < tend && !success; att++) {
            if (!grow_once()) break;
            if (anneal(MAXIT, tend)) {
                success = 1;
            } else {
                memcpy(nb, bk, sizeof(int) * (size_t)n * d);
                N_ = n;
                nA_ = savedNA;
                nB_ = savedNB;
            }
        }
        if (!success) break;
        save_best();
    }
    free(bk);
    print_out();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Safe baseline families.
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


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Main build: exact constructions, then bi-Cayley search, then annealed growth
# from the best regular graph found so far.
# ----------------------------------------------------------------------------

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
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    total = max(1.0, min(0.85 * time_limit, time_limit - 12.0))
    deadline = start + total

    # Stage 1: bi-Cayley search for a large regular starting graph.
    b1 = max(1.0, 0.5 * total)
    try:
        out = lib.run_c(C_BICAYLEY, [d, D, seed, round(b1, 2), best_n + 1],
                        timeout=b1 + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: annealed growth (new construction). Start from the best graph if it is
    # d-regular, otherwise from K_{d,d} inside the C program.
    b2 = deadline - time.monotonic() - 0.5
    if b2 >= 1.0:
        start_graph = best if _is_regular(best[0], best[1], d) else None
        try:
            out = lib.run_c(C_ANNEAL, [d, D, seed, round(b2, 2)],
                            stdin_graph=start_graph, timeout=b2 + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
