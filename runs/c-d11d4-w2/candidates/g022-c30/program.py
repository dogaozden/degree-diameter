import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage-lift search over semidirect products Z_M x| Z_K2.
#
# A random d-regular bipartite base on K + K vertices (d perfect matchings) is
# lifted over a group of order G. Each dart carries a group element. The lift
# has 2*K*G vertices, is bipartite, and has max degree d. Simulated annealing
# changes one voltage at a time and minimises the number of vertex pairs at
# distance > D. Each attempt draws a fresh base, group and K. A zero-cost lift
# that beats the current best order becomes the new best, and the target order
# moves up.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXD 32
#define MAXN 4096
#define MAXG 2048
#define WMAX 64

static int DEG, DIAM, KMAX;
static double TL, TSTART;
static uint64_t rs = 1;
static int GG, MM, K2, KB, NN, dN;
static int du[MAXK * MAXD], dv[MAXK * MAXD], dg[MAXK * MAXD];
static int mtbuf[MAXG * MAXG];
static int pwv[MAXG];
static int ladj[MAXN][MAXD];
static int ldeg[MAXN];
static uint64_t RA[MAXN * WMAX], RB[MAXN * WMAX];
static int bestEu[MAXN * MAXD / 2], bestEv[MAXN * MAXD / 2];
static int bestNE, bestNN;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static double cpu_now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Random semidirect product Z_M x| Z_K2 of order G; element (a,b) is coded a*K2+b. */
static int setup_group(int G) {
    int divs[64];
    int nd = 0;
    for (int k = 1; k <= G && nd < 64; k++)
        if (G % k == 0) divs[nd++] = k;
    for (int tries = 0; tries < 30; tries++) {
        int k2 = divs[rnd(nd)];
        int M = G / k2;
        int r = 0;
        if (M == 1) {
            r = 0;
        } else if (k2 == 1) {
            r = 1;
        } else {
            int ok = 0;
            for (int t = 0; t < 300; t++) {
                int cand = 1 + rnd(M - 1);
                if (gcd_i(cand, M) == 1 && powmod_ll(cand, k2, M) == 1) {
                    r = cand;
                    ok = 1;
                    break;
                }
            }
            if (!ok) continue;
        }
        GG = G;
        MM = M;
        K2 = k2;
        pwv[0] = 1 % M;
        for (int b = 1; b < K2; b++) pwv[b] = (int)((long long)pwv[b - 1] * r % M);
        for (int x = 0; x < G; x++) {
            int a = x / k2, b = x % k2;
            for (int y = 0; y < G; y++) {
                int c = y / k2, e = y % k2;
                long long aa = ((long long)a + (long long)pwv[b] * c) % M;
                int bb = (b + e) % k2;
                mtbuf[x * G + y] = (int)(aa * k2 + bb);
            }
        }
        return 1;
    }
    return 0;
}

static void setup_base(int K) {
    KB = K;
    NN = 2 * K * GG;
    dN = DEG * K;
    for (int p = 0; p < DEG; p++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        shuffle_int(perm, K);
        for (int i = 0; i < K; i++) {
            int j = p * K + i;
            du[j] = i;
            dv[j] = K + perm[i];
            dg[j] = rnd(GG);
        }
    }
}

/* Lifted adjacency: vertex u*GG+x (u < KB left, u >= KB right); dart (a,b,g) joins (a,x)-(b,mt[x][g]). */
static void build_graph(void) {
    for (int v = 0; v < NN; v++) ldeg[v] = 0;
    for (int j = 0; j < dN; j++) {
        int a0 = du[j], b0 = dv[j], g = dg[j];
        for (int x = 0; x < GG; x++) {
            int a = a0 * GG + x;
            int b = b0 * GG + mtbuf[x * GG + g];
            int dup = 0;
            for (int i = 0; i < ldeg[a]; i++)
                if (ladj[a][i] == b) {
                    dup = 1;
                    break;
                }
            if (dup) continue;
            if (ldeg[a] >= MAXD || ldeg[b] >= MAXD) continue;
            ladj[a][ldeg[a]++] = b;
            ladj[b][ldeg[b]++] = a;
        }
    }
}

/* Number of unordered pairs at distance > DIAM. */
static long long eval_cost(void) {
    int W = (NN + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)NN * (size_t)W);
    for (int v = 0; v < NN; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < NN; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < ldeg[v]; i++) {
                uint64_t *t = cur + (size_t)ladj[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < NN; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += NN - cnt;
    }
    return bad / 2;
}

/* Simulated annealing on the dart voltages of the current base/group. Returns 1 on zero cost. */
static int run_attempt(long maxStall) {
    build_graph();
    long long cur = eval_cost();
    if (cur == 0) return 1;
    double T = 0.3 + 1.2 * rnd01();
    long long bestc = cur;
    long stall = 0;
    while (stall < maxStall) {
        if (cpu_now() - TSTART >= TL) return 0;
        int j = rnd(dN);
        int old = dg[j];
        int nw = rnd(GG - 1);
        if (nw >= old) nw++;
        dg[j] = nw;
        build_graph();
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
            if (cur == 0) return 1;
            if (cur < bestc) {
                bestc = cur;
                stall = 0;
            } else {
                stall++;
            }
        } else {
            dg[j] = old;
            stall++;
        }
    }
    return 0;
}

static void save_graph(void) {
    bestNE = 0;
    bestNN = NN;
    for (int v = 0; v < NN; v++)
        for (int i = 0; i < ldeg[v]; i++) {
            int w = ladj[v][i];
            if (v < w) {
                bestEu[bestNE] = v;
                bestEv[bestNE] = w;
                bestNE++;
            }
        }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time minN [kmax]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    int minN = atoi(argv[5]);
    KMAX = (argc >= 7) ? atoi(argv[6]) : 3;
    if (DEG < 2 || DEG > MAXD || DIAM < 1 || TL <= 0 || KMAX < 1) {
        printf("0 0\n");
        return 0;
    }
    if (KMAX > MAXK) KMAX = MAXK;
    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    TSTART = cpu_now();
    int bestN = minN;
    int have = 0;
    int span = 4;
    while (cpu_now() - TSTART < TL) {
        int K = 1 + rnd(KMAX);
        int G = bestN / (2 * K) + 1 + rnd(span + 1);
        if (G < 2) G = 2;
        if (G > MAXG || 2 * K * G > MAXN) {
            K = 1;
            G = bestN / 2 + 1 + rnd(span + 1);
            if (G < 2) G = 2;
            if (G > MAXG || 2 * G > MAXN) break;
        }
        if (!setup_group(G)) continue;
        setup_base(K);
        if (run_attempt(800)) {
            if (NN > bestN) {
                bestN = NN;
                save_graph();
                have = 1;
            }
            span = span * 2;
            if (span > 40) span = 40;
        } else {
            if (span > 1) span = span * 3 / 4;
            if (span < 1) span = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestNN, bestNE);
    for (int i = 0; i < bestNE; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: simulated annealing over bipartite graphs (grow-and-repair).
# Starts from a valid graph, grows by one vertex whenever the cost is zero.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define LOGMAX 1024

static int DEG, DIAM;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestNv;
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static uint64_t rs = 1;
static int defi[MAXN], fulli[MAXN], stk[MAXN];
static int logOp[LOGMAX], logA[LOGMAX], logB[LOGMAX], logN;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += nv - cnt;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void raw_del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void raw_add(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void raw_remove(int a, int b) {
    raw_del_half(a, b);
    raw_del_half(b, a);
}

static void log_push(int op, int a, int b) {
    if (logN < LOGMAX) {
        logOp[logN] = op;
        logA[logN] = a;
        logB[logN] = b;
        logN++;
    }
}

static void edit_remove(int a, int b) {
    raw_remove(a, b);
    log_push(0, a, b);
}

static void edit_add(int a, int b) {
    raw_add(a, b);
    log_push(1, a, b);
}

/* Undo the logged edits in reverse order, restoring the previous state. */
static void undo_log(void) {
    for (int i = logN - 1; i >= 0; i--) {
        if (logOp[i] == 0) raw_add(logA[i], logB[i]);
        else raw_remove(logA[i], logB[i]);
    }
    logN = 0;
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static int swap_move(void) {
    int a = rnd(nv);
    if (deg[a] == 0) return 0;
    int c = -1;
    for (int t = 0; t < 200; t++) {
        int x = rnd(nv);
        if (x != a && col[x] == col[a] && deg[x] > 0) {
            c = x;
            break;
        }
    }
    if (c < 0) return 0;
    int b = adjv[a][rnd(deg[a])];
    int e = adjv[c][rnd(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    logN = 0;
    edit_remove(a, b);
    edit_remove(c, e);
    edit_add(a, e);
    edit_add(c, b);
    return 1;
}

static int relocate_move(void) {
    int v = rnd(nv);
    int c = col[v];
    logN = 0;
    while (deg[v] > 0) edit_remove(v, adjv[v][deg[v] - 1]);
    int nd = 0, nf = 0;
    for (int w = 0; w < nv; w++) {
        if (w == v || col[w] == c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        edit_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        edit_remove(w, x);
        edit_add(v, w);
        k++;
    }
    return 1;
}

static void grow(void) {
    int c = rnd(2);
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    int nd = 0, nf = 0;
    for (int w = 0; w < v; w++) {
        if (col[w] != 1 - c) continue;
        if (deg[w] < DEG) defi[nd++] = w;
        else fulli[nf++] = w;
    }
    shuffle_int(defi, nd);
    shuffle_int(fulli, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        raw_add(v, defi[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = fulli[i];
        int x = adjv[w][rnd(deg[w])];
        raw_remove(w, x);
        raw_add(v, w);
        k++;
    }
}

static void save_best(void) {
    memcpy(bestAdj, adjv, sizeof adjv);
    memcpy(bestDeg, deg, sizeof deg);
    memcpy(bestCol, col, sizeof col);
    bestNv = nv;
}

static void restore_best(void) {
    memcpy(adjv, bestAdj, sizeof adjv);
    memcpy(deg, bestDeg, sizeof deg);
    memcpy(col, bestCol, sizeof col);
    nv = bestNv;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [stall]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long stallLim = 1500;
    if (argc >= 6) stallLim = atol(argv[5]);
    if (stallLim < 50) stallLim = 50;
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) { deg[i] = 0; col[i] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        raw_add(u, v);
    }
    if (nv == 0) {
        printf("0 0\n");
        return 0;
    }

    /* two-colour the start graph by DFS */
    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    long long cur_cost = eval_cost();
    save_best();
    int have_valid = (cur_cost == 0);
    double tstart = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;
    logN = 0;

    while (1) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
        if (frac >= 1.0) break;

        if (cur_cost == 0) {
            if (nv > bestNv || !have_valid) {
                save_best();
                have_valid = 1;
            }
            if (nv + 1 >= MAXN) break;
            grow();
            cur_cost = eval_cost();
            stall = 0;
            continue;
        }

        double T = 0.12 + 0.5 * (1.0 - frac);
        int ok = (rnd01() < 0.6) ? swap_move() : relocate_move();
        if (!ok) {
            logN = 0;
            continue;
        }
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur_cost);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur_cost = c2;
            logN = 0;
        } else {
            undo_log();
        }

        if (++stall > stallLim) {
            restore_best();
            logN = 0;
            for (int k = 0; k < 2; k++) relocate_move();
            logN = 0;
            cur_cost = eval_cost();
            stall = 0;
        }
    }

    if (cur_cost == 0 && (nv > bestNv || !have_valid)) save_best();

    long long em = 0;
    for (int v = 0; v < bestNv; v++) em += bestDeg[v];
    printf("%d %lld\n", bestNv, em / 2);
    for (int v = 0; v < bestNv; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = lib._bipartition(n, adj) if hasattr(lib, "_bipartition") else _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _run_lift(d, D, seed, budget, min_n, kmax=3):
    """Run the voltage-lift engine; return the parsed (n, edges), or (0, []) if nothing was found."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{budget:.2f}", min_n, kmax],
                    stdin_graph=None, timeout=budget + 6.0)
    return lib.parse_graph_text(out)


def _run_anneal(d, D, seed, graph, budget, stall=1500):
    """Run the annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3 (non-calibration): projective plane of the largest prime power q <= d - 1.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n1, e1 = lib.projective_plane_incidence(q)
                consider(n1, e1)
                break

    # D >= 4: generalized quadrangle W(q) as a seed.
    gq = None
    if D >= 4 and tl >= 12:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Target path (D >= 4, d >= 5): voltage-lift search over semidirect products,
    # then annealing from the best valid graph.
    if D >= 4 and d >= 5 and tl >= 12:
        end = start + 0.85 * tl - 2.0
        if gq is not None:
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(sat[0], sat[1])

        now = time.monotonic()
        lift_end = now + 0.45 * (end - now)
        budget = lift_end - now - 1.5
        if budget >= 2.0:
            try:
                n2, e2 = _run_lift(d, D, seed, budget, best_n, 3)
                consider(n2, e2)
            except Exception:
                pass

        remaining = end - time.monotonic() - 1.0
        if remaining >= 2.0:
            try:
                n3, e3 = _run_anneal(d, D, seed + 1, best, remaining)
                consider(n3, e3)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
