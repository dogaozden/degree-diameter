"""Targets (D >= 4): Gen. quadrangle start, then a new search that builds voltage lifts
of small bipartite base graphs over semidirect products Z_m x| Z_k, annealing the
voltages in C. A lift that already has diameter <= D is a new start for the
parent's annealer (C_SOURCE below), which adds vertices while it can.

Fallbacks: K_{d,d}, the projective plane (D = 3), and the GQ incidence graph
saturated with spare degree. Every candidate goes through lib.is_valid before
it is kept.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing over bipartite graphs (grow-when-valid).
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
static int stampArr[MAXN], distArr[MAXN], qbuf[MAXN];
static int stampCur = 0;

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

static int targeted_move(void) {
    int v = rnd(nv);
    if (deg[v] == 0) return 0;
    stampCur++;
    int qh = 0, qt = 0;
    qbuf[qt++] = v;
    stampArr[v] = stampCur;
    distArr[v] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        if (distArr[u] >= DIAM) continue;
        for (int i = 0; i < deg[u]; i++) {
            int x = adjv[u][i];
            if (stampArr[x] != stampCur) {
                stampArr[x] = stampCur;
                distArr[x] = distArr[u] + 1;
                qbuf[qt++] = x;
            }
        }
    }
    int cnt = 0, w = -1;
    for (int x = 0; x < nv; x++) {
        if (col[x] != col[v] || stampArr[x] == stampCur) continue;
        cnt++;
        if (rnd(cnt) == 0) w = x;
    }
    if (w < 0 || deg[w] == 0) return 0;
    int a = adjv[v][rnd(deg[v])];
    int e = adjv[w][rnd(deg[w])];
    if (a == e) return 0;
    if (has_edge(v, e) || has_edge(w, a)) return 0;
    logN = 0;
    edit_remove(v, a);
    edit_remove(w, e);
    edit_add(v, e);
    edit_add(w, a);
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
        double pm = rnd01();
        int ok;
        if (pm < 0.30) ok = swap_move();
        else if (pm < 0.70) ok = targeted_move();
        else ok = relocate_move();
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
# C engine 2 (new): anneal the voltages of a d-regular lift over a finite group.
#
# Base: K vertices on side A and K on side B. Dart t of A-vertex i goes to
# B-vertex perm[t][i] with voltage volt[i][t] in G = Z_GM x| Z_GK.
# Lift: (i, x) ~ (K + j, x * g). Duplicate lifted edges are dropped from the
# output and penalised in the cost. Cost = 2 * (bad pairs) + duplicates.
# Output: the first lift with diameter <= DIAM, as "NV E" plus edges, or "0 0".
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4608
#define WMAX ((MAXV + 63) / 64)
#define MAXD 16
#define MAXK 64
#define MAXGK 64

static int DEGR, DIAM, K, GM, GK, G, NV;
static int pw[MAXGK];
static int perm[MAXD][MAXK];
static int volt[MAXK][MAXD];
static int nbr[MAXV][MAXD];
static int ncnt[MAXV];
static uint64_t RA[MAXV * WMAX];
static uint64_t RB[MAXV * WMAX];
static uint64_t rs = 1;
static int lastBad, lastDup;

typedef struct { int p[MAXD][MAXK]; int v[MAXK][MAXD]; } St;
static St bestS, bakS;

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

static void save_state(St *s) {
    memcpy(s->p, perm, sizeof perm);
    memcpy(s->v, volt, sizeof volt);
}

static void load_state(const St *s) {
    memcpy(perm, s->p, sizeof perm);
    memcpy(volt, s->v, sizeof volt);
}

/* Semidirect product Z_GM x| Z_GK, element a*GK + b, (a,b)*(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, d = y % GK;
    long long t = (long long)a + (long long)pw[b] * (long long)c;
    return (int)(t % GM) * GK + (b + d) % GK;
}

static void build(void) {
    lastDup = 0;
    for (int v = 0; v < NV; v++) ncnt[v] = 0;
    for (int i = 0; i < K; i++) {
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int t = 0; t < DEGR; t++) {
                int j = perm[t][i];
                int y = gmul(x, volt[i][t]);
                int w = (K + j) * G + y;
                int seen = 0;
                for (int q = 0; q < ncnt[v]; q++)
                    if (nbr[v][q] == w) { seen = 1; break; }
                if (seen || ncnt[w] >= DEGR) {
                    lastDup++;
                    continue;
                }
                nbr[v][ncnt[v]++] = w;
                nbr[w][ncnt[w]++] = v;
            }
        }
    }
}

static int evalcost(void) {
    build();
    int W = (NV + 63) >> 6;
    uint64_t *cu = RA, *nx = RB, *tm;
    memset(RA, 0, sizeof(uint64_t) * (size_t)NV * (size_t)W);
    for (int v = 0; v < NV; v++)
        cu[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nx + (size_t)v * W;
            memcpy(o, cu + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < ncnt[v]; i++) {
                uint64_t *s = cu + (size_t)nbr[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        tm = cu;
        cu = nx;
        nx = tm;
    }
    long long bad = 0;
    for (int v = 0; v < NV; v++) {
        uint64_t *s = cu + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(s[w]);
        bad += NV - c;
    }
    lastBad = (int)(bad / 2);
    return 2 * lastBad + lastDup;
}

static void print_graph(void) {
    long long m = 0;
    for (int v = 0; v < K * G; v++) m += ncnt[v];
    printf("%d %lld\n", NV, m);
    for (int v = 0; v < K * G; v++)
        for (int i = 0; i < ncnt[v]; i++)
            printf("%d %d\n", v, nbr[v][i]);
}

static void init_state(void) {
    for (int t = 0; t < DEGR; t++) {
        for (int i = 0; i < K; i++) perm[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int x = perm[t][i];
            perm[t][i] = perm[t][j];
            perm[t][j] = x;
        }
    }
    for (int i = 0; i < K; i++)
        for (int t = 0; t < DEGR; t++)
            volt[i][t] = rnd(G);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEGR = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    GM = atoi(argv[6]);
    GK = atoi(argv[7]);
    int r = argc > 8 ? atoi(argv[8]) : 1;
    if (DEGR < 1 || DEGR > MAXD || DIAM < 1 || K < 1 || K > MAXK ||
        GM < 1 || GK < 1 || GK > MAXGK || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = GM * GK;
    NV = 2 * K * G;
    if (NV > MAXV) {
        printf("0 0\n");
        return 0;
    }
    if (r < 0) r = 0;
    r %= GM;
    pw[0] = 1 % GM;
    for (int b = 1; b < GK; b++) pw[b] = (int)((long long)pw[b - 1] * r % GM);

    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    init_state();
    int cost = evalcost();
    if (lastBad == 0) {
        print_graph();
        return 0;
    }
    int bestCost = cost;
    save_state(&bestS);
    clock_t c0 = clock();
    long stall = 0;
    const long stallLim = 800;

    while (1) {
        double frac = (double)(clock() - c0) / CLOCKS_PER_SEC / tl;
        if (frac >= 1.0) break;
        save_state(&bakS);
        double T = 2.0 * (1.0 - frac) + 0.2;
        if (K >= 2 && rnd01() < 0.12) {
            int t = rnd(DEGR), a = rnd(K), b = rnd(K);
            int tmp = perm[t][a];
            perm[t][a] = perm[t][b];
            perm[t][b] = tmp;
        } else {
            int i = rnd(K), t = rnd(DEGR);
            volt[i][t] = rnd(G);
        }
        int c2 = evalcost();
        if (lastBad == 0) {
            print_graph();
            return 0;
        }
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < bestCost) {
                bestCost = cost;
                save_state(&bestS);
                stall = 0;
            } else {
                stall++;
            }
        } else {
            load_state(&bakS);
            stall++;
        }
        if (stall > stallLim) {
            load_state(&bestS);
            for (int k = 0; k < 3; k++) {
                int i = rnd(K), t = rnd(DEGR);
                volt[i][t] = rnd(G);
            }
            cost = evalcost();
            if (lastBad == 0) {
                print_graph();
                return 0;
            }
            stall = 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

# Target orders to aim for (beat the record) in specific cases.
RECORD_AIM = {(11, 4): 1736}


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
    color = _bipartition(n, adj)
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


def _lift_config(target_n, rng):
    """Random (K, GM, GK, r) so that the lift has order 2*K*G >= target_n, with G = GM*GK."""
    K = rng.choice([1, 1, 2, 2, 3, 4, 6, 8, 11, 12])
    G = -(-target_n // (2 * K)) + rng.randint(0, 2)
    divs = [g for g in range(1, min(G, 24) + 1) if G % g == 0]
    GK = rng.choice(divs)
    GM = G // GK
    if GM == 1:
        return K, 1, GK, 0
    if GK == 1:
        return K, GM, 1, 1
    pool = list(range(1, GM))
    rng.shuffle(pool)
    for r in pool[:80]:
        if math.gcd(r, GM) == 1 and pow(r, GK, GM) == 1 % GM:
            return K, GM, GK, r
    return K, G, 1, 1  # cyclic fallback of the same order


def _run_lift(d, D, seed, K, GM, GK, r, budget):
    """Run the voltage annealer for one group configuration; return parsed (n, edges)."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{budget:.2f}", K, GM, GK, r],
                    timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def _run_c(d, D, seed, graph, budget, stall=1500):
    """Run the C annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

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

    sat = None

    if D == 3 and d >= 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            pg_n, pg_e = lib.projective_plane_incidence(qs[0])
            consider(pg_n, pg_e)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat_e = _saturate_edges(gq[0], gq[1], d, rng)
            sat = (gq[0], sat_e)
            consider(sat[0], sat[1])

    # New engine: voltage lifts over semidirect products, annealed in C.
    if D >= 4 and d >= 3:
        lift_end = start + 0.60 * tl
        aim = RECORD_AIM.get((d, D), 0)
        attempt = 0
        while time.monotonic() < lift_end - 1.0:
            budget = min(6.0, lift_end - time.monotonic())
            if rng.random() < 0.5:
                target = best_n + 2
            else:
                target = max(best_n + 2, aim)
            K, GM, GK, r = _lift_config(target, rng)
            try:
                n2, e2 = _run_lift(d, D, seed * 7919 + attempt, K, GM, GK, r, budget)
                consider(n2, e2)
            except Exception:
                pass
            attempt += 1

    # Parent annealer: grow the best valid graph (and the saturated GQ for diversity).
    if D >= 3 and d >= 3:
        end = start + 0.92 * tl - 1.5
        starts = [best]
        if sat is not None:
            starts.append(sat)
        for idx, g in enumerate(starts):
            remaining = end - time.monotonic()
            if remaining < 2.0:
                break
            share = 0.7 if (idx == 0 and len(starts) > 1) else 1.0
            try:
                n2, e2 = _run_c(d, D, seed + idx, g, remaining * share)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
