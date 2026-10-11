import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine 1: simulated annealing over bipartite graphs with three moves.
# Used by the vertex-extension and annealing phases (parent engine, unchanged).
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

static void vertex_replace_kick(void) {
    if (nv < 3) return;
    int v = rnd(nv);
    while (deg[v] > 0) raw_remove(v, adjv[v][deg[v] - 1]);
    int L = nv - 1;
    if (v != L) {
        for (int i = 0; i < deg[L]; i++) {
            int w = adjv[L][i];
            for (int j = 0; j < deg[w]; j++)
                if (adjv[w][j] == L) adjv[w][j] = v;
        }
        memcpy(adjv[v], adjv[L], sizeof(int) * DEGMAX);
        deg[v] = deg[L];
        col[v] = col[L];
        deg[L] = 0;
    }
    nv--;
    grow();
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
        if (pm < 0.35) ok = swap_move();
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
            if (rnd01() < 0.5) {
                vertex_replace_kick();
            } else {
                for (int k = 0; k < 2; k++) relocate_move();
            }
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
# C search engine 2 (new, bold): annealing over voltage lifts of a small
# bipartite base graph with d darts per base vertex, over a semidirect product
# Z_m x| Z_k2 (element code a*k2+b). The lift has 2*k*G vertices; its cost is
# the number of vertex pairs at distance > D. Moves: change one voltage, or swap
# the endpoints of two darts (keeps the base d-regular). Returns the first lift
# with cost 0, or "0 0".
#
# Input (stdin, via lib.graph_to_text): "k m_edges" then pairs:
#   pair 0 = (d, m), pair 1 = (k2, r), pair 2+a = (from_a, to_a * G + g_a).
# Args: D seed time_limit.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4400
#define MAXW 70
#define MAXDART 1200
#define MAXDEG 16
#define MAXK 16

static int K, DEG, MM, K2, DIAM, G, NV, W, NDART;
static int dfrom[MAXDART], dto[MAXDART], dg[MAXDART];
static int rpow[32];
static int adj[MAXV * MAXDEG];
static int acnt[MAXV];
static uint64_t BUFA[MAXV * MAXW];
static uint64_t BUFB[MAXV * MAXW];
static uint64_t rs = 1;
static int mv_idx[2], mv_to[2], mv_g[2], mv_n;

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

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, d = y % K2;
    return ((a + rpow[b] * c) % MM) * K2 + (b + d) % K2;
}

/* Dart a joins side-0 vertex (from, x) to side-1 vertex (to, x*g) for all x. */
static int build_adj(void) {
    for (int v = 0; v < NV; v++) acnt[v] = 0;
    for (int a = 0; a < NDART; a++) {
        int i = dfrom[a], j = dto[a], g = dg[a];
        for (int x = 0; x < G; x++) {
            int u = i * G + x;
            int w = (K + j) * G + gmul(x, g);
            if (acnt[u] >= DEG || acnt[w] >= DEG) return 0;
            adj[u * DEG + acnt[u]++] = w;
            adj[w * DEG + acnt[w]++] = u;
        }
    }
    return 1;
}

static long eval_cost(void) {
    if (!build_adj()) return 1L << 40;
    uint64_t *cur = BUFA, *nxt = BUFB, *tmp;
    memset(BUFA, 0, sizeof(uint64_t) * (size_t)NV * W);
    for (int v = 0; v < NV; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < NV; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int t = 0; t < acnt[v]; t++) {
                const uint64_t *s = cur + (size_t)adj[v * DEG + t] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < NV; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(s[w]);
        bad += NV - c;
    }
    return bad / 2;
}

/* True if some dart other than idx has the triple (f, t, g). */
static int dup_check(int idx, int f, int t, int g) {
    for (int b = 0; b < NDART; b++)
        if (b != idx && dfrom[b] == f && dto[b] == t && dg[b] == g) return 1;
    return 0;
}

static void randomize(void) {
    for (int a = 0; a < NDART; a++) {
        for (int t = 0; t < 60; t++) {
            int ng = rnd(G);
            if (!dup_check(a, dfrom[a], dto[a], ng)) {
                dg[a] = ng;
                break;
            }
        }
    }
}

static int do_move(void) {
    mv_n = 0;
    if (rnd(2) == 0) {
        int a = rnd(NDART);
        int ng = rnd(G);
        if (ng == dg[a]) return 0;
        if (dup_check(a, dfrom[a], dto[a], ng)) return 0;
        mv_idx[0] = a;
        mv_to[0] = dto[a];
        mv_g[0] = dg[a];
        mv_n = 1;
        dg[a] = ng;
        return 1;
    } else {
        int a = rnd(NDART), b = rnd(NDART);
        if (a == b || dto[a] == dto[b]) return 0;
        if (dup_check(a, dfrom[a], dto[b], dg[a])) return 0;
        if (dup_check(b, dfrom[b], dto[a], dg[b])) return 0;
        mv_idx[0] = a;
        mv_to[0] = dto[a];
        mv_g[0] = dg[a];
        mv_idx[1] = b;
        mv_to[1] = dto[b];
        mv_g[1] = dg[b];
        mv_n = 2;
        int ta = dto[a];
        dto[a] = dto[b];
        dto[b] = ta;
        return 1;
    }
}

static void undo_move(void) {
    for (int q = mv_n - 1; q >= 0; q--) {
        int a = mv_idx[q];
        dto[a] = mv_to[q];
        dg[a] = mv_g[q];
    }
}

int main(int argc, char **argv) {
    if (argc < 4) {
        printf("0 0\n");
        return 0;
    }
    DIAM = atoi(argv[1]);
    unsigned long long seed = strtoull(argv[2], NULL, 10);
    double tl = atof(argv[3]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    int n = 0, cnt = 0;
    static int P[2 * (MAXDART + 2)];
    if (scanf("%d %d", &n, &cnt) != 2 || cnt < 2 || cnt > MAXDART + 2) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < 2 * cnt; i++)
        if (scanf("%d", &P[i]) != 1) {
            printf("0 0\n");
            return 0;
        }
    DEG = P[0];
    MM = P[1];
    K2 = P[2];
    int RR = P[3];
    K = n;
    NDART = cnt - 2;
    if (K < 1 || K > MAXK || DEG < 1 || DEG > MAXDEG || MM < 1 || K2 < 1 || K2 > 31 ||
        DIAM < 1 || NDART != K * DEG) {
        printf("0 0\n");
        return 0;
    }
    G = MM * K2;
    NV = 2 * K * G;
    if (NV > MAXV || NV < 2) {
        printf("0 0\n");
        return 0;
    }
    W = (NV + 63) / 64;
    int rr = ((RR % MM) + MM) % MM;
    rpow[0] = 1 % MM;
    for (int b = 1; b < K2; b++) rpow[b] = (int)((long)rpow[b - 1] * rr % MM);

    for (int a = 0; a < NDART; a++) {
        int i = P[2 * (a + 2)], code = P[2 * (a + 2) + 1];
        if (code < 0) {
            printf("0 0\n");
            return 0;
        }
        int j = code / G, g = code % G;
        if (i < 0 || i >= K || j >= K) {
            printf("0 0\n");
            return 0;
        }
        dfrom[a] = i;
        dto[a] = j;
        dg[a] = g;
    }

    double tstart = (double)clock() / CLOCKS_PER_SEC;
    long cost = eval_cost();
    long best = cost, since = 0;
    while (cost > 0) {
        double el = (double)clock() / CLOCKS_PER_SEC - tstart;
        if (el >= tl) break;
        double frac = el / tl;
        double T = 0.25 + 2.5 * (1.0 - frac);
        if (!do_move()) continue;
        long c2 = eval_cost();
        double dl = (double)(c2 - cost);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cost = c2;
        } else {
            undo_move();
        }
        if (cost < best) {
            best = cost;
            since = 0;
        } else {
            since++;
        }
        if (since > 3000) {
            randomize();
            cost = eval_cost();
            best = cost;
            since = 0;
        }
    }

    if (cost == 0 && eval_cost() == 0) {
        long m2 = 0;
        for (int v = 0; v < NV; v++) m2 += acnt[v];
        printf("%d %ld\n", NV, m2 / 2);
        for (int v = 0; v < NV; v++)
            for (int t = 0; t < acnt[v]; t++) {
                int w = adj[v * DEG + t];
                if (v < w) printf("%d %d\n", v, w);
            }
    } else {
        printf("0 0\n");
    }
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


# ----------------------------------------------------------------------------
# Twin extension: a twin v of x (same side, N(v) = N(x)) keeps old distances,
# has dist(v, x) = 2, and preserves bipartiteness.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


# ----------------------------------------------------------------------------
# Cover-based vertex extension.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


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


def _cand_matrix(cand_balls, n):
    """Boolean matrix M[i, w] = 1 iff vertex w lies in the ball of candidate i."""
    nb = (n + 7) // 8
    buf = b"".join(x.to_bytes(nb, "little") for x in cand_balls)
    arr = np.frombuffer(buf, dtype=np.uint8).reshape(len(cand_balls), nb)
    return np.unpackbits(arr, axis=1, bitorder="little")[:, :n].astype(bool)


def _weighted_cover(B, cand_ids, n, d, nrng, randomize):
    """Hardest-first weighted set cover: rare uncovered vertices weigh more."""
    k = B.shape[0]
    uncov = np.ones(n, dtype=bool)
    avail = np.ones(k, dtype=bool)
    chosen = []
    for _ in range(d):
        if not uncov.any():
            break
        sub = B[:, uncov]
        cnt = sub.sum(axis=0)
        if (cnt == 0).any():
            return None
        w = 1.0 / cnt
        score = sub.astype(np.float64) @ w
        if randomize:
            score = score * (1.0 + 0.08 * nrng.random(k))
        score[~avail] = -1.0
        i = int(np.argmax(score))
        if score[i] <= 0:
            break
        avail[i] = False
        chosen.append(cand_ids[i])
        uncov &= ~B[i]
    return chosen if not uncov.any() else None


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _local_cover(cands, ball, full, d, rng, iters, deadline):
    """Plateau-walking swap search for a cover of `full` by at most d candidates."""
    pool = list(cands)
    if not pool:
        return None
    k = min(d, len(pool))
    chosen = rng.sample(pool, k)
    union = 0
    for s in chosen:
        union |= ball[s]
    if union == full:
        return chosen
    score = union.bit_count()
    for _ in range(iters):
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        s = rng.choice(pool)
        if s in chosen:
            continue
        trial = chosen[:]
        trial[i] = s
        u = 0
        for t in trial:
            u |= ball[t]
        sc = u.bit_count()
        if sc >= score:
            chosen, score = trial, sc
            if u == full:
                return chosen
    return None


def _find_cover(cands, ball, n, full, d, rng, deadline):
    """Try weighted covers, then greedy, then swap search."""
    B = _cand_matrix([ball[s] for s in cands], n)
    nrng = np.random.default_rng(rng.randrange(1 << 30))
    for attempt in range(12):
        if time.monotonic() >= deadline:
            return None
        chosen = _weighted_cover(B, cands, n, d, nrng, attempt > 0)
        if chosen:
            return chosen
    for attempt in range(60):
        if time.monotonic() >= deadline:
            return None
        chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if chosen:
            return chosen
    if time.monotonic() < deadline:
        return _local_cover(cands, ball, full, d, rng, 400, deadline)
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = _find_cover(cands, ball, n, full, d, rng, deadline)
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


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


# ----------------------------------------------------------------------------
# BFS-verified vertex insertion with neighbourhood hill-climbing.
# ----------------------------------------------------------------------------

def _multi_ball(adj, S, r, n):
    """Number of vertices within distance r of the source set S."""
    seen = bytearray(n)
    frontier = []
    for s in S:
        if not seen[s]:
            seen[s] = 1
            frontier.append(s)
    cnt = len(frontier)
    for _ in range(r):
        if not frontier:
            break
        nxt = []
        for u in frontier:
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = 1
                    nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _insert_search(n, adj, deg, color, d, D, rng, iters, deadline):
    """Find (colour, neighbour set) for a new vertex whose D-ball covers all n vertices, or None."""
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
        if not cands:
            continue
        k = min(d, len(cands))
        S = rng.sample(cands, k)
        best = _multi_ball(adj, S, D - 1, n)
        for _ in range(iters):
            if best >= n:
                return c, S
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(k)
            s = rng.choice(cands)
            if s in S:
                continue
            T = S[:]
            T[i] = s
            val = _multi_ball(adj, T, D - 1, n)
            if val >= best:
                S, best = T, val
        if best >= n:
            return c, S
    return None


def _insert_grow(n, edges, d, D, deadline, rng):
    """Repeatedly insert BFS-verified vertices until the deadline or repeated failure."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    fails = 0
    while time.monotonic() < deadline and fails < 25:
        res = _insert_search(n, adj, deg, color, d, D, rng, 80, deadline)
        if res is None:
            fails += 1
            continue
        c, S = res
        v = n
        n += 1
        color.append(c)
        adj.append(list(S))
        deg.append(len(S))
        for s in S:
            adj[s].append(v)
            deg[s] += 1
            edges.append((s, v))
        fails = 0
    return n, edges


# ----------------------------------------------------------------------------
# Pipeline helpers.
# ----------------------------------------------------------------------------

def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Bold new search: voltage lifts over semidirect products, annealed in C.
# ----------------------------------------------------------------------------

def _sample_params(G, rng):
    """Return (m, k2, r) with G = m * k2 and Z_m x|_r Z_k2 a group, or None."""
    opts = [1, 1, 2, 3, 4, 5, 6, 8, 10, 12]
    for _ in range(40):
        k2 = rng.choice(opts)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            return m, 1, 1
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 120))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def _random_base(k, d, G, rng):
    """Random d-regular bipartite base on k + k vertices as darts (i, j, g), all triples distinct."""
    darts, seen = [], set()
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            j = perm[i]
            g = rng.randrange(G)
            while (i, j, g) in seen:
                g = rng.randrange(G)
            seen.add((i, j, g))
            darts.append((i, j, g))
    return darts


def _run_lift(d, D, seed, k, m, k2, r, darts, budget):
    """Anneal voltages of the lift in C; return (n, edges) or (0, []) if none found."""
    G = m * k2
    # Encode the lift as an edge list: header pairs (d, m), (k2, r), then darts (i, j*G + g).
    edges = [(d, m), (k2, r)] + [(i, j * G + g) for i, j, g in darts]
    out = lib.run_c(C_LIFT, [D, seed, f"{budget:.2f}"], stdin_graph=(k, edges),
                    timeout=budget + 4.0)
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

    use_c = D >= 4 and d >= 5
    pipe_end = start + 0.20 * tl
    lift_end = start + (0.70 if use_c else 0.85) * tl

    # Structured starting graphs: W(q) for D = 4, projective plane for D = 3.
    sat = None
    src_list = []
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(sat[0], sat[1])
            src_list = [gq, sat]
    elif D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            pg = lib.projective_plane_incidence(qs[0])
            consider(pg[0], pg[1])
            src_list = [pg]

    # Growth pipeline on the structured graphs.
    if src_list:
        first = True
        while time.monotonic() < pipe_end:
            src = src_list[0] if first else rng.choice(src_list + [best])
            first = False
            pn, pe = _pipeline(src[0], src[1], d, D, pipe_end, rng)
            consider(pn, pe)

    # Bold phase: voltage lifts over semidirect products, annealed in C.
    # Each attempt targets an order 2*k*G strictly above the current best.
    k_opts = [1, 1, 2, 2, 3, 4]
    attempt = 0
    while time.monotonic() < lift_end - 0.5:
        attempt += 1
        k = rng.choice(k_opts)
        G = max(d, best_n // (2 * k) + 1 + rng.randrange(0, 3))
        prm = _sample_params(G, rng)
        if prm is None:
            continue
        mm, k2, rr = prm
        darts = _random_base(k, d, mm * k2, rng)
        budget = min(lift_end - time.monotonic(), max(1.0, 0.05 * tl))
        if budget < 0.5:
            break
        try:
            n2, e2 = _run_lift(d, D, seed * 1000 + attempt, k, mm, k2, rr, darts, budget)
            consider(n2, e2)
        except Exception:
            pass

    # Annealing schedule (D >= 4, d >= 5), starting from the best valid graph:
    #   1. anneal from the best graph,
    #   2. BFS-verified insertion on the result,
    #   3. anneal again from the best graph,
    #   4. anneal from the saturated quadrangle with whatever time remains.
    if use_c:
        end = start + 0.92 * tl - 1.5

        def remaining():
            return end - time.monotonic()

        if remaining() >= 2.0:
            try:
                n2, e2 = _run_c(d, D, seed, best, remaining() * 0.5)
                consider(n2, e2)
            except Exception:
                pass

        if remaining() >= 3.0:
            try:
                ins_end = min(end, time.monotonic() + 0.08 * tl)
                gn, ge = _insert_grow(best_n, best[1], d, D, ins_end, rng)
                consider(gn, ge)
            except Exception:
                pass

        if remaining() >= 2.0:
            try:
                n2, e2 = _run_c(d, D, seed + 1, best, remaining() * 0.6)
                consider(n2, e2)
            except Exception:
                pass

        if sat is not None and remaining() >= 2.0:
            try:
                n2, e2 = _run_c(d, D, seed + 2, sat, remaining())
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
