import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy for the weakest parent case (d >= 5, D >= 4):
#
#   1. Fallback: the generalized quadrangle incidence graph W(q) (degree q+1,
#      diameter 4) and a saturated copy with spare degree filled. Always valid.
#   2. NEW construction, searched in C (HAAR_SOURCE): bipartite Haar graphs over
#      finite groups G of order g. Vertices a_x, b_x (x in G); a_x ~ b_{x*s} for
#      s in S, |S| = d. Left multiplication is an automorphism, so diameter <= D
#      reduces to two BFS runs (from a_1 and from b_1). Cost = number of unreached
#      (vertex, root) pairs. Groups are semidirect products Z_m x| Z_k (all
#      admissible r) and Z_p^2 x| Z_3 (companion matrix of x^2+x+1). The search
#      climbs g upward and keeps the largest order for which a zero-cost S exists.
#      Order g gives 2g vertices, so a success at g = 867 matches the record 1734.
#   3. Growth: the bit-parallel annealer (ANNEAL_SOURCE) starts from the best valid
#      graph and tries to add vertices while keeping diameter <= D.
#
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

HAAR_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXG 1100
#define MAXD 32
#define MAXGL 4096

typedef struct { int type, m, k, r, p; } GDesc;

static int DEG, DIAM, GG;
static int curType, curM, curK, curR, curP;
static int pw[MAXG];
static int Am[3][2][2];
static int MT[MAXG * MAXG];
static int INV[MAXG];
static int S[MAXD], iS[MAXD];
static unsigned char inS[MAXG];
static unsigned char ra[MAXG], rb[MAXG];
static int fa[MAXG], fb[MAXG];
static GDesc glist[MAXGL];
static double tlim;
static uint64_t rs = 1;

static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nxt() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0);
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod_i(int b, int e, int m) {
    int r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = (int)((long long)r * b % m);
        b = (int)((long long)b * b % m);
        e >>= 1;
    }
    return r;
}

static int isqrt_i(int x) {
    int r = 0;
    while ((r + 1) * (r + 1) <= x) r++;
    return r;
}

static int is_prime_i(int x) {
    if (x < 2) return 0;
    for (int i = 2; i * i <= x; i++)
        if (x % i == 0) return 0;
    return 1;
}

/* Type 0: Z_m x| Z_k, element (a,b) coded a*k+b, (a,b)(c,d) = (a + r^b c, b + d). */
static void set_type0(int m, int k, int r) {
    curType = 0;
    curM = m;
    curK = k;
    curR = r;
    GG = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
}

/* Type 1: Z_p^2 x| Z_3, element (v, j) coded (v0*p+v1)*3 + j,
   (v,j)(w,l) = (v + A^j w, j + l) with A the companion matrix of x^2+x+1. */
static void set_type1(int p) {
    int A1[2][2], i, j, kk;
    curType = 1;
    curP = p;
    GG = 3 * p * p;
    A1[0][0] = 0;
    A1[0][1] = p - 1;
    A1[1][0] = 1;
    A1[1][1] = p - 1;
    Am[0][0][0] = 1; Am[0][0][1] = 0; Am[0][1][0] = 0; Am[0][1][1] = 1;
    for (i = 0; i < 2; i++)
        for (j = 0; j < 2; j++) {
            Am[1][i][j] = A1[i][j];
            int s = 0;
            for (kk = 0; kk < 2; kk++) s += A1[i][kk] * A1[kk][j];
            Am[2][i][j] = s % p;
        }
}

static int mulf(int x, int y) {
    if (curType == 0) {
        int k = curK, m = curM;
        int a = x / k, b = x % k, c = y / k, d = y % k;
        int v = (a + pw[b] * c) % m;
        return v * k + (b + d) % k;
    } else {
        int p = curP, t = 3;
        int j = x % t, idx = x / t;
        int v0 = idx / p, v1 = idx % p;
        int l = y % t, jdx = y / t;
        int w0 = jdx / p, w1 = jdx % p;
        int u0 = (v0 + Am[j][0][0] * w0 + Am[j][0][1] * w1) % p;
        int u1 = (v1 + Am[j][1][0] * w0 + Am[j][1][1] * w1) % p;
        return (u0 * p + u1) * t + (j + l) % t;
    }
}

static void build_table(void) {
    int x, y;
    for (x = 0; x < GG; x++)
        for (y = 0; y < GG; y++) MT[x * GG + y] = mulf(x, y);
    for (x = 0; x < GG; x++) {
        INV[x] = -1;
        for (y = 0; y < GG; y++)
            if (MT[x * GG + y] == 0) {
                INV[x] = y;
                break;
            }
    }
}

static int build_groups(int G) {
    int cnt = 0;
    for (int k = 1; k <= G; k++) {
        if (G % k) continue;
        int m = G / k;
        if (k == 1) {
            if (cnt < MAXGL) {
                glist[cnt].type = 0;
                glist[cnt].m = m;
                glist[cnt].k = 1;
                glist[cnt].r = 1;
                glist[cnt].p = 0;
                cnt++;
            }
            continue;
        }
        if (m < 2) continue;
        for (int r = 1; r < m && cnt < MAXGL; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_i(r, k, m) != 1 % m) continue;
            glist[cnt].type = 0;
            glist[cnt].m = m;
            glist[cnt].k = k;
            glist[cnt].r = r;
            glist[cnt].p = 0;
            cnt++;
        }
    }
    if (G % 3 == 0) {
        int q = G / 3;
        int p = isqrt_i(q);
        if (p * p == q && p != 3 && is_prime_i(p) && cnt < MAXGL) {
            glist[cnt].type = 1;
            glist[cnt].m = 0;
            glist[cnt].k = 3;
            glist[cnt].r = 0;
            glist[cnt].p = p;
            cnt++;
        }
    }
    return cnt;
}

/* BFS from a_1 (startB = 0) or b_1 (startB = 1), counting reached a- and b-vertices.
   Edges: a_x ~ b_{x*s} (s in S), so a -> b uses x*s and b -> a uses y*s^{-1}. */
static void bfs(int startB, int *outA, int *outB) {
    int cntA = 0, cntB = 0, nfa = 0, nfb = 0, t, i, j, cnt;
    memset(ra, 0, (size_t)GG);
    memset(rb, 0, (size_t)GG);
    if (!startB) {
        ra[0] = 1;
        fa[0] = 0;
        nfa = 1;
        cntA = 1;
    } else {
        rb[0] = 1;
        fb[0] = 0;
        nfb = 1;
        cntB = 1;
    }
    for (t = 1; t <= DIAM; t++) {
        cnt = 0;
        if ((t + startB) & 1) {
            for (i = 0; i < nfa; i++) {
                int x = fa[i];
                for (j = 0; j < DEG; j++) {
                    int y = MT[x * GG + S[j]];
                    if (!rb[y]) {
                        rb[y] = 1;
                        fb[cnt++] = y;
                        cntB++;
                    }
                }
            }
            nfb = cnt;
        } else {
            for (i = 0; i < nfb; i++) {
                int y = fb[i];
                for (j = 0; j < DEG; j++) {
                    int x = MT[y * GG + iS[j]];
                    if (!ra[x]) {
                        ra[x] = 1;
                        fa[cnt++] = x;
                        cntA++;
                    }
                }
            }
            nfa = cnt;
        }
    }
    *outA = cntA;
    *outB = cntB;
}

static int cost_fn(void) {
    int a0, b0, a1, b1;
    bfs(0, &a0, &b0);
    bfs(1, &a1, &b1);
    return (GG - a0) + (GG - b0) + (GG - b1);
}

static int climb(int iters) {
    int c, it, j, v, old, c2;
    memset(inS, 0, (size_t)GG);
    for (j = 0; j < DEG; j++) {
        do {
            v = rnd(GG);
        } while (inS[v]);
        inS[v] = 1;
        S[j] = v;
        iS[j] = INV[v];
    }
    c = cost_fn();
    for (it = 0; it < iters && c > 0; it++) {
        if ((it & 63) == 0 && now_s() > tlim) break;
        j = rnd(DEG);
        do {
            v = rnd(GG);
        } while (inS[v]);
        old = S[j];
        inS[old] = 0;
        inS[v] = 1;
        S[j] = v;
        iS[j] = INV[v];
        c2 = cost_fn();
        if (c2 <= c || rnd01() < 0.01) {
            c = c2;
        } else {
            inS[v] = 0;
            inS[old] = 1;
            S[j] = old;
            iS[j] = INV[old];
        }
    }
    return c;
}

static void apply_desc(GDesc g) {
    if (g.type == 0) set_type0(g.m, g.k, g.r);
    else set_type1(g.p);
}

int main(int argc, char **argv) {
    int Glo, iters = 3000;
    unsigned long long seed;
    int bestG = 0;
    GDesc bestD;
    int bestS[MAXD];
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    tlim = atof(argv[4]);
    Glo = atoi(argv[5]);
    if (argc > 6) iters = atoi(argv[6]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || tlim <= 0 || iters < 1) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nxt();
    if (Glo < 2) Glo = 2;
    memset(&bestD, 0, sizeof bestD);

    for (int G = Glo; G < MAXG - 1; G++) {
        double el = now_s();
        double rem = tlim - el;
        if (rem < 0.05) break;
        if (G < DEG + 1) continue;
        int cnt = build_groups(G);
        if (cnt == 0) continue;
        double gb = 0.35 * rem;
        if (gb < 0.5) gb = 0.5;
        double gend = el + gb;
        int found = 0;
        while (now_s() < gend && now_s() < tlim) {
            GDesc g = glist[rnd(cnt)];
            apply_desc(g);
            if (GG != G) continue;
            build_table();
            if (climb(iters) == 0) {
                found = 1;
                bestG = G;
                bestD = g;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
                break;
            }
        }
        if (!found) break;
    }

    if (bestG == 0) {
        printf("0 0\n");
        return 0;
    }
    apply_desc(bestD);
    build_table();
    {
        int G = bestG;
        printf("%d %d\n", 2 * G, G * DEG);
        for (int x = 0; x < G; x++)
            for (int j = 0; j < DEG; j++) {
                int y = MT[x * G + bestS[j]];
                printf("%d %d\n", x, G + y);
            }
    }
    return 0;
}
"""


ANNEAL_SOURCE = r"""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _colour(n, adj):
    """Two-colouring by BFS; components are coloured independently."""
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices in random order. Distances never grow."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _colour(n, adj)
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


def _run_haar(d, D, seed, budget, g0):
    """Group-Haar search in C. Returns the best Haar graph found (order 2g)."""
    out = lib.run_c(HAAR_SOURCE, [d, D, seed, f"{budget:.2f}", g0, 3000],
                    timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def _run_anneal(d, D, seed, graph, budget, stall=1500):
    """Run the bit-parallel annealer from `graph` for `budget` seconds."""
    out = lib.run_c(ANNEAL_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
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

    # Safe fallback: K_{d,d}, valid for D >= 2 and optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3:
        if d >= 3 and lib.is_prime_power(d - 1):
            n0, e0 = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n0, e0, d, D):
                return n0, e0
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n0, e0 = lib.projective_plane_incidence(q)
                consider(n0, e0)
                break
    else:
        # D >= 4: generalized quadrangle W(q) and a saturated variant.
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate(gq[0], gq[1], d, rng))

        # Bold step: group-Haar search in C, climbing the group order from the
        # current best. Budget: first 55% of the time limit.
        haar_end = start + 0.55 * tl
        budget = haar_end - time.monotonic()
        if budget > 2.0 and 2 <= d <= 32:
            try:
                n2, e2 = _run_haar(d, D, seed, budget, best_n // 2 + 1)
                consider(n2, e2)
            except Exception:
                pass

    # Growth: annealer from the best valid graph with the remaining time.
    end = start + 0.9 * tl - 2.0
    budget = end - time.monotonic()
    if budget >= 2.0 and d <= 32:
        try:
            n2, e2 = _run_anneal(d, D, seed, best, budget)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
