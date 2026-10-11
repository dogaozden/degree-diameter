import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New search stage: voltage-lift annealing over semidirect products.
#
# A base multigraph with KB vertices per side and DEG-regular (parallel darts
# allowed, each carrying a distinct group element) is lifted over a group G of
# order MM*KS, giving a DEG-regular bipartite graph on 2*KB*G vertices.
# Group translations are automorphisms, so the diameter check only needs BFS
# from one vertex per base vertex. Cost S = total unreached count over those
# sources; S == 0 means the lift has diameter <= DIAM.
#
# Moves: change one dart's voltage, or swap the B-endpoints of two darts.
# A rejected move is undone from a snapshot.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXBV 64
#define MAXDEG 32
#define MAXE 1024

static int DEG, DIAM, KB, GG, MM, KS, RR, NN, E;
static int PW[64];
static int *mulT, *invT;
static int dA[MAXE], dB[MAXE], dG[MAXE];
static int uA[MAXE], uB[MAXE], uG[MAXE];
static int sA[MAXE], sB[MAXE], sG[MAXE];
static int nbV[MAXBV][MAXDEG], nbG[MAXBV][MAXDEG], nbCnt[MAXBV];
static int *stamp, *qu, *qd;
static int stampc = 0;
static uint64_t rs = 1;

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

static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

/* Semidirect product Z_MM x| Z_KS, element (a,b) coded as a*KS+b. */
static int gmul(int x, int y) {
    int a = x / KS, b = x % KS, c = y / KS, d = y % KS;
    long long t = ((long long)PW[b] * c + a) % MM;
    return (int)t * KS + (b + d) % KS;
}

static int ginv(int x) {
    int a = x / KS, b = x % KS;
    int nb = (KS - b) % KS;
    long long t = ((long long)PW[nb] * a) % MM;
    int ia = (int)((MM - t) % MM);
    return ia * KS + nb;
}

static int bfs_count(int src) {
    stampc++;
    int h = 0, t = 0, cnt = 1;
    qu[t] = src;
    qd[t] = 0;
    t++;
    stamp[src] = stampc;
    while (h < t) {
        int v = qu[h], dv = qd[h];
        h++;
        if (dv >= DIAM) continue;
        int u = v / GG, x = v % GG;
        for (int i = 0; i < nbCnt[u]; i++) {
            int w = nbV[u][i] * GG + mulT[x * GG + nbG[u][i]];
            if (stamp[w] != stampc) {
                stamp[w] = stampc;
                qu[t] = w;
                qd[t] = dv + 1;
                t++;
                cnt++;
            }
        }
    }
    return cnt;
}

static long long eval_cost(void) {
    int V = 2 * KB;
    for (int u = 0; u < V; u++) nbCnt[u] = 0;
    for (int j = 0; j < E; j++) {
        int A = dA[j], B = KB + dB[j], g = dG[j];
        nbV[A][nbCnt[A]] = B;
        nbG[A][nbCnt[A]] = g;
        nbCnt[A]++;
        nbV[B][nbCnt[B]] = A;
        nbG[B][nbCnt[B]] = invT[g];
        nbCnt[B]++;
    }
    long long S = 0;
    for (int u = 0; u < V; u++) S += (long long)(NN - bfs_count(u * GG));
    return S;
}

/* True if some dart i < lim, i != skip, has base pair (a,b) and voltage g. */
static int clash(int lim, int skip, int a, int b, int g) {
    for (int i = 0; i < lim; i++)
        if (i != skip && dA[i] == a && dB[i] == b && dG[i] == g) return 1;
    return 0;
}

static int volt_move(void) {
    int j = rnd(E);
    int g = rnd(GG);
    if (g == dG[j]) return 0;
    if (clash(E, j, dA[j], dB[j], g)) return 0;
    dG[j] = g;
    return 1;
}

static int rewire_move(void) {
    int j1 = rnd(E), j2 = rnd(E);
    if (j1 == j2) return 0;
    int a1 = dA[j1], a2 = dA[j2], b1 = dB[j1], b2 = dB[j2];
    if (a1 == a2 || b1 == b2) return 0;
    if (clash(E, j1, a1, b2, dG[j1])) return 0;
    if (clash(E, j2, a2, b1, dG[j2])) return 0;
    dB[j1] = b2;
    dB[j2] = b1;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    KB = atoi(argv[3]);
    MM = atoi(argv[4]);
    KS = atoi(argv[5]);
    RR = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double tl = atof(argv[8]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || KB < 1 || 2 * KB > MAXBV ||
        KB * DEG > MAXE || MM < 2 || KS < 1 || KS > 64 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    GG = MM * KS;
    if (GG > 2000) {
        printf("0 0\n");
        return 0;
    }
    RR %= MM;
    if (RR < 0) RR += MM;
    PW[0] = 1 % MM;
    for (int i = 1; i < KS; i++) PW[i] = (int)((long long)PW[i - 1] * RR % MM);
    if ((long long)PW[KS - 1] * RR % MM != 1 % MM) {
        printf("0 0\n");
        return 0;
    }

    mulT = malloc(sizeof(int) * (size_t)GG * (size_t)GG);
    invT = malloc(sizeof(int) * (size_t)GG);
    for (int x = 0; x < GG; x++)
        for (int y = 0; y < GG; y++) mulT[x * GG + y] = gmul(x, y);
    for (int x = 0; x < GG; x++) invT[x] = ginv(x);

    NN = 2 * KB * GG;
    stamp = calloc((size_t)NN, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)NN);
    qd = malloc(sizeof(int) * (size_t)NN);

    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    E = KB * DEG;
    int idx = 0;
    int perm[MAXBV];
    for (int r = 0; r < DEG; r++) {
        for (int i = 0; i < KB; i++) perm[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < KB; i++) {
            dA[idx] = i;
            dB[idx] = perm[i];
            idx++;
        }
    }
    for (int j = 0; j < E; j++) {
        int ok = 0;
        for (int t = 0; t < 20000 && !ok; t++) {
            int g = rnd(GG);
            if (!clash(j, -1, dA[j], dB[j], g)) {
                dG[j] = g;
                ok = 1;
            }
        }
        if (!ok) {
            printf("0 0\n");
            return 0;
        }
    }

    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(sA, dA, sizeof(int) * E);
    memcpy(sB, dB, sizeof(int) * E);
    memcpy(sG, dG, sizeof(int) * E);

    double t0 = now_s();
    long long it = 0;
    const long long CYC = 3000;
    const double TH = 1.5, TLo = 0.05;

    while (cur > 0) {
        if (now_s() - t0 >= tl) break;
        if (it > 0 && it % CYC == 0 && cur > bestc) {
            memcpy(dA, sA, sizeof(int) * E);
            memcpy(dB, sB, sizeof(int) * E);
            memcpy(dG, sG, sizeof(int) * E);
            cur = eval_cost();
        }
        double p = (double)(it % CYC) / (double)CYC;
        double T = TH * pow(TLo / TH, p);
        memcpy(uA, dA, sizeof(int) * E);
        memcpy(uB, dB, sizeof(int) * E);
        memcpy(uG, dG, sizeof(int) * E);
        int ok = (rnd01() < 0.5) ? volt_move() : rewire_move();
        it++;
        if (!ok) continue;
        long long c2 = eval_cost();
        long long dl = c2 - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(sA, dA, sizeof(int) * E);
                memcpy(sB, dB, sizeof(int) * E);
                memcpy(sG, dG, sizeof(int) * E);
            }
        } else {
            memcpy(dA, uA, sizeof(int) * E);
            memcpy(dB, uB, sizeof(int) * E);
            memcpy(dG, uG, sizeof(int) * E);
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", NN, E * GG);
    for (int j = 0; j < E; j++)
        for (int x = 0; x < GG; x++) {
            int a = dA[j] * GG + x;
            int b = (KB + dB[j]) * GG + mulT[x * GG + dG[j]];
            printf("%d %d\n", a, b);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C annealer (cost = pairs at distance > DIAM, grows by one vertex when valid).
# Used as the final polish from the best valid graph.
# ----------------------------------------------------------------------------

C_ANNEAL = r"""
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


def _random_group(G, rng):
    """Return (m, k, r) with m * k = G giving Z_m x| Z_k (r^k = 1 mod m); cyclic if none is found."""
    options = [k for k in range(2, 13) if G % k == 0 and G // k >= 3]
    rng.shuffle(options)
    for k in options[:4]:
        m = G // k
        for _ in range(60):
            r = rng.randrange(2, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                return m, k, r
    return G, 1, 1


def _run_lift(d, D, K, m, k, r, seed, budget):
    """Run the lift annealer for a fixed group and base size; return (n, edges), n = 0 if nothing was found."""
    out = lib.run_c(C_LIFT, [d, D, K, m, k, r, seed, f"{budget:.2f}"],
                    stdin_graph=None, timeout=budget + 5.0)
    return lib.parse_graph_text(out)


def _run_anneal(d, D, seed, graph, budget):
    """Run the vertex-growing annealer from `graph` for `budget` seconds."""
    out = lib.run_c(C_ANNEAL, [d, D, seed, f"{budget:.2f}", 1500],
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

    # Quadrangle start (cheap fallback for the D = 4 target): W(q) plus saturation.
    if D >= 4 and d >= 5:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(gq[0], _saturate_edges(gq[0], gq[1], d, rng))

    # Main new stage: voltage lifts over semidirect products. Each run asks for a
    # lift strictly larger than the current best; a success raises the target.
    lift_end = start + 0.55 * tl
    fails = 0
    while d >= 3 and time.monotonic() < lift_end - 1.0 and fails < 3:
        remaining = lift_end - time.monotonic()
        K = rng.choice([1, 1, 2, 2, 3, 3, 4, 5, 6])
        G = best_n // (2 * K) + 1 + rng.choice([0, 0, 0, 1, 2])
        if G < 2 or G > 1500:
            continue
        m, k, r = _random_group(G, rng)
        budget = min(5.0, remaining - 0.5)
        try:
            n2, e2 = _run_lift(d, D, K, m, k, r, rng.randrange(1 << 30), budget)
        except Exception:
            fails += 1
            continue
        fails = 0
        if n2 > 0:
            consider(n2, e2)

    # Final polish: grow the best valid graph with the vertex-adding annealer.
    end = start + 0.9 * tl - 1.0
    remaining = end - time.monotonic()
    if remaining >= 2.0:
        try:
            n2, e2 = _run_anneal(d, D, seed, best, remaining)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
