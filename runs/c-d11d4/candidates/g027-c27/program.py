import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (new): simulated annealing over Z_M x| Z_K2 voltage lifts.
#
# Base graph: k A-vertices and k B-vertices, d darts leaving each A-vertex and
# entering each B-vertex. Lift: vertex (i, x) for A-side base i and group
# element x, joined to (k + j, x*g) for each dart (i -> j, g). The lift is
# invariant under left translation, so every vertex has the same eccentricity
# as one of the 2k base representatives (x = identity). The cost is therefore
# the sum over those 2k representatives of the number of vertices they miss
# within distance D. Cost 0 means diameter <= D.
#
# Moves: change one dart voltage, or swap the B-endpoints of two darts (this
# keeps both degree counts). Parallel darts must keep distinct voltages so the
# lift has no duplicate edges.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXDART (MAXK * MAXD)
#define MAXR 64

static int d, D, k, M, K2, R, G, n, ndart;
static int PW[MAXR];
static int dfrom[MAXDART], dto[MAXDART], dvol[MAXDART];
static int savto[MAXDART], savvol[MAXDART];
static int bestto[MAXDART], bestvol[MAXDART];
static int *adj, *adeg, *stamp, *dist, *queue;
static int stampCur = 0;
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int m) { return (int)(nextr() % (uint64_t)m); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

/* Group multiplication: cyclic if K2 == 1, else (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    if (K2 == 1) return (x + y) % M;
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int a2 = (int)(((long long)a + (long long)PW[b] * c) % M);
    return a2 * K2 + (b + e) % K2;
}

static int build_adj(void) {
    memset(adeg, 0, sizeof(int) * (size_t)n);
    for (int t = 0; t < ndart; t++) {
        int i = dfrom[t], j = dto[t], g = dvol[t];
        for (int x = 0; x < G; x++) {
            int a = i * G + x;
            int b = (k + j) * G + gmul(x, g);
            if (adeg[a] >= d || adeg[b] >= d) return 0;
            adj[(size_t)a * d + adeg[a]++] = b;
            adj[(size_t)b * d + adeg[b]++] = a;
        }
    }
    return 1;
}

/* Parallel darts (same i, same j) must have distinct voltages. */
static int darts_ok(void) {
    for (int a = 0; a < ndart; a++)
        for (int b = a + 1; b < ndart; b++)
            if (dfrom[a] == dfrom[b] && dto[a] == dto[b] && dvol[a] == dvol[b])
                return 0;
    return 1;
}

static long long cost_eval(void) {
    long long total = 0;
    int nr = 2 * k;
    for (int r = 0; r < nr; r++) {
        int s = r * G;
        stampCur++;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        stamp[s] = stampCur;
        dist[s] = 0;
        while (qh < qt) {
            int u = queue[qh++];
            if (dist[u] >= D) continue;
            for (int i = 0; i < adeg[u]; i++) {
                int v = adj[(size_t)u * d + i];
                if (stamp[v] != stampCur) {
                    stamp[v] = stampCur;
                    dist[v] = dist[u] + 1;
                    queue[qt++] = v;
                }
            }
        }
        total += n - qt;
    }
    return total;
}

static void print_graph(void) {
    long long m = 0;
    for (int v = 0; v < n; v++) m += adeg[v];
    m /= 2;
    printf("%d %lld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < adeg[v]; i++) {
            int u = adj[(size_t)v * d + i];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double tl = atof(argv[8]);
    if (d < 1 || d > MAXD || k < 1 || k > MAXK || M < 2 || K2 < 1 || K2 >= MAXR
        || D < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = (K2 == 1) ? M : M * K2;
    if (G < 2 || G < d) {
        printf("0 0\n");
        return 0;
    }
    if (K2 > 1) {
        PW[0] = 1 % M;
        for (int b = 1; b < K2; b++)
            PW[b] = (int)((long long)PW[b - 1] * (R % M) % M);
    }
    n = 2 * k * G;
    if (n > 60000) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    adj = malloc(sizeof(int) * (size_t)n * d);
    adeg = malloc(sizeof(int) * (size_t)n);
    stamp = calloc((size_t)n, sizeof(int));
    dist = malloc(sizeof(int) * (size_t)n);
    queue = malloc(sizeof(int) * (size_t)n);
    if (!adj || !adeg || !stamp || !dist || !queue) {
        printf("0 0\n");
        return 0;
    }

    ndart = k * d;
    for (int p = 0; p < d; p++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            int t = p * k + i;
            dfrom[t] = i;
            dto[t] = perm[i];
            dvol[t] = rnd(G);
        }
    }
    int tries = 0;
    while (!darts_ok() && tries < 20000) {
        dvol[rnd(ndart)] = rnd(G);
        tries++;
    }
    if (!(darts_ok() && build_adj())) {
        printf("0 0\n");
        return 0;
    }

    long long cur = cost_eval();
    long long bestc = cur;
    memcpy(bestto, dto, sizeof(int) * ndart);
    memcpy(bestvol, dvol, sizeof(int) * ndart);

    double c0 = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    long long stall = 0, it = 0;

    while (cur > 0) {
        if ((it & 31) == 0) {
            frac = ((double)clock() / CLOCKS_PER_SEC - c0) / tl;
            if (frac >= 1.0) break;
        }
        it++;
        double T = 1.0 + 30.0 * (1.0 - frac);

        memcpy(savto, dto, sizeof(int) * ndart);
        memcpy(savvol, dvol, sizeof(int) * ndart);
        int t1 = rnd(ndart);
        if (rnd01() < 0.6) {
            dvol[t1] = (dvol[t1] + 1 + rnd(G - 1)) % G;
        } else {
            int t2 = rnd(ndart);
            if (t2 == t1) continue;
            int tmp = dto[t1];
            dto[t1] = dto[t2];
            dto[t2] = tmp;
        }

        int ok = darts_ok() && build_adj();
        int accept = 0;
        long long c2 = 0;
        if (ok) {
            c2 = cost_eval();
            double dl = (double)(c2 - cur);
            if (dl <= 0 || rnd01() < exp(-dl / T)) accept = 1;
        }
        if (accept) {
            cur = c2;
        } else {
            memcpy(dto, savto, sizeof(int) * ndart);
            memcpy(dvol, savvol, sizeof(int) * ndart);
            build_adj();
        }

        if (cur < bestc) {
            bestc = cur;
            memcpy(bestto, dto, sizeof(int) * ndart);
            memcpy(bestvol, dvol, sizeof(int) * ndart);
            stall = 0;
        } else if (++stall > 30000) {
            memcpy(dto, bestto, sizeof(int) * ndart);
            memcpy(dvol, bestvol, sizeof(int) * ndart);
            build_adj();
            cur = cost_eval();
            stall = 0;
        }
    }

    if (cur != 0) {
        printf("0 0\n");
    } else {
        print_graph();
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: general simulated annealing with growth (from the parent program).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
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
    """Greedily join deficient opposite-side vertices in random order. Returns (n, edges)."""
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
    return n, edges


def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices (same neighbourhood) while all neighbours have spare degree."""
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


def _pick_group(G, rng):
    """Return (M, K2, R) with group order G: semidirect Z_M x| Z_K2 (R^K2 = 1 mod M), or cyclic."""
    opts = []
    for K2 in range(2, 13):
        if G % K2 or G // K2 < 3:
            continue
        M = G // K2
        cands = [r for r in range(2, M) if math.gcd(r, M) == 1 and pow(r, K2, M) == 1]
        if cands:
            opts.append((M, K2, rng.choice(cands)))
    if opts and rng.random() < 0.7:
        return rng.choice(opts)
    return (G, 1, 1)


def _lift_run(d, D, k, M, K2, R, seed, budget):
    """Run the C voltage annealer; return (n, edges) or None if no valid lift was found."""
    out = lib.run_c(C_LIFT, [d, D, k, M, K2, R, seed, f"{budget:.2f}"],
                    stdin_graph=None, timeout=budget + 6.0)
    n, e = lib.parse_graph_text(out)
    if n <= 0 or not e:
        return None
    return n, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power gives the Moore-optimal incidence graph.
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

    # D = 3 (non-calibration): projective planes with twin growth and saturation.
    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in pg_qs:
            pn, pe = lib.projective_plane_incidence(q)
            consider(pn, pe)
            sn, se = _saturate_edges(pn, pe, d, rng)
            consider(sn, se)
            tn, te = _twin_grow(pn, pe, d, rng, start + 0.4 * tl)
            consider(tn, te)

    # D >= 4: start from W(q) (valid, diameter 4), saturated with spare degree.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sn, se = _saturate_edges(gq[0], gq[1], d, rng)
            consider(sn, se)

    # New stage: voltage-lift annealing in C, growing the group order.
    if D >= 4 and d >= 3:
        lift_end = start + (0.6 if d >= 5 else 0.5) * tl
        KS = [1, 2, 3, 4, 5, 6]
        ladder = {k: 0 for k in KS}
        fails = {k: 0 for k in KS}
        while True:
            rem = lift_end - time.monotonic()
            if rem < 2.5:
                break
            k = rng.choice(KS)
            floor = best_n // (2 * k) + 1
            G = max(ladder[k], floor, d, 2)
            M, K2, R = _pick_group(G, rng)
            budget = min(rem - 1.0, max(3.0, min(8.0, rem / 3.0)))
            if budget < 1.5:
                break
            try:
                res = _lift_run(d, D, k, M, K2, R, rng.randrange(1 << 30), budget)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = G + max(1, G // 100)
                fails[k] = 0
            else:
                fails[k] += 1
                if fails[k] >= 2:
                    ladder[k] = max(best_n // (2 * k) + 1, G - max(1, G // 200))
                    fails[k] = 0

    # General annealing with growth, from the best valid graph found so far.
    if D >= 4 and d >= 5:
        end = start + 0.9 * tl - 1.0
        remaining = end - time.monotonic()
        if remaining > 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", 1500],
                                stdin_graph=best, timeout=remaining + 4.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
