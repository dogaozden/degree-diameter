import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: exact-cost voltage lifts over Z_m.
#
# A base bipartite graph has k vertices per side and d darts per base vertex
# (d random perfect matchings between the sides). Dart (a, b, t) joins
# (a, g) to (k+b, g+t mod m). The lift has 2km vertices, is d-regular and
# bipartite. Z_m acts regularly on each fibre, so distance (u,g)->(v,h) equals
# distance (u,0)->(v,h-g). Diameter <= D therefore only needs one BFS from
# each of the 2k base vertices (u,0). The cost is the number of unreached
# (source, vertex) pairs plus a penalty for duplicate darts. Simulated
# annealing mutates dart voltages and swaps two targets inside one matching.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDART 512
#define MAXV 32
#define MAXNV 16384
#define MAXBD 40

static int d, D, k, m, V, N, nd;
static int dA[MAXDART], dB[MAXDART], dT[MAXDART];
static int bdeg[MAXV];
static int badjV[MAXV][MAXBD], badjS[MAXV][MAXBD];
static int stampArr[MAXNV], distArr[MAXNV], qbuf[MAXNV];
static int stampCur = 0;
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int n) { return (int)(nextr() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static void build_base(void) {
    for (int u = 0; u < V; u++) bdeg[u] = 0;
    for (int i = 0; i < nd; i++) {
        int a = dA[i];
        int b = k + dB[i];
        badjV[a][bdeg[a]] = b;
        badjS[a][bdeg[a]] = dT[i];
        bdeg[a]++;
        badjV[b][bdeg[b]] = a;
        badjS[b][bdeg[b]] = (m - dT[i]) % m;
        bdeg[b]++;
    }
}

static long long eval_cost(void) {
    long long pen = 0;
    for (int i = 0; i < nd; i++)
        for (int j = i + 1; j < nd; j++)
            if (dA[i] == dA[j] && dB[i] == dB[j] && dT[i] == dT[j]) pen++;
    build_base();
    long long cost = 0;
    for (int u = 0; u < V; u++) {
        stampCur++;
        int qh = 0, qt = 0;
        int src = u * m;
        stampArr[src] = stampCur;
        distArr[src] = 0;
        qbuf[qt++] = src;
        while (qh < qt) {
            int x = qbuf[qh++];
            int dx = distArr[x];
            if (dx >= D) continue;
            int bu = x / m;
            int g = x - bu * m;
            for (int i = 0; i < bdeg[bu]; i++) {
                int h = g + badjS[bu][i];
                if (h >= m) h -= m;
                int y = badjV[bu][i] * m + h;
                if (stampArr[y] != stampCur) {
                    stampArr[y] = stampCur;
                    distArr[y] = dx + 1;
                    qbuf[qt++] = y;
                }
            }
        }
        cost += N - qt;
    }
    return cost + 40 * pen;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    double tl = atof(argv[6]);
    if (d < 1 || d > MAXBD - 1 || D < 1 || k < 1 || k > 16 || m < 2 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    V = 2 * k;
    N = V * m;
    nd = k * d;
    if (N > MAXNV || nd > MAXDART) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 99991ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    for (int l = 0; l < d; l++) {
        int p[MAXV];
        for (int a = 0; a < k; a++) p[a] = a;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int a = 0; a < k; a++) {
            int idx = l * k + a;
            dA[idx] = a;
            dB[idx] = p[a];
            dT[idx] = rnd(m);
        }
    }

    long long cur = eval_cost();
    clock_t c0 = clock();
    double frac = 0.0, T = 3.0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 63) == 0) {
            frac = ((double)(clock() - c0) / CLOCKS_PER_SEC) / tl;
            if (frac >= 1.0) break;
            T = 3.0 * (1.0 - frac) + 0.1;
        }
        it++;
        int kind = (k >= 2 && rnd01() < 0.15) ? 1 : 0;
        int i1 = 0, i2 = 0, oldt = 0;
        if (kind == 0) {
            i1 = rnd(nd);
            oldt = dT[i1];
            int nt = rnd(m);
            if (m > 1)
                while (nt == oldt) nt = rnd(m);
            dT[i1] = nt;
        } else {
            int l = rnd(d);
            int a1 = rnd(k);
            int a2 = rnd(k - 1);
            if (a2 >= a1) a2++;
            i1 = l * k + a1;
            i2 = l * k + a2;
            int t = dB[i1];
            dB[i1] = dB[i2];
            dB[i2] = t;
        }
        long long c2 = eval_cost();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            if (kind == 0) {
                dT[i1] = oldt;
            } else {
                int t = dB[i1];
                dB[i1] = dB[i2];
                dB[i2] = t;
            }
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %lld\n", N, (long long)nd * m);
    for (int i = 0; i < nd; i++) {
        int a = dA[i];
        int b = k + dB[i];
        for (int g = 0; g < m; g++) {
            int h = (g + dT[i]) % m;
            printf("%d %d\n", a * m + g, b * m + h);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: simulated annealing over bipartite graphs (the parent engine).
# It grows a valid graph by one vertex whenever the bad-pair cost reaches 0.
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
static int badCnt[MAXN], tmpBad[MAXN];

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
        tmpBad[v] = nv - cnt;
        bad += nv - cnt;
    }
    return bad / 2;
}

static void commit_bad(void) {
    memcpy(badCnt, tmpBad, sizeof(int) * (size_t)nv);
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
    int v = -1;
    for (int t = 0; t < 64; t++) {
        int x = rnd(nv);
        if (badCnt[x] > 0) {
            v = x;
            break;
        }
    }
    if (v < 0) v = rnd(nv);
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
    commit_bad();
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
            commit_bad();
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
            commit_bad();
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
            commit_bad();
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

# Target orders for the lift search; other cases use the current best + 1.
LIFT_TARGET = {(11, 4): 1735}
# Share of the lift window given to the first attempt with each base size k.
LIFT_WEIGHT = {3: 0.30, 2: 0.25, 4: 0.20, 5: 0.12, 1: 0.07, 6: 0.06}


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


def _c_lift(d, D, k, m, seed, budget):
    """Run the lift annealer for base size k and group Z_m; return (n, edges) or None."""
    out = lib.run_c(C_LIFT, [d, D, k, m, seed, f"{budget:.2f}"], timeout=budget + 5.0)
    n, e = lib.parse_graph_text(out)
    return (n, e) if n > 0 and e else None


def _lift_stage(d, D, best_n, deadline, rng, consider):
    """Search lifts of increasing order; keep growing m for the first base size that works."""
    T = LIFT_TARGET.get((d, D), best_n + 1)
    window = deadline - time.monotonic()
    if window < 2.0:
        return
    got = None
    for k in [3, 2, 4, 5, 1, 6]:
        now = time.monotonic()
        budget = min(window * LIFT_WEIGHT[k], deadline - now)
        if budget < 1.0:
            continue
        m = max(2, -(-T // (2 * k)))
        res = _c_lift(d, D, k, m, rng.randrange(1 << 30), budget)
        if res is not None:
            consider(*res)
            got = (k, m)
            break
    if got is None:
        return
    k, m = got
    while True:
        now = time.monotonic()
        left = deadline - now
        if left < 2.0:
            break
        m += 1
        res = _c_lift(d, D, k, m, rng.randrange(1 << 30), min(left, 0.5 * window))
        if res is None:
            break
        consider(*res)


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
    state = {"best": lib.haar_graph(d, range(d))}

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    def finish():
        b = state["best"]
        if not lib.is_valid(b[0], b[1], d, D):
            b = lib.haar_graph(d, range(d))
        return b

    use_c = D >= 4 and d >= 5

    # Stage 1: exact-cost voltage lifts (a different construction from GQ growth).
    lift_end = start + (0.40 * tl if use_c else 0.80 * tl)
    _lift_stage(d, D, state["best"][0], lift_end, rng, consider)

    if not use_c:
        return finish()

    # Stage 2: generalized quadrangle W(q) and its saturated variant as fallback starts.
    sat = None
    gq = _best_gq(d)
    if gq is not None:
        consider(gq[0], gq[1])
        sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
        consider(sat[0], sat[1])

    # Stage 3: annealing from the best valid graph, then from the saturated quadrangle.
    end = start + 0.92 * tl - 1.0
    starts = [state["best"]]
    if sat is not None:
        starts.append(sat)
    for idx, g in enumerate(starts):
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        share = remaining if idx == len(starts) - 1 else 0.6 * remaining
        try:
            n2, e2 = _run_c(d, D, seed + idx, g, share)
            consider(n2, e2)
        except Exception:
            pass

    return finish()
