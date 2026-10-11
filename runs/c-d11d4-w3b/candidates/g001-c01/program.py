import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing over bipartite graphs with three moves.
#
#   * swap, targeted and relocate moves on an explicit graph
#   * stall kicks (vertex replacement or double relocate)
#   * cost = number of unordered vertex pairs at distance > DIAM
#   * whenever cost is 0 the state is saved and grown by one vertex
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
# C engine 2 (new construction): voltage lifts over semidirect products
# G = Z_M x| Z_K2 with a random d-regular bipartite base on K + K vertices.
#
# Vertices are (base b, element x), b < 2K, x < G. Dart e = (u, v, g) joins
# (u, x) to (K + v, x*g). Left translation by G is an automorphism, so the
# bad-pair count equals G times the sum over the 2K base vertices of the number
# of vertices unreachable from (b, identity) within DIAM steps. Each evaluation
# is therefore 2K BFS runs. Simulated annealing changes one voltage per move and
# stops as soon as the cost reaches 0.
#
# Output: "1 NDART" then NDART lines "u v g" on success, else "0 0".
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXDEG 16
#define MAXDART (MAXK * MAXDEG)
#define MAXG 4096
#define MAXN (2 * MAXK * MAXG)

static int DEG, DIAM, K, M, K2, R, G, NDART;
static int pw[MAXG];
static int ginv[MAXG];
static int du[MAXDART], dv[MAXDART], dg[MAXDART];
static int badj[2 * MAXK][MAXDEG];
static int dist_[MAXN];
static int que[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t nxt64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(nxt64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(nxt64() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a1 = x / K2, b1 = x % K2;
    int a2 = y / K2, b2 = y % K2;
    int a = (a1 + pw[b1] * a2) % M;
    int b = (b1 + b2) % K2;
    return a * K2 + b;
}

static long long eval_cost(void) {
    int N = 2 * K * G;
    long long total = 0;
    for (int b0 = 0; b0 < 2 * K; b0++) {
        for (int i = 0; i < N; i++) dist_[i] = -1;
        int src = b0 * G;
        int qh = 0, qt = 0;
        dist_[src] = 0;
        que[qt++] = src;
        while (qh < qt) {
            int v = que[qh++];
            int dd = dist_[v];
            if (dd >= DIAM) continue;
            int b = v / G;
            int x = v - b * G;
            for (int t = 0; t < DEG; t++) {
                int e = badj[b][t];
                int w;
                if (b < K) w = (K + dv[e]) * G + gmul(x, dg[e]);
                else w = du[e] * G + gmul(x, ginv[dg[e]]);
                if (dist_[w] < 0) {
                    dist_[w] = dd + 1;
                    que[qt++] = w;
                }
            }
        }
        total += N - qt;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    M = atoi(argv[5]);
    K2 = atoi(argv[6]);
    R = atoi(argv[7]);
    K = atoi(argv[8]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || K < 1 || K > MAXK || M < 1 || K2 < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (G < 1 || G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    R = ((R % M) + M) % M;

    rs = seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nxt64();

    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)(((long long)pw[b - 1] * R) % M);
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        int nb = (K2 - b) % K2;
        long long t = ((long long)pw[nb] * a) % M;
        int ap = (int)((M - t) % M);
        ginv[x] = ap * K2 + nb;
    }

    NDART = DEG * K;
    int perm[MAXK];
    for (int j = 0; j < DEG; j++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rndi(i + 1);
            int t = perm[i];
            perm[i] = perm[r];
            perm[r] = t;
        }
        for (int i = 0; i < K; i++) {
            int e = j * K + i;
            du[e] = i;
            dv[e] = perm[i];
            dg[e] = rndi(G);
        }
    }

    int cnt[2 * MAXK];
    memset(cnt, 0, sizeof cnt);
    for (int e = 0; e < NDART; e++) {
        int a = du[e];
        badj[a][cnt[a]++] = e;
        int b = K + dv[e];
        badj[b][cnt[b]++] = e;
    }

    long long cur = eval_cost();
    double tstart = (double)clock() / CLOCKS_PER_SEC;
    while (cur > 0) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - tstart) / tl;
        if (frac >= 1.0) break;
        double T = 0.8 * (1.0 - frac) + 0.05;
        int e = rndi(NDART);
        int old = dg[e];
        int nvv = rndi(G);
        if (nvv == old) continue;
        dg[e] = nvv;
        long long c2 = eval_cost();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) cur = c2;
        else dg[e] = old;
    }

    if (cur == 0) {
        printf("1 %d\n", NDART);
        for (int e = 0; e < NDART; e++) printf("%d %d %d\n", du[e], dv[e], dg[e]);
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
    """Greedily join deficient opposite-side vertices in random order (keeps diameter and bipartiteness)."""
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
    """Insert BFS-verified vertices (old distances are preserved) until the deadline or repeated failure."""
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
# NEW construction glue: voltage lifts over semidirect products searched in C.
# ----------------------------------------------------------------------------

def _sample_params(G, rng):
    """Return (M, K2, R) with M * K2 = G and R a valid multiplier (R^K2 = 1 mod M), or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    rng.shuffle(divs)
    for K2 in divs:
        M = G // K2
        if K2 == 1:
            return M, 1, 1
        cands = [1]
        pool = rng.sample(range(2, M), min(M - 2, 60)) if M > 2 else []
        for r in pool:
            if math.gcd(r, M) == 1 and pow(r, K2, M) == 1 % M:
                cands.append(r)
        if cands:
            return M, K2, rng.choice(cands)
    return None


def _lift_search(d, D, K, M, K2, R, seed, budget):
    """Run the C lift annealer; return the list of darts (u, v, g) on success, else None."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{budget:.2f}", M, K2, R, K],
                    timeout=budget + 4.0)
    nums = out.split()
    if len(nums) < 2 or nums[0] != "1":
        return None
    m = int(nums[1])
    if len(nums) < 2 + 3 * m:
        return None
    return [(int(nums[2 + 3 * i]), int(nums[3 + 3 * i]), int(nums[4 + 3 * i]))
            for i in range(m)]


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

    # D = 3 non-calibration: one projective plane plus saturation.
    if D == 3 and d >= 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            n1, e1 = lib.projective_plane_incidence(qs[0])
            consider(n1, e1)
            consider(n1, _saturate_edges(n1, e1, d, rng))

    if D >= 4 and d >= 3:
        # Stage 1: generalized quadrangle W(q), saturation, BFS-verified insertion.
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat = _saturate_edges(gq[0], gq[1], d, rng)
            consider(gq[0], sat)
            ins_end = start + 0.14 * tl
            n2, e2 = _insert_grow(state["best"][0], state["best"][1], d, D, ins_end, rng)
            consider(n2, e2)

        # Stage 2: voltage lifts over semidirect products, searched in C.
        lift_end = start + 0.80 * tl
        Ks = [1, 2, 3, 4]
        target_G = {K: 2 for K in Ks}
        fails = {K: 0 for K in Ks}
        while time.monotonic() < lift_end - 1.0:
            best_n = state["best"][0]
            K = rng.choice(Ks)
            G = max(target_G[K], best_n // (2 * K) + 1, 2)
            params = _sample_params(G, rng)
            if params is None:
                target_G[K] = G + 1
                continue
            M, K2, R = params
            remaining = lift_end - time.monotonic()
            budget = min(remaining, max(2.0, 0.06 * tl))
            if budget < 0.5:
                break
            try:
                darts = _lift_search(d, D, K, M, K2, R, rng.randrange(1 << 30), budget)
            except Exception:
                darts = None
                fails[K] += 2
            if darts is None:
                fails[K] += 1
                if fails[K] >= 2:
                    target_G[K] = G + 1
                    fails[K] = 0
                else:
                    target_G[K] = G
                continue
            fails[K] = 0
            try:
                order, mul, _ = lib.semidirect_group(M, K2, R)
                n, e = lib.group_lift(2 * K, [(u, K + v, g) for u, v, g in darts], order, mul)
                consider(n, e)
                consider(n, _saturate_edges(n, e, d, rng))
            except Exception:
                pass
            target_G[K] = G + 1

        # Stage 3: C annealing from the best valid graph found so far.
        end = start + 0.92 * tl - 1.5
        remaining = end - time.monotonic()
        if remaining >= 2.0:
            try:
                n2, e2 = _run_c(d, D, seed, state["best"], remaining)
                consider(n2, e2)
            except Exception:
                pass

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
