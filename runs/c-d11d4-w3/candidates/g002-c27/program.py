import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C search engine (parent): simulated annealing over bipartite graphs with
# swap, relocate and targeted moves. Cost = number of vertex pairs at distance
# > DIAM. Stalls restore the best graph and kick it.
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
static int bq[MAXN], bmark[MAXN], bdist[MAXN], cand[MAXN];
static int bstamp = 0;
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
    int x = rnd(nv);
    if (deg[x] == 0) return 0;
    bstamp++;
    int qh = 0, qt = 0;
    bq[qt++] = x;
    bmark[x] = bstamp;
    bdist[x] = 0;
    while (qh < qt) {
        int u = bq[qh++];
        if (bdist[u] >= DIAM) continue;
        for (int i = 0; i < deg[u]; i++) {
            int w = adjv[u][i];
            if (bmark[w] != bstamp) {
                bmark[w] = bstamp;
                bdist[w] = bdist[u] + 1;
                bq[qt++] = w;
            }
        }
    }
    int nf = 0;
    for (int i = 0; i < nv; i++)
        if (col[i] == col[x] && bmark[i] != bstamp) cand[nf++] = i;
    if (nf == 0) return 0;
    int y = cand[rnd(nf)];
    if (deg[y] == 0) return 0;
    int e = adjv[y][rnd(deg[y])];
    if (deg[e] == 0) return 0;
    int c = adjv[e][rnd(deg[e])];
    if (c == y || c == x) return 0;
    if (col[c] != col[x]) return 0;
    int b = adjv[x][rnd(deg[x])];
    if (b == e) return 0;
    if (has_edge(x, e) || has_edge(c, b)) return 0;
    logN = 0;
    edit_remove(x, b);
    edit_remove(c, e);
    edit_add(x, e);
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
        double u = rnd01();
        int ok;
        if (u < 0.30) ok = swap_move();
        else if (u < 0.50) ok = relocate_move();
        else ok = targeted_move();
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
# NEW C engine: bi-Cayley graphs over metacyclic groups Z_m x| Z_k.
#
# Vertices: (x,0) = x and (x,1) = N + x, with N = m*k. Edge (x,0)-(x*s,1) for s in S,
# |S| = DEG. Left multiplication is an automorphism, so the graph is a DEG-regular
# bipartite graph and only two BFS runs (from (1,0) and (1,1)) decide the diameter.
# Cost = unreached vertices from both sources. The search anneals the set S.
# ----------------------------------------------------------------------------

BICAYLEY_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1400
#define DMAX 24
#define RESTART_LEN 30000

static int M, K, R, N, DEG, DIAM;
static int *mt;
static int invt[NMAX];
static int S[DMAX], Sinv[DMAX];
static int inS[NMAX];
static int dd[2 * NMAX], mark[2 * NMAX], qv[2 * NMAX];
static int mc = 0;
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

static void build_tables(void) {
    int *pw = malloc(sizeof(int) * (size_t)K);
    pw[0] = 1 % M;
    for (int j = 1; j < K; j++) pw[j] = (int)((long long)pw[j - 1] * R % M);
    mt = malloc(sizeof(int) * (size_t)N * (size_t)N);
    for (int x = 0; x < N; x++) {
        int a = x / K, b = x % K;
        for (int y = 0; y < N; y++) {
            int c = y / K, e = y % K;
            int ra = (int)(((long long)a + (long long)pw[b] * c) % M);
            int rb = (b + e) % K;
            mt[(size_t)x * N + y] = ra * K + rb;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[(size_t)x * N + y] == 0) { invt[x] = y; break; }
    free(pw);
}

static int bfs_reach(int src) {
    mc++;
    int h = 0, t = 0;
    qv[t++] = src;
    mark[src] = mc;
    dd[src] = 0;
    while (h < t) {
        int u = qv[h++];
        if (dd[u] >= DIAM) continue;
        if (u < N) {
            for (int j = 0; j < DEG; j++) {
                int v = N + mt[(size_t)u * N + S[j]];
                if (mark[v] != mc) {
                    mark[v] = mc;
                    dd[v] = dd[u] + 1;
                    qv[t++] = v;
                }
            }
        } else {
            int y = u - N;
            for (int j = 0; j < DEG; j++) {
                int v = mt[(size_t)y * N + Sinv[j]];
                if (mark[v] != mc) {
                    mark[v] = mc;
                    dd[v] = dd[u] + 1;
                    qv[t++] = v;
                }
            }
        }
    }
    return t;
}

static long cost_now(void) {
    for (int j = 0; j < DEG; j++) Sinv[j] = invt[S[j]];
    long bad0 = 2L * N - bfs_reach(0);
    long bad1 = 2L * N - bfs_reach(N);
    return bad0 + bad1;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    R = atoi(argv[3]);
    DEG = atoi(argv[4]);
    DIAM = atoi(argv[5]);
    unsigned long long seed = strtoull(argv[6], NULL, 10);
    double tl = atof(argv[7]);
    if (M < 1 || K < 1 || DEG < 1 || DEG > DMAX || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    N = M * K;
    if (N > NMAX || N <= DEG) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 4242ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    build_tables();

    int found = 0;
    while (!found) {
        if ((double)clock() / CLOCKS_PER_SEC >= tl) break;
        memset(inS, 0, sizeof(int) * NMAX);
        for (int j = 0; j < DEG; j++) {
            int e;
            do { e = rnd(N); } while (inS[e]);
            inS[e] = 1;
            S[j] = e;
        }
        long cur = cost_now();
        for (long it = 0;; it++) {
            if (cur == 0) { found = 1; break; }
            if (it >= RESTART_LEN) break;
            if ((it & 63) == 0 && (double)clock() / CLOCKS_PER_SEC >= tl) break;
            double T = 2.0 * (1.0 - (double)it / RESTART_LEN) + 0.1;
            int j = rnd(DEG);
            int e;
            do { e = rnd(N); } while (inS[e]);
            int old = S[j];
            inS[old] = 0;
            inS[e] = 1;
            S[j] = e;
            long c2 = cost_now();
            long dl = c2 - cur;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
                cur = c2;
            } else {
                inS[e] = 0;
                inS[old] = 1;
                S[j] = old;
            }
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * N, N * DEG);
    for (int x = 0; x < N; x++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", x, N + mt[(size_t)x * N + S[j]]);
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


def _lns_step(n, edges, d, D, rng, deadline):
    """One delete-and-regrow move; returns a valid (n2, edges2) with n2 >= n, or None."""
    if n < 6:
        return None
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    k = rng.randint(2, 6)
    if rng.random() < 0.5:
        c = rng.randrange(n)
        order = [c]
        seen = {c}
        i = 0
        while i < len(order) and len(order) < k:
            u = order[i]
            i += 1
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    order.append(w)
        removed = set(order[:k])
    else:
        removed = set(rng.sample(range(n), k))
    keep = [v for v in range(n) if v not in removed]
    idx = {v: i for i, v in enumerate(keep)}
    e1 = [(idx[u], idx[v]) for u, v in edges if u in idx and v in idx]
    n1 = len(keep)
    n2, e2 = _twin_grow(n1, e1, d, rng, deadline)
    n2, e2 = _grow(n2, e2, d, D, deadline, rng)
    if n2 < n or time.monotonic() >= deadline:
        return None
    if not lib.is_valid(n2, e2, d, D):
        return None
    return n2, e2


def _run_c(d, D, seed, graph, budget, stall=1500):
    """Run the parent C annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def _parent_build(d, D, seed, time_limit):
    """Parent pipeline (projective planes, quadrangles, growth, LNS, C annealing).

    Always returns a valid graph (K_{d,d} fallback at worst).
    """
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    use_c = D >= 4 and d >= 5
    if use_c:
        pipe_end = start + 0.28 * tl
        deadline = start + 0.36 * tl
    else:
        pipe_end = start + 0.5 * tl
        deadline = start + 0.85 * tl

    if D == 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        t0 = time.monotonic()
        span = max(0.0, 0.3 * (deadline - t0))
        for i, q in enumerate(pg_qs):
            pg_n, pg_e = lib.projective_plane_incidence(q)
            consider(pg_n, pg_e)
            slice_end = t0 + span * (i + 1) / len(pg_qs)
            n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
            consider(n2, e2)

    sat = None
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat = (gq[0], _saturate_edges(gq[0], gq[1], d, rng))
            consider(sat[0], sat[1])
            first = True
            while time.monotonic() < pipe_end or first:
                if first:
                    src = gq
                else:
                    src = rng.choice([gq, sat, best])
                first = False
                pn, pe = _pipeline(src[0], src[1], d, D, pipe_end, rng)
                consider(pn, pe)

        lns_end = start + (0.45 if use_c else 0.85) * tl
        cur = best
        while time.monotonic() < lns_end:
            res = _lns_step(cur[0], cur[1], d, D, rng, lns_end)
            if res is not None:
                cur = res
                consider(res[0], res[1])
            elif rng.random() < 0.02:
                cur = best

    if use_c:
        end = start + 0.88 * tl - 1.0
        starts_c = [best]
        if sat is not None:
            starts_c.append(sat)
        for idx, g in enumerate(starts_c):
            remaining = end - time.monotonic()
            if remaining < 2.0:
                break
            share = 0.6 if (idx == 0 and len(starts_c) > 1) else 1.0
            budget = remaining * share
            try:
                n2, e2 = _run_c(d, D, seed + idx, g, budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# NEW construction: bi-Cayley graphs over metacyclic groups.
# ----------------------------------------------------------------------------

_BC_ATTEMPT = 3.0  # seconds per C attempt


def _bicayley_groups(N, rng, max_k=20):
    """Candidate semidirect products Z_m x| Z_k of order N as (m, k, r) triples, shuffled."""
    out = []
    for k in range(1, max_k + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:2]:
            out.append((m, k, r))
    rng.shuffle(out)
    return out


def _bicayley_search(d, D, N_lo, deadline, rng, seed):
    """Search bi-Cayley graphs of order 2N for increasing N; return the largest valid one found."""
    best = None
    N = N_lo
    fails = 0
    errors = 0
    cache = {}
    while time.monotonic() < deadline - 0.5 and N <= 1111:
        if N not in cache:
            cache[N] = _bicayley_groups(N, rng)
        gl = cache[N]
        if not gl:
            N += 1
            fails = 0
            continue
        m, k, r = gl[fails % len(gl)]
        budget = min(_BC_ATTEMPT, deadline - time.monotonic())
        if budget < 0.3:
            break
        n, e = 0, []
        try:
            out = lib.run_c(BICAYLEY_C, [m, k, r, d, D, seed * 7919 + N, f"{budget:.2f}"],
                            timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            errors += 1
            if errors >= 3:
                break
            n, e = 0, []
        if n > 0 and lib.is_valid(n, e, d, D):
            best = (n, e)
            N += 1
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                N += 1
                fails = 0
    return best


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

    def take(res):
        nonlocal best
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if D == 4 and d >= 5:
        # Parent pipeline first, on a short budget, as the safety net.
        try:
            take(_parent_build(d, D, seed, 0.3 * tl))
        except Exception:
            pass
        # New bold phase: bi-Cayley search from just above the parent's order.
        N_lo = int(0.39 * lib.moore_bound(d, D)) + 2
        deadline = start + 0.9 * tl - 1.0
        try:
            take(_bicayley_search(d, D, N_lo, deadline, rng, seed))
        except Exception:
            pass
        return best

    try:
        take(_parent_build(d, D, seed, tl))
    except Exception:
        pass
    return best
