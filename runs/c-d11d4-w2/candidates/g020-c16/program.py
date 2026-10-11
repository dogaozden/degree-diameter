import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (new): bi-Cayley search. The graph has vertices a_g and b_g for g in a
# finite group G of order M*K, with edges a_g ~ b_{g s} for s in a connection set S
# of size d. Left translation is an automorphism, so zero cost (from the two roots
# a_e and b_e) means diameter <= DIAM. Simulated annealing over S.
# Group: Z_M x|_R Z_K, element (a,b) coded a*K+b, (a,b)(c,d) = (a + R^b c, b + d).
# ----------------------------------------------------------------------------

BC_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 4096
#define MAXD 32

static int M, K, DEG, DIAM, G;
static int pw[64];
static int S[MAXD], invS[MAXD];
static unsigned char inS[MAXG];
static uint64_t rs = 1;
static int stampArr[2 * MAXG], distArr[2 * MAXG], qbuf[2 * MAXG];
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

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, d = y % K;
    int ra = (a + pw[b] * c) % M;
    int rb = (b + d) % K;
    return ra * K + rb;
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int ra = (M - (pw[nb] * a) % M) % M;
    return ra * K + nb;
}

/* BFS from root up to depth DIAM. Vertices: A = 0..G-1 (a_g), B = G..2G-1 (b_g).
   Returns the number of A-side and B-side vertices reached. */
static void bfs_counts(int root, int *cntA, int *cntB) {
    stampCur++;
    int qh = 0, qt = 0, ca = 0, cb = 0;
    qbuf[qt++] = root;
    stampArr[root] = stampCur;
    distArr[root] = 0;
    while (qh < qt) {
        int u = qbuf[qh++];
        int du = distArr[u];
        if (u < G) {
            ca++;
            if (du >= DIAM) continue;
            for (int i = 0; i < DEG; i++) {
                int x = G + gmul(u, S[i]);
                if (stampArr[x] != stampCur) {
                    stampArr[x] = stampCur;
                    distArr[x] = du + 1;
                    qbuf[qt++] = x;
                }
            }
        } else {
            cb++;
            if (du >= DIAM) continue;
            int h = u - G;
            for (int i = 0; i < DEG; i++) {
                int x = gmul(h, invS[i]);
                if (stampArr[x] != stampCur) {
                    stampArr[x] = stampCur;
                    distArr[x] = du + 1;
                    qbuf[qt++] = x;
                }
            }
        }
    }
    *cntA = ca;
    *cntB = cb;
}

/* Zero iff diameter <= DIAM: by left-translation symmetry only the balls of a_e
   (A and B parts) and of b_e (B part) matter. */
static long cost(void) {
    int ca, cb, dummyA, cbb;
    bfs_counts(0, &ca, &cb);
    bfs_counts(G, &dummyA, &cbb);
    return (long)(G - ca) + (long)(G - cb) + (long)(G - cbb);
}

static void clear_S(void) {
    for (int i = 0; i < DEG; i++) inS[S[i]] = 0;
}

static void random_S(void) {
    clear_S();
    for (int i = 0; i < DEG; i++) {
        int x;
        do { x = rnd(G); } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
        invS[i] = ginv(x);
    }
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    M = atoi(argv[5]);
    K = atoi(argv[6]);
    int R = atoi(argv[7]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || M < 2 || K < 1 || K > 63 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = M * K;
    if (G > MAXG || G <= DEG) {
        printf("0 0\n");
        return 0;
    }
    {
        int a = R, b = M;
        while (b) {
            int t = a % b;
            a = b;
            b = t;
        }
        if (a != 1) {
            printf("0 0\n");
            return 0;
        }
    }
    pw[0] = 1 % M;
    for (int b = 1; b < K; b++) pw[b] = (pw[b - 1] * R) % M;
    if ((pw[K - 1] * R) % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    memset(inS, 0, sizeof inS);
    memset(S, 0, sizeof S);
    random_S();
    long cur = cost();
    long bestc = cur;
    double tstart = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    long it = 0, stall = 0;
    const long stallLim = 6000;

    while (cur > 0) {
        if ((it & 127) == 0) {
            double el = (double)clock() / CLOCKS_PER_SEC - tstart;
            frac = el / tl;
            if (frac >= 1.0) break;
        }
        it++;
        double T = 0.15 + 1.5 * (1.0 - frac);
        int i = rnd(DEG);
        int x;
        do { x = rnd(G); } while (inS[x]);
        int old = S[i];
        inS[old] = 0;
        inS[x] = 1;
        S[i] = x;
        invS[i] = ginv(x);
        long c2 = cost();
        long dl = c2 - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                stall = 0;
            } else {
                stall++;
            }
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[i] = old;
            invS[i] = ginv(old);
            stall++;
        }
        if (stall > stallLim) {
            random_S();
            cur = cost();
            bestc = cur;
            stall = 0;
        }
    }

    if (cur == 0) {
        printf("%d %d\n", 2 * G, G * DEG);
        for (int g = 0; g < G; g++)
            for (int i = 0; i < DEG; i++)
                printf("%d %d\n", g, G + gmul(g, S[i]));
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine 2 (kept from the parent): simulated annealing over general bipartite
# graphs, growing the best valid graph by one vertex whenever cost reaches 0.
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

/* Vertex-replace kick (structural): delete a random vertex v, move the last
   vertex into its index so indices stay contiguous, then grow a fresh vertex.
   Uses raw (unlogged) edits; the caller resets the log and re-evaluates. */
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


def _run_c(d, D, seed, graph, budget, stall=1500):
    """Run the C annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", stall],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def _group_candidates(G, rng):
    """Candidate groups of order G: two non-abelian semidirect products, then the cyclic group."""
    nonab = []
    for k in range(2, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            nonab.append((m, k, r))
    rng.shuffle(nonab)
    return nonab[:2] + [(G, 1, 1)]


def _bicayley_phase(d, D, rng, G, deadline):
    """Sweep the order G upward; for each G try candidate groups with the bi-Cayley annealer.

    Returns the largest valid graph found (n, edges), or None.
    """
    best = None
    tick = rng.randrange(1, 1 << 20)
    while deadline - time.monotonic() >= 1.0 and G <= 2000:
        for (m, k, r) in _group_candidates(G, rng):
            rem = deadline - time.monotonic()
            if rem < 1.0:
                break
            slice_s = min(1.5, rem)
            tick += 1
            try:
                out = lib.run_c(BC_SOURCE, [d, D, tick, f"{slice_s:.2f}", m, k, r],
                                timeout=slice_s + 4.0)
                n, e = lib.parse_graph_text(out)
            except Exception:
                continue
            if n > 0 and e and (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
                best = (n, e)
                break
        G += 1
    return best


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

    # D = 3 without the calibration: incidence graph of PG(2, q) for the largest prime power q <= d - 1.
    if D == 3 and d >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n0, e0 = lib.projective_plane_incidence(q)
                consider(n0, e0)
                break

    # D >= 4: generalized quadrangle W(q), saturated with spare degree.
    sat = None
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            sat_e = _saturate_edges(gq[0], gq[1], d, rng)
            sat = (gq[0], sat_e)
            consider(sat[0], sat[1])

    # Bold new construction for D = 4: bi-Cayley graphs over non-abelian groups.
    if D == 4 and d >= 5:
        found = _bicayley_phase(d, D, rng, best_n // 2 + 1, start + 0.36 * tl)
        if found is not None:
            consider(found[0], found[1])

    # C annealing from the best valid graph, then from the saturated quadrangle.
    if D >= 4 and d >= 5:
        end = start + 0.93 * tl - 1.5
        starts_c = [best]
        if sat is not None and sat is not best:
            starts_c.append(sat)
        for idx, g in enumerate(starts_c):
            remaining = end - time.monotonic()
            if remaining < 2.0:
                break
            share = 0.65 if (idx == 0 and len(starts_c) > 1) else 1.0
            budget = remaining * share
            try:
                n2, e2 = _run_c(d, D, seed + idx, g, budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
