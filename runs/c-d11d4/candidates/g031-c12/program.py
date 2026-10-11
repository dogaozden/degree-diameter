import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage lifts over semidirect products Z_m x| Z_k2 with K base
# vertices per side and DEG darts per base vertex.
#
# Lifted vertex (i, x) for an A-side base vertex i (or B-side base vertex
# K + j) and group element x. Dart t at base vertex i goes to base vertex
# P[t][i] with voltage V[t][i]: (i, x) ~ (P[t][i], x * V[t][i]).
# Left translation is an automorphism, so the bad-pair count is
#     G * sum over the 2K base representatives of (unreached vertices) / 2,
# which needs only 2K BFS runs per evaluation. Moves: change a voltage, or swap
# two images inside one permutation. Simulated annealing; prints the lift as
# soon as its cost reaches 0, otherwise "0 0".
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXG 1024
#define MAXD 32
#define MAXN (2 * MAXK * MAXG)
#define STALL 20000

static int DEG, DIAM, K, G, K2, RR, NN;
static int MT[MAXG][MAXG];
static int P[MAXD][MAXK], V[MAXD][MAXK];
static int bestP[MAXD][MAXK], bestV[MAXD][MAXK];
static int adjL[MAXN][MAXD];
static int ac[MAXN];
static int distv[MAXN], qbuf[MAXN];
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

/* Multiplication table of Z_m x|_r Z_k2, element (a,b) coded a*k2+b. */
static void build_group(void) {
    int m = G / K2;
    static int pw[MAXG];
    int r = RR % m;
    pw[0] = 1 % m;
    for (int b = 1; b < K2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
    for (int x = 0; x < G; x++) {
        int a1 = x / K2, b1 = x % K2;
        for (int y = 0; y < G; y++) {
            int c = y / K2, e = y % K2;
            int a = (int)((a1 + (long long)pw[b1] * c) % m);
            int b = (b1 + e) % K2;
            MT[x][y] = a * K2 + b;
        }
    }
}

static void random_state(void) {
    for (int t = 0; t < DEG; t++) {
        for (int i = 0; i < K; i++) P[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmp = P[t][i];
            P[t][i] = P[t][j];
            P[t][j] = tmp;
        }
        for (int i = 0; i < K; i++) V[t][i] = rnd(G);
    }
}

static void build_adj(void) {
    for (int v = 0; v < NN; v++) ac[v] = 0;
    for (int t = 0; t < DEG; t++) {
        for (int i = 0; i < K; i++) {
            int ib = i * G;
            int jb = (K + P[t][i]) * G;
            int g = V[t][i];
            for (int x = 0; x < G; x++) {
                int a = ib + x;
                int b = jb + MT[x][g];
                adjL[a][ac[a]++] = b;
                adjL[b][ac[b]++] = a;
            }
        }
    }
}

/* Bad ordered pairs / 2, using the 2K base representatives (identity coset). */
static long long cost_fn(void) {
    build_adj();
    long long sum = 0;
    for (int s = 0; s < 2 * K; s++) {
        int src = s * G;
        for (int v = 0; v < NN; v++) distv[v] = -1;
        int qh = 0, qt = 0;
        qbuf[qt++] = src;
        distv[src] = 0;
        while (qh < qt) {
            int u = qbuf[qh++];
            int du = distv[u];
            if (du >= DIAM) continue;
            for (int k = 0; k < ac[u]; k++) {
                int w = adjL[u][k];
                if (distv[w] < 0) {
                    distv[w] = du + 1;
                    qbuf[qt++] = w;
                }
            }
        }
        sum += NN - qt;
    }
    return (long long)G * sum / 2;
}

static int dup_dart(int t, int i) {
    for (int s = 0; s < t; s++)
        if (bestP[s][i] == bestP[t][i] && bestV[s][i] == bestV[t][i]) return 1;
    return 0;
}

static void print_best(void) {
    int n = 2 * K * G;
    long long cnt = 0;
    for (int t = 0; t < DEG; t++)
        for (int i = 0; i < K; i++)
            if (!dup_dart(t, i)) cnt += G;
    printf("%d %lld\n", n, cnt);
    for (int t = 0; t < DEG; t++)
        for (int i = 0; i < K; i++) {
            if (dup_dart(t, i)) continue;
            for (int x = 0; x < G; x++) {
                int a = i * G + x;
                int b = (K + bestP[t][i]) * G + MT[x][bestV[t][i]];
                printf("%d %d\n", a, b);
            }
        }
}

static void save_best(void) {
    memcpy(bestP, P, sizeof P);
    memcpy(bestV, V, sizeof V);
}

static void restore_best(void) {
    memcpy(P, bestP, sizeof P);
    memcpy(V, bestV, sizeof V);
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
    K = atoi(argv[5]);
    G = atoi(argv[6]);
    K2 = atoi(argv[7]);
    RR = atoi(argv[8]);
    if (DEG < 1 || DEG > MAXD || DIAM < 1 || K < 1 || K > MAXK || G < 2 || G > MAXG ||
        K2 < 1 || K2 > G || G % K2 != 0 || G / K2 < 2 || RR < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    build_group();
    NN = 2 * K * G;
    random_state();
    long long cur = cost_fn();
    long long best = cur;
    save_best();
    int found = (cur == 0);

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    double frac = 0.0;
    long long it = 0, stall = 0;
    while (!found) {
        if ((it & 31) == 0) {
            frac = ((double)clock() / CLOCKS_PER_SEC - t0) / tl;
            if (frac >= 1.0) break;
        }
        it++;
        int kind = 0;
        int t = rnd(DEG), i = rnd(K), i2 = 0, oldv = 0;
        if (K >= 2 && rnd(10) < 3) {
            kind = 1;
            i2 = rnd(K - 1);
            if (i2 >= i) i2++;
            int tmp = P[t][i];
            P[t][i] = P[t][i2];
            P[t][i2] = tmp;
        } else {
            oldv = V[t][i];
            int nvv = rnd(G);
            if (G > 1)
                while (nvv == oldv) nvv = rnd(G);
            V[t][i] = nvv;
        }
        long long c2 = cost_fn();
        double T = (double)G * (0.8 * (1.0 - frac) + 0.03);
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else if (kind == 1) {
            int tmp = P[t][i];
            P[t][i] = P[t][i2];
            P[t][i2] = tmp;
        } else {
            V[t][i] = oldv;
        }
        if (cur == 0) {
            found = 1;
            save_best();
            break;
        }
        if (cur < best) {
            best = cur;
            save_best();
            stall = 0;
        } else {
            stall++;
        }
        if (stall > STALL) {
            restore_best();
            for (int k = 0; k < 3; k++) {
                int tt = rnd(DEG), ii = rnd(K);
                V[tt][ii] = rnd(G);
            }
            cur = cost_fn();
            stall = 0;
        }
    }
    if (found) print_best();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: simulated annealing over bipartite graphs (the parent's engine,
# used as the final polish from the best valid graph found so far).
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
    """W(q) for the largest prime power q <= min(d - 1, 9) (keeps the Python build fast)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _twin_grow(n, edges, d, rng, deadline):
    """Add twins (same side, same neighbourhood) while all neighbours have spare degree.

    A twin keeps all old distances and bipartiteness.
    """
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
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


def _lift_configs(lo, hi, rng):
    """Lift parameters (n, K, G, k2, r) with lo <= n <= hi, sorted by n.

    n = 2 * K * G, where G = m * k2 is the group order (Z_m x| Z_k2 with r^k2 = 1 mod m).
    """
    out = []
    for K in range(1, 9):
        g_lo = max(2, -(-lo // (2 * K)))
        g_hi = min(1024, hi // (2 * K))
        for G in range(g_lo, g_hi + 1):
            n = 2 * K * G
            for k2 in range(1, min(G, 12) + 1):
                if G % k2:
                    continue
                m = G // k2
                if m < 2:
                    continue
                if k2 == 1:
                    out.append((n, K, G, 1, 1))
                    continue
                rr = [r for r in range(1, m)
                      if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
                rng.shuffle(rr)
                for r in rr[:2]:
                    out.append((n, K, G, k2, r))
    rng.shuffle(out)
    out.sort(key=lambda c: c[0])
    return out


def _lift_search(d, D, lo, deadline, rng, consider):
    """Run the C lift annealer over candidate parameters; ratchet lo upward on success."""
    while True:
        left = deadline - time.monotonic()
        if left < 1.0:
            return
        cfgs = _lift_configs(lo, lo + 40, rng)
        if not cfgs:
            return
        per = max(1.0, left / 12.0)
        success = False
        for n, K, G, k2, r in cfgs:
            left = deadline - time.monotonic()
            if left < 1.0:
                return
            budget = min(per, left - 0.5)
            if budget < 0.5:
                return
            try:
                out = lib.run_c(C_LIFT, [d, D, rng.randrange(1 << 30), f"{budget:.2f}", K, G, k2, r],
                                timeout=budget + 4.0)
                n2, e2 = lib.parse_graph_text(out)
            except Exception:
                continue
            if n2 > 0 and consider(n2, e2):
                lo = n2 + 2
                success = True
                break
        if not success:
            return


def _run_anneal(d, D, seed, graph, budget, stall=1500):
    """Run the C annealer from `graph` for `budget` seconds; return the parsed (n, edges)."""
    out = lib.run_c(C_ANNEAL, [d, D, seed, f"{budget:.2f}", stall],
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
            return True
        return False

    # Stage 1: structured seed (generalized quadrangle or projective plane), twin growth, saturation.
    seed_graph = None
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                seed_graph = lib.projective_plane_incidence(q)
                break
    elif D >= 4:
        seed_graph = _best_gq(d)
    if seed_graph is not None:
        n0, e0 = seed_graph
        consider(n0, e0)
        tn, te = _twin_grow(n0, e0, d, rng, start + 0.10 * tl)
        consider(tn, te)
        consider(tn, _saturate_edges(tn, te, d, rng))

    # Stage 2 (new construction): voltage lifts over semidirect products, searched in C.
    lift_end = start + 0.42 * tl
    if d >= 3 and D >= 3 and time.monotonic() < lift_end - 2.0:
        moore = lib.moore_bound(d, D)
        lo = int(0.78 * moore)
        if lo < best_n + 2 or lo > 1.15 * best_n + 2:
            lo = best_n + 2
        _lift_search(d, D, lo, lift_end, rng, consider)

    # Stage 3: C annealing from the best valid graph, using the remaining budget.
    end = start + 0.93 * tl - 1.5
    remaining = end - time.monotonic()
    if remaining > 2.0:
        try:
            n2, e2 = _run_anneal(d, D, seed, best, remaining)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
