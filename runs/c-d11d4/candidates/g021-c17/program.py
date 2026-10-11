import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing over bipartite graphs with two moves
# (swap and relocate). Cost = number of pairs at distance > DIAM. Once cost is
# 0 the state is saved and grown by one vertex. Used to grow a valid start graph.
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
# C engine 2: voltage-lift annealer over semidirect groups Z_M x| Z_K2.
#
# Base: K left + K right vertices, d-regular multigraph given by d random
# permutations (dart (j, u) joins left u to right perm[j][u]). Each dart has a
# group voltage. Lift: left (u, x) joins right (t, x*g). Left multiplication by
# a group element is an automorphism, so distances from (u, x) equal those from
# (u, identity). Cost = sum over the 2K base sources of vertices not within
# DIAM, plus a large penalty for parallel lift edges (equal voltages on
# parallel darts). Prints the lift on cost 0, otherwise "0 0".
# Args: d DIAM seed time K M K2 R.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 6000
#define MAXD 32
#define MAXK 24
#define PEN 1000LL
#define STALL 4000

static int d, DIAM, K, M, K2, R, G, NV;
static int pw[256];
static int perm[MAXD][MAXK];
static int volt[MAXD][MAXK];
static int adjv[MAXV][MAXD];
static int degc[MAXV];
static int distv[MAXV], qv[MAXV];
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

/* Semidirect product Z_M x| Z_K2: (a,b)(c,e) = (a + r^b c, b + e), element = a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int aa = (a + pw[b] * c) % M;
    return aa * K2 + (b + e) % K2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int aa = (M - (pw[nb] * a) % M) % M;
    return aa * K2 + nb;
}

static void build(void) {
    NV = 2 * K * G;
    for (int v = 0; v < NV; v++) degc[v] = 0;
    for (int j = 0; j < d; j++)
        for (int u = 0; u < K; u++) {
            int t = perm[j][u];
            int g = volt[j][u];
            for (int x = 0; x < G; x++) {
                int L = u * G + x;
                int Rv = (K + t) * G + gmul(x, g);
                adjv[L][degc[L]++] = Rv;
                adjv[Rv][degc[Rv]++] = L;
            }
        }
}

static long long dup_count(void) {
    long long c = 0;
    for (int u = 0; u < K; u++)
        for (int j1 = 0; j1 < d; j1++)
            for (int j2 = j1 + 1; j2 < d; j2++)
                if (perm[j1][u] == perm[j2][u] && volt[j1][u] == volt[j2][u]) c++;
    return c;
}

static long long eval_cost(void) {
    build();
    long long T = 0;
    for (int s0 = 0; s0 < 2 * K; s0++) {
        int src = s0 * G;
        for (int v = 0; v < NV; v++) distv[v] = -1;
        int head = 0, tail = 0;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= DIAM) continue;
            for (int i = 0; i < d; i++) {
                int w = adjv[v][i];
                if (distv[w] < 0) {
                    distv[w] = dv + 1;
                    qv[tail++] = w;
                }
            }
        }
        T += NV - tail;
    }
    return T + PEN * dup_count();
}

static void randomize_state(void) {
    for (int j = 0; j < d; j++) {
        for (int u = 0; u < K; u++) perm[j][u] = u;
        for (int u = K - 1; u > 0; u--) {
            int k = rnd(u + 1);
            int t = perm[j][u];
            perm[j][u] = perm[j][k];
            perm[j][k] = t;
        }
        for (int u = 0; u < K; u++) volt[j][u] = rnd(G);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 1 || d > MAXD || DIAM < 1 || K < 1 || K > MAXK || M < 1 || K2 < 1 || K2 > 255 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (2 * K * G > MAXV) {
        printf("0 0\n");
        return 0;
    }
    R %= M;
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * R) % M;

    randomize_state();
    long long cur = eval_cost();
    long long stall = 0;
    clock_t c0 = clock();

    while (cur > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        double frac = el / tl;
        double T = 1.2 * (1.0 - frac) + 0.05;
        int j = rnd(d), u = rnd(K);
        int old = volt[j][u];
        int nw = rnd(G);
        if (nw == old) continue;
        volt[j][u] = nw;
        long long c2 = eval_cost();
        long long dl = c2 - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = c2;
            stall = 0;
        } else {
            volt[j][u] = old;
            stall++;
        }
        if (stall > STALL) {
            randomize_state();
            cur = eval_cost();
            stall = 0;
        }
    }

    if (cur == 0) {
        build();
        long long m = (long long)K * G * d;
        printf("%d %lld\n", NV, m);
        for (int L = 0; L < K * G; L++)
            for (int i = 0; i < d; i++)
                printf("%d %d\n", L, adjv[L][i]);
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
    """Greedily join deficient opposite-side vertices in random order (keeps D and bipartiteness)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            out.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return out


def _lift_candidates(d, D, min_n, max_n, rng, limit=400):
    """Semidirect-lift parameters (n, K, M, K2, R) with n in [min_n, max_n], smallest n first."""
    out = []
    for K in range(1, min(d, 12) + 1):
        G0 = max(1, -(-min_n // (2 * K)))
        for G in range(G0, G0 + 4):
            n = 2 * K * G
            if n > max_n:
                break
            for k2 in range(1, min(12, G) + 1):
                if G % k2:
                    continue
                m = G // k2
                if m == 1:
                    choices = [0]
                elif k2 == 1:
                    choices = [1]
                else:
                    valid = [r for r in range(1, m)
                             if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
                    if not valid:
                        continue
                    choices = [1]
                    extra = rng.choice(valid)
                    if extra != 1:
                        choices.append(extra)
                for r in choices:
                    out.append((n, K, m, k2, r))
    rng.shuffle(out)
    out.sort(key=lambda t: t[0])
    return out[:limit]


def _run_lift(d, D, seed, K, m, k2, r, budget):
    """Run the C voltage-lift annealer; return parsed (n, edges), with n = 0 if it found nothing."""
    out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{budget:.2f}", K, m, k2, r],
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

    # Safe fallback: K_{d,d}, valid for D >= 2 (and d = 1 gives one edge).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured starts: projective plane for D = 3, generalized quadrangle for D >= 4.
    starts = []
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            starts.append(lib.projective_plane_incidence(qs[0]))
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    sat_graphs = []
    for n0, e0 in starts:
        consider(n0, e0)
        sat_graphs.append((n0, _saturate_edges(n0, e0, d, rng)))
    for n0, e0 in sat_graphs:
        consider(n0, e0)

    # New stage: voltage lifts over semidirect groups, searched in C.
    # Candidates are tried from the smallest order above the current best upward,
    # so each success raises the bar for the next attempt.
    if D >= 3 and d >= 3:
        lift_end = start + 0.45 * tl
        max_n = min(lib.moore_bound(d, D), 5000)
        cands = _lift_candidates(d, D, best_n + 1, max_n, rng)
        for n_c, K, m, k2, r in cands:
            if n_c <= best_n:
                continue
            remaining = lift_end - time.monotonic()
            if remaining < 1.0:
                break
            try:
                n2, e2 = _run_lift(d, D, rng.randrange(1 << 30), K, m, k2, r,
                                   min(2.5, remaining))
            except Exception:
                continue
            if n2 > 0:
                consider(n2, e2)

    # Vertex annealing: grow from the best valid graph, then from the saturated start.
    end = start + 0.88 * tl - 1.0
    runs = [best]
    if sat_graphs:
        runs.append(sat_graphs[0])
    for idx, g in enumerate(runs):
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        share = 0.6 if (idx == 0 and len(runs) > 1) else 1.0
        try:
            n2, e2 = _run_c(d, D, seed + idx, g, remaining * share)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
