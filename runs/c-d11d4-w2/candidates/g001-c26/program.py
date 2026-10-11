import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: targeted vertex insertion plus annealing repair.
#
# Cost = number of unordered vertex pairs at distance > DIAM (bitset balls).
# When cost is 0 the state is saved and a new vertex is inserted. Its neighbours
# are chosen greedily to cover the most still-unreached vertices, using radius
# DIAM-1 balls of the candidates. Annealing (swap and relocate moves, undone
# exactly through an edit log) then repairs any leftover bad pairs. Stalls
# restart from the best valid graph.
# ----------------------------------------------------------------------------

C_INSERT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4000
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define LOGMAX 4096

static int DEG, DIAM, nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int bAdj[MAXN][DEGMAX];
static int bDeg[MAXN];
static int bCol[MAXN];
static int bNv = 0;
static uint64_t BR[MAXN * WMAX];
static uint64_t BR1[MAXN * WMAX];
static uint64_t TA[MAXN * WMAX];
static uint64_t TB[MAXN * WMAX];
static uint64_t rs = 1;
static int stk[MAXN];
static int defi[MAXN], fulli[MAXN], selmark[MAXN];
static int logOp[LOGMAX], logA[LOGMAX], logB[LOGMAX];
static int logN = 0;

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

/* Bitset balls: BR = radius DIAM, BR1 = radius DIAM-1. */
static void compute_balls(void) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = TA, *nxt = TB, *t;
    memset(cur, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        if (r == DIAM - 1)
            memcpy(BR1, cur, sizeof(uint64_t) * (size_t)nv * (size_t)W);
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    memcpy(BR, cur, sizeof(uint64_t) * (size_t)nv * (size_t)W);
}

static long long badcount(void) {
    int W = (nv + 63) >> 6;
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        const uint64_t *s = BR + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += nv - cnt;
    }
    return bad / 2;
}

/* Insert a new vertex of colour c. Neighbours: greedy max coverage of
   still-unreached vertices, using deficient opposite-side candidates only. */
static void insert_vertex(int c) {
    int W = (nv + 63) >> 6;
    uint64_t U[WMAX];
    memset(U, 0, sizeof(U));
    memset(selmark, 0, sizeof(int) * (size_t)nv);
    int chosen[DEGMAX];
    int k = 0;
    for (int step = 0; step < DEG; step++) {
        int best = -1, bestg = -1, ties = 0;
        for (int s = 0; s < nv; s++) {
            if (col[s] != 1 - c || selmark[s] || deg[s] >= DEG) continue;
            const uint64_t *b = BR1 + (size_t)s * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(b[w] & ~U[w]);
            if (g > bestg) {
                bestg = g;
                best = s;
                ties = 1;
            } else if (g == bestg) {
                ties++;
                if (rnd(ties) == 0) best = s;
            }
        }
        if (best < 0) break;
        selmark[best] = 1;
        chosen[k++] = best;
        const uint64_t *b = BR1 + (size_t)best * W;
        for (int w = 0; w < W; w++) U[w] |= b[w];
    }
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    for (int i = 0; i < k; i++) raw_add(v, chosen[i]);
}

static void save_best(void) {
    memcpy(bAdj, adjv, sizeof adjv);
    memcpy(bDeg, deg, sizeof deg);
    memcpy(bCol, col, sizeof col);
    bNv = nv;
}

static void restore_best(void) {
    memcpy(adjv, bAdj, sizeof adjv);
    memcpy(deg, bDeg, sizeof deg);
    memcpy(col, bCol, sizeof col);
    nv = bNv;
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
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [stall]\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long stallLim = 3000;
    if (argc >= 6) stallLim = atol(argv[5]);
    if (stallLim < 50) stallLim = 50;
    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
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
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < deg[v]; i++)
            if (col[adjv[v][i]] == col[v]) {
                printf("0 0\n");
                return 0;
            }

    compute_balls();
    long long cur = badcount();
    if (cur == 0) save_best();

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;
    logN = 0;

    while (1) {
        double el = (double)clock() / CLOCKS_PER_SEC - t0;
        if (el >= tl) break;
        double frac = el / tl;

        if (cur == 0) {
            if (nv > bNv) save_best();
            if (nv + 1 >= MAXN) break;
            insert_vertex(rnd(2));
            compute_balls();
            cur = badcount();
            stall = 0;
            logN = 0;
            continue;
        }

        double T = 0.08 + 0.3 * (1.0 - frac);
        int ok = (rnd01() < 0.5) ? swap_move() : relocate_move();
        if (!ok) {
            logN = 0;
            continue;
        }
        compute_balls();
        long long c2 = badcount();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
            logN = 0;
        } else {
            undo_log();
        }

        if (++stall > stallLim) {
            if (bNv > 0) {
                restore_best();
                logN = 0;
                compute_balls();
                cur = badcount();
            }
            stall = 0;
        }
    }

    if (cur == 0 && nv > bNv) save_best();
    if (bNv <= 0) {
        printf("0 0\n");
        return 0;
    }
    long long em = 0;
    for (int v = 0; v < bNv; v++) em += bDeg[v];
    printf("%d %lld\n", bNv, em / 2);
    for (int v = 0; v < bNv; v++)
        for (int i = 0; i < bDeg[v]; i++)
            if (v < bAdj[v][i]) printf("%d %d\n", v, bAdj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions.
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (keeps bipartiteness)."""
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

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
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Bases: projective planes (D = 3) and the generalized quadrangle (D >= 4),
    # each also saturated so that spare degree is used.
    bases = []
    if D == 3:
        for q in [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]:
            bases.append(lib.projective_plane_incidence(q))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)
    for n, e in bases:
        consider(n, e)
        if time.monotonic() - start < 0.3 * tl:
            consider(n, _saturate_edges(n, e, d, rng))

    # Main phase: targeted insertion with annealing repair in C, from the best valid graph.
    if D >= 2 and d >= 3:
        end = start + 0.92 * tl - 2.0
        remaining = end - time.monotonic()
        if remaining >= 3.0:
            try:
                out = lib.run_c(C_INSERT, [d, D, seed, f"{remaining:.2f}", 4000],
                                stdin_graph=(best_n, best_e), timeout=remaining + 6.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
