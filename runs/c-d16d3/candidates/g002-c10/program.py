import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW 32
#define MAXLOG 64

typedef uint64_t Row[MAXW];

static int n, d, D, W;
static int deg[MAXN], nb[MAXN][MAXD], col[MAXN];
static Row P1[MAXN], P2[MAXN];
static int bestn = 0;
static int bdeg[MAXN], bnb[MAXN][MAXD], bcol[MAXN];
static uint64_t rs = 88172645463325252ULL;
static int logging = 0, logn = 0;
static int logt[MAXLOG], logu[MAXLOG], logv[MAXLOG];

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double runif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int adj(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (nb[u][i] == v) return 1;
    return 0;
}
static void raw_add(int u, int v) { nb[u][deg[u]++] = v; nb[v][deg[v]++] = u; }
static void raw_del(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; break; }
    for (int i = 0; i < deg[v]; i++) if (nb[v][i] == u) { nb[v][i] = nb[v][--deg[v]]; break; }
}
static void log_op(int t, int u, int v) {
    if (logging && logn < MAXLOG) { logt[logn] = t; logu[logn] = u; logv[logn] = v; logn++; }
}
static void add_edge(int u, int v) { raw_add(u, v); log_op(1, u, v); }
static void del_edge(int u, int v) { raw_del(u, v); log_op(0, u, v); }
static void undo(void) {
    int was = logging;
    logging = 0;
    for (int i = logn - 1; i >= 0; i--) {
        if (logt[i]) raw_del(logu[i], logv[i]); else raw_add(logu[i], logv[i]);
    }
    logn = 0;
    logging = was;
}

/* Bitmask of vertices within distance R of each vertex. */
static Row *ball(int R) {
    Row *cur = P1, *nxt = P2;
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], (size_t)W * 8);
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int k = 0; k < W; k++) nxt[v][k] |= cur[u][k];
            }
        }
        Row *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > D. Zero means valid. */
static long cost_full(void) {
    Row *B = ball(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < W; k++) c += pc64(B[v][k]);
        bad += n - c;
    }
    return bad / 2;
}

static void snapshot(void) {
    bestn = n;
    memcpy(bdeg, deg, sizeof deg);
    memcpy(bnb, nb, sizeof nb);
    memcpy(bcol, col, sizeof col);
}
static void restore(void) {
    n = bestn;
    memcpy(deg, bdeg, sizeof deg);
    memcpy(nb, bnb, sizeof nb);
    memcpy(col, bcol, sizeof col);
}

/* Insert a new vertex of colour `side` whose neighbourhood covers all old
   vertices within distance D-1. Keeps the graph valid. */
static int try_grow(int side) {
    Row *B = ball(D - 1);
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++) if (col[u] != side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int att = 0; att < 4; att++) {
        Row cov;
        char used[MAXN];
        int chosen[MAXD], nch = 0, covc = 0;
        memset(cov, 0, sizeof(Row));
        memset(used, 0, sizeof used);
        while (covc < n && nch < d) {
            int best = -1, bg = 0, start = rint_(nc);
            for (int t = 0; t < nc; t++) {
                int u = cand[(start + t) % nc];
                if (used[u]) continue;
                int g = 0;
                for (int k = 0; k < W; k++) g += pc64(B[u][k] & ~cov[k]);
                if (g > bg) { bg = g; best = u; }
            }
            if (best < 0) break;
            used[best] = 1;
            chosen[nch++] = best;
            covc = 0;
            for (int k = 0; k < W; k++) { cov[k] |= B[best][k]; covc += pc64(cov[k]); }
        }
        if (covc == n) {
            int w = n++;
            col[w] = side;
            deg[w] = 0;
            for (int i = 0; i < nch; i++) raw_add(w, chosen[i]);
            return 1;
        }
    }
    return 0;
}

static void move_addedge(void) {
    for (int t = 0; t < 30; t++) {
        int u = rint_(n), v = rint_(n);
        if (col[u] == col[v] || deg[u] >= d || deg[v] >= d || adj(u, v)) continue;
        add_edge(u, v);
        return;
    }
}

static void move_switch(void) {
    for (int t = 0; t < 30; t++) {
        int a = rint_(n), c = rint_(n);
        if (a == c || col[a] != 0 || col[c] != 0 || deg[a] == 0 || deg[c] == 0) continue;
        int b = nb[a][rint_(deg[a])], e = nb[c][rint_(deg[c])];
        if (b == e || adj(a, e) || adj(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        return;
    }
}

static void move_kick(void) {
    for (int t = 0; t < 30; t++) {
        int u = rint_(n);
        if (deg[u] == 0) continue;
        int v = nb[u][rint_(deg[u])];
        del_edge(u, v);
        return;
    }
}

static int read_graph(void) {
    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || n0 > MAXN || m0 < 0) return 0;
    n = n0;
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d || adj(u, v)) return 0;
        raw_add(u, v);
    }
    return 1;
}

static int color_graph(void) {
    static int q[MAXN];
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[t++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

static void output(void) {
    if (bestn <= 0) { printf("0 0\n"); return; }
    int m = 0;
    for (int u = 0; u < bestn; u++)
        for (int i = 0; i < bdeg[u]; i++) if (bnb[u][i] > u) m++;
    printf("%d %d\n", bestn, m);
    for (int u = 0; u < bestn; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (bnb[u][i] > u) printf("%d %d\n", u, bnb[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 0;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= 0x9E3779B97F4A7C15ULL * (uint64_t)(atoll(argv[3]) + 1);
    if (rs == 0) rs = 1;
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (!read_graph() || !color_graph()) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();
    long cost = cost_full();
    if (cost == 0) snapshot();
    long mincost = cost, stagn = 0, iter = 0;
    double T = 0.5;
    const long LIMIT = 3000;
    logging = 1;

    while (1) {
        if ((iter & 31) == 0) {
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > limit) break;
        }
        iter++;
        if (cost == 0) {
            if (n > bestn) snapshot();
            if (n < MAXN - 1 && try_grow(rint_(2))) {
                mincost = 0;
                stagn = 0;
                continue;
            }
        }
        logn = 0;
        int r = rint_(100);
        if (r < 30) move_addedge();
        else if (r < 97) move_switch();
        else move_kick();
        long nc = cost_full();
        if (nc <= cost || runif() < exp(-(double)(nc - cost) / T)) cost = nc;
        else undo();

        if (cost < mincost) { mincost = cost; stagn = 0; }
        else stagn++;

        if (stagn > LIMIT) {
            if (bestn > 0) restore();
            for (int k = 0; k < 3; k++) move_kick();
            cost = cost_full();
            mincost = cost;
            stagn = 0;
            T = 0.3 + 0.9 * runif();
        }
    }
    output();
    return 0;
}
"""


def _arc_extension(q, d, rng):
    """Arc-extended PG(2,q) graph for degree d (q+1 <= d). Returns (n, edges), or the plain
    incidence graph when there is no spare capacity."""
    s = d - q - 1
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    if s == 0:
        return n2, list(edges)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)

    def loads_ok(S):
        cl = [0] * m
        cp = [0] * m
        for P in S:
            for L in point_lines[P]:
                cl[L] += 1
            for Q in line_points[P]:
                cp[Q] += 1
        return max(cl) <= s and max(cp) <= s

    def greedy(trials):
        best = []
        order = list(range(m))
        for _ in range(trials):
            rng.shuffle(order)
            cl = [0] * m
            cp = [0] * m
            S = []
            for P in order:
                if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                    S.append(P)
                    for L in point_lines[P]:
                        cl[L] += 1
                    for Q in line_points[P]:
                        cp[Q] += 1
            if len(S) > len(best):
                best = S
        return best

    cands = []
    if s >= 1:
        cands.append(greedy(40))
    if s >= 2:
        F = lib.GF(q)
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        if loads_ok(cs):
            cands.append(cs)
    S = max(cands, key=len, default=[])
    if not S or not loads_ok(S):
        return n2, list(edges)

    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    deadline = t_start + time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or lib.moore_bound(d, D) <= best[0]:
        return best

    def consider(cand):
        nonlocal best
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Seed: arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            if time.monotonic() > t_start + 0.2 * time_limit:
                break
            consider(_arc_extension(q, d, rng))

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Main search: C engine that grows the graph by covering insertions and
    # repairs bad pairs with degree-preserving 2-switches and annealing.
    remaining = deadline - time.monotonic()
    if d <= 60 and best[0] <= 1500 and remaining > 8:
        budget = max(1.0, remaining * 0.75 - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=remaining * 0.9)
            consider(lib.parse_graph_text(out))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
