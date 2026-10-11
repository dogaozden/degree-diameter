import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: incremental "grow and anneal" search.
#
# New idea in this version: the engine keeps a valid graph, adds one vertex
# (taking its d neighbours from the other side, evicting an existing edge when
# the other side is full), then runs simulated annealing on degree-preserving
# bipartite double-edge switches. Switches are biased toward vertices that
# currently miss pairs at distance <= D. If annealing reaches cost 0 the graph
# is valid and the search grows again. Otherwise it rolls back to the last
# valid snapshot. The cost (number of pairs at distance > D) is computed with
# bitset ball expansion.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXDEG 24
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2 + 8)

typedef struct {
    int n;
    int col[MAXN];
    int m;
    int eu[MAXE];
    int ev[MAXE];
} Graph;

static int d, D;
static int n;
static int col[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static unsigned char A[MAXN][MAXN];
static int sideList[2][MAXN];
static int nside[2];
static int badv[MAXN];
static int tmpSide[MAXN];
static uint64_t ballA[MAXN][MAXW];
static uint64_t ballB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double tEnd;
static Graph best, snap;

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D (unreachable pairs included). Fills badv. */
static long cost_bad(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = ballA;
    uint64_t (*nxt)[MAXW] = ballB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * MAXW);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad2 = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        badv[v] = n - c;
        bad2 += n - c;
    }
    return bad2 / 2;
}

static void rem_from(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void add_edge(int u, int v) {
    A[u][v] = 1;
    A[v][u] = 1;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    A[u][v] = 0;
    A[v][u] = 0;
    rem_from(u, v);
    rem_from(v, u);
}

static void assign_sides(void) {
    static int queue[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (col[y] == -1) {
                    col[y] = 1 - col[x];
                    queue[qt++] = y;
                }
            }
        }
    }
    nside[0] = nside[1] = 0;
    for (int v = 0; v < n; v++) sideList[col[v]][nside[col[v]]++] = v;
}

static void capture(Graph *g) {
    g->n = n;
    g->m = 0;
    for (int v = 0; v < n; v++) {
        g->col[v] = col[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v && g->m < MAXE) {
                g->eu[g->m] = v;
                g->ev[g->m] = u;
                g->m++;
            }
        }
    }
}

/* Replace the current state by a stored graph. */
static void load(const Graph *g) {
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) A[v][adj[v][k]] = 0;
        deg[v] = 0;
    }
    n = g->n;
    for (int v = 0; v < n; v++) {
        col[v] = g->col[v];
        deg[v] = 0;
    }
    nside[0] = nside[1] = 0;
    for (int v = 0; v < n; v++) sideList[col[v]][nside[col[v]]++] = v;
    for (int i = 0; i < g->m; i++) add_edge(g->eu[i], g->ev[i]);
}

/* Add one vertex with up to d neighbours on the opposite side. */
static void grow_vertex(void) {
    if (n >= MAXN - 2) return;
    int c = rint_(2);
    int o = 1 - c;
    int v = n++;
    col[v] = c;
    deg[v] = 0;
    sideList[c][nside[c]++] = v;
    int m = nside[o];
    for (int i = 0; i < m; i++) tmpSide[i] = sideList[o][i];
    for (int i = m - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = tmpSide[i];
        tmpSide[i] = tmpSide[j];
        tmpSide[j] = t;
    }
    int need = d;
    if (need > m) need = m;
    /* First pass: join deficient vertices. */
    for (int i = 0; i < m && need > 0; i++) {
        int b = tmpSide[i];
        if (deg[b] < d) {
            add_edge(v, b);
            need--;
        }
    }
    /* Second pass: evict one random edge of a full vertex. */
    for (int i = 0; i < m && need > 0; i++) {
        int b = tmpSide[i];
        if (A[v][b]) continue;
        if (deg[b] >= d) {
            int x = adj[b][rint_(deg[b])];
            del_edge(b, x);
        }
        add_edge(v, b);
        need--;
    }
}

/* Add cross edges between deficient vertices (only helps distances). */
static void fill(void) {
    for (int i = 0; i < nside[0]; i++) {
        int x = sideList[0][i];
        for (int j = 0; j < nside[1] && deg[x] < d; j++) {
            int y = sideList[1][j];
            if (deg[y] < d && !A[x][y]) add_edge(x, y);
        }
    }
}

/* Pick a degree-preserving double-edge switch a-b, c-e -> a-e, c-b on one side. */
static int try_switch(int *pa, int *pb, int *pc, int *pe) {
    for (int t = 0; t < 40; t++) {
        int s = rint_(2);
        int m = nside[s];
        if (m < 2) continue;
        int a = sideList[s][rint_(m)];
        if (rnd() & 1) {
            for (int q = 0; q < 6; q++) {
                int cand = sideList[s][rint_(m)];
                if (badv[cand] > 0 && deg[cand] > 0) {
                    a = cand;
                    break;
                }
            }
        }
        if (deg[a] == 0) continue;
        int b = adj[a][rint_(deg[a])];
        int c = sideList[s][rint_(m)];
        if (c == a || deg[c] == 0) continue;
        int e = adj[c][rint_(deg[c])];
        if (A[a][e] || A[c][b]) continue;
        *pa = a;
        *pb = b;
        *pc = c;
        *pe = e;
        return 1;
    }
    return 0;
}

/* Annealing over switches. Returns 1 iff cost reaches 0 (state is then valid). */
static int anneal(long iters, double T0, double T1) {
    long cur = cost_bad();
    if (cur == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now_sec() > tEnd) break;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        int a, b, c, e;
        if (!try_switch(&a, &b, &c, &e)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost_bad();
        long delta = nw - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double t0 = now_sec();
    tEnd = t0 + budget;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG - 2 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    static int ru[MAXE], rv[MAXE];
    int in_n = 0, in_m = 0;
    if (scanf("%d %d", &in_n, &in_m) != 2) {
        in_n = 0;
        in_m = 0;
    }
    int rm = 0;
    if (in_n > 0 && in_n < MAXN) {
        for (int i = 0; i < in_m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (rm < MAXE && u >= 0 && v >= 0 && u < in_n && v < in_n && u != v) {
                ru[rm] = u;
                rv[rm] = v;
                rm++;
            }
        }
    }
    if (in_n == 0) {
        /* Fallback start: K_{d,d}. */
        in_n = 2 * d;
        rm = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                ru[rm] = i;
                rv[rm] = d + j;
                rm++;
            }
    }

    /* Build the start graph, skipping edges that would break the degree bound. */
    n = in_n;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) A[v][adj[v][k]] = 0;
        deg[v] = 0;
    }
    for (int i = 0; i < rm; i++) {
        int u = ru[i], v = rv[i];
        if (A[u][v] || deg[u] >= d || deg[v] >= d) continue;
        add_edge(u, v);
    }
    assign_sides();
    capture(&snap);

    int ok0 = (cost_bad() == 0);
    int usable = 0;
    if (ok0) {
        capture(&best);
        usable = 1;
    } else {
        while (now_sec() < tEnd) {
            if (anneal(20000, 0.5, 0.05)) {
                usable = 1;
                break;
            }
        }
        if (usable) {
            capture(&snap);
            capture(&best);
        }
    }

    if (usable) {
        int fails = 0;
        while (now_sec() < tEnd && n < MAXN - 3) {
            grow_vertex();
            fill();
            long L = 4000 + 1000L * (long)(fails < 40 ? fails : 40);
            if (anneal(L, 0.6, 0.04)) {
                capture(&snap);
                fails = 0;
                if (n > best.n) capture(&best);
            } else {
                load(&snap);
                fails++;
            }
        }
    }

    Graph *out = (best.n > 0) ? &best : &snap;
    printf("%d %d\n", out->n, out->m);
    for (int i = 0; i < out->m; i++) printf("%d %d\n", out->eu[i], out->ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (starting points for the C engine).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2 and is always valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    cands = []
    if D >= 4:
        cands.append(_best_gq(d))
    if D >= 3:
        cands.append(_best_pg(d))
    for c in cands:
        if c is None:
            continue
        n, e = c
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    remaining = time_limit - (time.monotonic() - t0)
    budget = max(0.2, 0.9 * remaining - 0.5)
    timeout = min(remaining * 0.95, budget + 1.0)
    if timeout > 0.5:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                            stdin_graph=(best_n, best_e), timeout=timeout)
            n, e = lib.parse_graph_text(out)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
