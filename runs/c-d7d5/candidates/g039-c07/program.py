import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as safe fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: simulated annealing over general d-regular bipartite graphs.
#
# Unlike the group-lift search, the graph is not required to have any symmetry.
# Moves are double edge switches (a1-b1, a2-b2 -> a1-b2, a2-b1), which keep
# every degree equal to d and keep the graph simple and bipartite. The cost is
# the number of unordered vertex pairs at distance > DIAM, computed with
# bitset ball expansion. Whenever cost reaches 0 the graph is snapshotted and
# two vertices (one per side) are added, each joined to d edges taken from
# the current graph, then annealing repairs the diameter again. A stalled run
# restarts from the last valid snapshot with fresh random growth choices.
#
# Vertex ids: side A = even ids, side B = odd ids.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 4096
#define DMAX 16
#define WMAX 64
#define MMAX (NMAX * DMAX / 2 + 2 * DMAX + 8)
#define STALL 3000

static int DG = 3, DIAM = 3;
static int n = 0, m = 0;
static int adj[NMAX * DMAX];
static int ea[MMAX], eb[MMAX];
static uint64_t R0[NMAX * WMAX], R1[NMAX * WMAX];
static int s_adj[NMAX * DMAX], s_ea[MMAX], s_eb[MMAX];
static int s_n = 0, s_m = 0, s_valid = 0;
static int markx[NMAX], marky[NMAX], stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < DG; k++)
        if (adj[a * DG + k] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int k = 0; k < DG; k++)
        if (adj[v * DG + k] == old) {
            adj[v * DG + k] = nw;
            return;
        }
}

/* Raw double switch on edges e1=(a1,b1), e2=(a2,b2) -> (a1,b2), (a2,b1).
   Applying it twice restores the original graph. */
static void apply_raw(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    eb[e1] = b2;
    eb[e2] = b1;
}

static int valid_switch(int e1, int e2) {
    if (e1 == e2) return 0;
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    return 1;
}

/* Number of unordered pairs at distance > DIAM (0 means valid diameter). */
static int eval_bad(void) {
    int W = (n + 63) / 64;
    uint64_t *cur = R0, *nxt = R1;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) cur[v * W + w] = 0;
    for (int v = 0; v < n; v++) cur[v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < DG; k++) {
                const uint64_t *ng = cur + (size_t)adj[v * DG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= ng[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[(size_t)v * W + w]);
        bad += (long long)(n - c);
    }
    return (int)(bad / 2);
}

/* Random d-regular bipartite start: circulant, then random switches. */
static void init_start(int n0) {
    int H = n0 / 2;
    n = 2 * H;
    m = H * DG;
    for (int i = 0; i < H; i++)
        for (int s = 0; s < DG; s++) {
            int e = i * DG + s;
            int a = 2 * i, b = 2 * ((i + s) % H) + 1;
            ea[e] = a;
            eb[e] = b;
            adj[a * DG + s] = b;
        }
    for (int j = 0; j < H; j++)
        for (int s = 0; s < DG; s++) {
            int b = 2 * j + 1;
            int i = ((j - s) % H + H) % H;
            adj[b * DG + s] = 2 * i;
        }
    for (long t = 0; t < 20L * m; t++) {
        int e1 = rint_(m), e2 = rint_(m);
        if (valid_switch(e1, e2)) apply_raw(e1, e2);
    }
}

static void snapshot(void) {
    memcpy(s_adj, adj, sizeof(int) * (size_t)n * DG);
    memcpy(s_ea, ea, sizeof(int) * (size_t)m);
    memcpy(s_eb, eb, sizeof(int) * (size_t)m);
    s_n = n;
    s_m = m;
    s_valid = 1;
}

static void restore(void) {
    memcpy(adj, s_adj, sizeof(int) * (size_t)s_n * DG);
    memcpy(ea, s_ea, sizeof(int) * (size_t)s_m);
    memcpy(eb, s_eb, sizeof(int) * (size_t)s_m);
    n = s_n;
    m = s_m;
}

/* Add one A vertex a and one B vertex b, each of degree DG. Take DG edges
   (x_k, y_k) with distinct endpoints; edge k becomes (a, y_k) and a new edge
   (x_k, b) is appended. Degrees of the old vertices are unchanged. */
static int grow(void) {
    if (n + 2 > NMAX || m + DG > MMAX) return 0;
    int a = n, b = n + 1;
    int ce[DMAX], cx[DMAX], cy[DMAX];
    stamp++;
    int k = 0;
    long tries = 0;
    while (k < DG && tries < 1000000) {
        tries++;
        int e = rint_(m);
        int x = ea[e], y = eb[e];
        if (markx[x] == stamp || marky[y] == stamp) continue;
        markx[x] = stamp;
        marky[y] = stamp;
        ce[k] = e;
        cx[k] = x;
        cy[k] = y;
        k++;
    }
    if (k < DG) return 0;
    for (k = 0; k < DG; k++) {
        int e = ce[k], x = cx[k], y = cy[k];
        repl(x, y, b);
        repl(y, x, a);
        eb[e] = y;
        ea[e] = a;
        ea[m + k] = x;
        eb[m + k] = b;
        adj[a * DG + k] = y;
        adj[b * DG + k] = x;
    }
    m += DG;
    n += 2;
    return 1;
}

int main(int argc, char **argv) {
    DG = argc > 1 ? atoi(argv[1]) : 3;
    DIAM = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int n0 = argc > 5 ? atoi(argv[5]) : 0;

    if (DG < 1 || DG > DMAX || DIAM < 1 || DIAM > 64) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    if (n0 < 2 * DG) n0 = 2 * DG;
    if (n0 > NMAX - 2) n0 = NMAX - 2;
    if (n0 % 2) n0--;

    init_start(n0);
    int cost = eval_bad();
    int best_cost = cost;
    long stall = 0;
    const double T = 0.5;

    while (now_s() < deadline) {
        if (cost == 0) {
            snapshot();
            if (!grow()) break;
            cost = eval_bad();
            best_cost = cost;
            stall = 0;
            continue;
        }
        if (stall > STALL) {
            if (s_valid) {
                restore();
                if (!grow()) break;
            } else {
                init_start(n0);
            }
            cost = eval_bad();
            best_cost = cost;
            stall = 0;
            continue;
        }
        int e1 = rint_(m), e2 = rint_(m);
        if (!valid_switch(e1, e2)) {
            stall++;
            continue;
        }
        apply_raw(e1, e2);
        int c2 = eval_bad();
        int accept = 0;
        if (c2 <= cost) accept = 1;
        else if (urand() < exp(-(double)(c2 - cost) / T)) accept = 1;
        if (accept) cost = c2;
        else apply_raw(e1, e2);
        if (cost < best_cost) {
            best_cost = cost;
            stall = 0;
        } else {
            stall++;
        }
    }

    if (cost == 0) snapshot();
    if (!s_valid) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", s_n, s_m);
    for (int e = 0; e < s_m; e++) printf("%d %d\n", s_ea[e], s_eb[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the annealing engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealing over general d-regular bipartite graphs, growing the order
    # by two vertices at each success. Starts at the best known order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 2.0:
            n0 = best_n - best_n % 2
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", n0],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
