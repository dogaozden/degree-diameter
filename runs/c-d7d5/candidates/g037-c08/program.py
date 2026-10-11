import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions used as fallbacks and as starting graphs.
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
# C engine: simulated annealing on a general bipartite graph with vertex
# growth. Cost = number of unordered vertex pairs at distance > D, computed
# with bitset BFS. Moves are degree-preserving double swaps, edge additions
# between deficient vertices (monotone), and "split" moves that move an edge
# endpoint onto a deficient vertex. The graph is grown by adding vertices on
# both sides; each growth stage is repaired by annealing. The best valid graph
# is always kept and printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MD 64
#define MW ((MAXN + 63) / 64)

static int DG = 3, DM = 3;
static int N = 0;
static int adj[MAXN * MD];
static int deg[MAXN];
static int side[MAXN];

static int badj[MAXN * MD];
static int bdeg[MAXN];
static int bside[MAXN];
static int bN = 0;

static int def0[MAXN], def1[MAXN];
static int lop[8], lu[8], lv[8], nlog = 0;

static uint64_t R1[MAXN * MW], R2[MAXN * MW];
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u * MD + i] == v) return 1;
    return 0;
}

static void raw_add(int u, int v) {
    adj[u * MD + deg[u]++] = v;
    adj[v * MD + deg[v]++] = u;
}

static void raw_del1(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u * MD + i] == v) {
            adj[u * MD + i] = adj[u * MD + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void raw_del(int u, int v) {
    raw_del1(u, v);
    raw_del1(v, u);
}

static void op_add(int u, int v) {
    raw_add(u, v);
    lop[nlog] = 1; lu[nlog] = u; lv[nlog] = v; nlog++;
}

static void op_del(int u, int v) {
    raw_del(u, v);
    lop[nlog] = 0; lu[nlog] = u; lv[nlog] = v; nlog++;
}

static void undo(void) {
    while (nlog > 0) {
        nlog--;
        if (lop[nlog] == 1) raw_del(lu[nlog], lv[nlog]);
        else raw_add(lu[nlog], lv[nlog]);
    }
}

/* Number of unordered pairs at distance > DM (unreachable pairs count too). */
static long long cost_bad(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur + (size_t)adj[v * MD + i] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(c[w]);
        miss += N - pc;
    }
    return miss / 2;
}

static void build_def(int *n0, int *n1) {
    *n0 = 0;
    *n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DG) {
            if (side[v] == 0) def0[(*n0)++] = v;
            else def1[(*n1)++] = v;
        }
    }
}

static int samp_side(int s, int need_def, int need_pos) {
    for (int t = 0; t < 400; t++) {
        int v = rint_(N);
        if (side[v] != s) continue;
        if (need_def && deg[v] >= DG) continue;
        if (need_pos && deg[v] == 0) continue;
        return v;
    }
    return -1;
}

/* Add an edge between two deficient vertices on opposite sides. */
static int move_add(void) {
    int n0, n1;
    build_def(&n0, &n1);
    if (!n0 || !n1) return 0;
    for (int t = 0; t < 40; t++) {
        int a = def0[rint_(n0)], b = def1[rint_(n1)];
        if (!has_edge(a, b)) {
            op_add(a, b);
            return 1;
        }
    }
    return 0;
}

/* Replace edge (a,b) by (a,y) and (x,b), with x, y deficient. Degrees of a, b unchanged. */
static int move_split(void) {
    int n0, n1;
    build_def(&n0, &n1);
    if (!n0 || !n1) return 0;
    for (int t = 0; t < 40; t++) {
        int a = samp_side(0, 0, 1);
        if (a < 0) return 0;
        int b = adj[a * MD + rint_(deg[a])];
        int x = def0[rint_(n0)], y = def1[rint_(n1)];
        if (x == a || y == b) continue;
        if (has_edge(a, y) || has_edge(x, b)) continue;
        op_del(a, b);
        op_add(a, y);
        op_add(x, b);
        return 1;
    }
    return 0;
}

/* Double swap: (a,b),(a2,b2) -> (a,b2),(a2,b). Degrees unchanged. */
static int move_swap(void) {
    int a = samp_side(0, 0, 1);
    if (a < 0) return 0;
    int a2 = samp_side(0, 0, 1);
    if (a2 < 0 || a2 == a) return 0;
    int b = adj[a * MD + rint_(deg[a])];
    int b2 = adj[a2 * MD + rint_(deg[a2])];
    if (b == b2) return 0;
    if (has_edge(a, b2) || has_edge(a2, b)) return 0;
    op_del(a, b);
    op_del(a2, b2);
    op_add(a, b2);
    op_add(a2, b);
    return 1;
}

static long long cur_cost = 0;

/* Simulated annealing on the bad-pair cost. Returns 1 when cost reaches 0. */
static int stage(long long iters, double T0, double T1) {
    cur_cost = cost_bad();
    if (cur_cost == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 15) == 0 && now_s() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        nlog = 0;
        int ok;
        int r = rint_(100);
        if (r < 25) ok = move_add();
        else if (r < 50) ok = move_split();
        else ok = move_swap();
        if (!ok) {
            nlog = 0;
            continue;
        }
        long long nc = cost_bad();
        long long delta = nc - cur_cost;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur_cost = nc;
            nlog = 0;
            if (cur_cost == 0) return 1;
        } else {
            undo();
            nlog = 0;
        }
    }
    return 0;
}

static void save_best(void) {
    memcpy(badj, adj, sizeof(int) * (size_t)N * MD);
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(bside, side, sizeof(int) * (size_t)N);
    bN = N;
}

static void restore_best(void) {
    N = bN;
    memcpy(adj, badj, sizeof(int) * (size_t)N * MD);
    memcpy(deg, bdeg, sizeof(int) * (size_t)N);
    memcpy(side, bside, sizeof(int) * (size_t)N);
}

static int bip_sides(void) {
    static int col[MAXN], q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u * MD + i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[t++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < N; v++) side[v] = col[v];
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DG = atoi(argv[1]);
    DM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (DG < 1 || DG >= MD || DM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int n = 0, mm = 0;
    if (scanf("%d %d", &n, &mm) != 2) {
        n = 0;
        mm = 0;
    }
    if (n <= 0 || mm <= 0) {
        /* Default start: K_{DG,DG}, valid for D >= 2. */
        N = 2 * DG;
        for (int i = 0; i < DG; i++) {
            side[i] = 0;
            side[DG + i] = 1;
        }
        for (int i = 0; i < DG; i++)
            for (int j = 0; j < DG; j++)
                raw_add(i, DG + j);
    } else {
        if (n > MAXN) {
            printf("0 0\n");
            return 0;
        }
        N = n;
        for (int e = 0; e < mm; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                printf("0 0\n");
                return 0;
            }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) {
                printf("0 0\n");
                return 0;
            }
            if (has_edge(u, v)) continue;
            if (deg[u] >= DG || deg[v] >= DG) {
                printf("0 0\n");
                return 0;
            }
            raw_add(u, v);
        }
        if (!bip_sides()) {
            printf("0 0\n");
            return 0;
        }
    }

    int have = 0;
    if (cost_bad() == 0) {
        have = 1;
        save_best();
    }
    long long iters = 2000 + 4LL * N;
    int step = N / 60;
    if (step < 1) step = 1;

    while (now_s() < deadline) {
        if (!have) {
            if (stage(iters, 3.0, 0.2)) {
                have = 1;
                save_best();
                iters = 2000 + 4LL * N;
            } else {
                iters = iters * 2;
            }
            continue;
        }
        int add = step;
        if (bN + 2 * add > MAXN) add = (MAXN - bN) / 2;
        if (add < 1) break;
        int old = N;
        for (int k = 0; k < 2 * add; k++) {
            int v = old + k;
            side[v] = (k < add) ? 0 : 1;
            deg[v] = 0;
        }
        N = old + 2 * add;
        if (stage(iters, 3.0, 0.2)) {
            save_best();
            step = step + step / 4 + 1;
            iters = 2000 + 4LL * N;
        } else {
            restore_best();
            step = step / 2;
            if (step < 1) step = 1;
            iters = iters + iters / 4 + 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    restore_best();
    long long m = 0;
    for (int v = 0; v < N; v++) m += deg[v];
    m /= 2;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * MD + i];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the annealing engine grows the
# best exact graph. Every result is checked; the best valid graph is returned.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.90 * time_limit, time_limit - 5.0))

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

    # Bold step: grow the best exact graph with simulated annealing on
    # bad-pair counts (bitset BFS), instead of bi-Cayley group search.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                                stdin_graph=best, timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
