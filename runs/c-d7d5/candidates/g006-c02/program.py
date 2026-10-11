import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New search engine (replaces the bi-Cayley voltage annealing).
#
# The state is an arbitrary bipartite graph with max degree DEG on n vertices
# (side 0 / side 1). It is not restricted to a lift, so the search space is
# much larger. Cost = number of ordered vertex pairs at distance > DIAM,
# computed exactly with bitset BFS (all sources at once, O(n*DEG*n/64*DIAM)).
#
# Moves (all preserve bipartiteness and the degree cap):
#   switch : (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)
#   expand : deficient a, deficient b, edge (x,y) -> (a,y),(x,b); adds one edge
# After each move, greedy fill adds any edge between deficient vertices on
# opposite sides. Moves are undone from a log if rejected.
#
# Growth: whenever the cost reaches 0, the graph is saved, two vertices (one per
# side) are appended, and annealing continues from there. The last saved valid
# graph is printed.
#
# Input: optional start graph on stdin ("n m", edges), else empty graph on n0.
# Usage: prog d D seed slice [n0]
# Output: valid graph "n m" + edges, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define MAXD 64
#define MAXW (MAXV / 64)
#define MAXLOG 65536

static int DEG, DIAM, n;
static int side[MAXV], deg[MAXV], nb[MAXV][MAXD];
static int lop[MAXLOG], lu[MAXLOG], lv[MAXLOG];
static int nlog = 0, logging = 0, log_overflow = 0;
static int cur;
static uint64_t RA[MAXV][MAXW], RB[MAXV][MAXW];

typedef struct {
    int n;
    int deg[MAXV];
    int nb[MAXV][MAXD];
} State;

static State st_best, st_res;
static int best_cost;
static int have_valid = 0;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t T0C;
static double slice_s;
static double elapsed(void) { return (double)(clock() - T0C) / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int adjq(int u, int v) {
    int k = deg[u];
    for (int i = 0; i < k; i++) if (nb[u][i] == v) return 1;
    return 0;
}

static void push_log(int op, int u, int v) {
    if (!logging) return;
    if (nlog >= MAXLOG) { log_overflow = 1; return; }
    lop[nlog] = op; lu[nlog] = u; lv[nlog] = v; nlog++;
}

static void rem_one(int x, int y) {
    int k = deg[x];
    for (int i = 0; i < k; i++) {
        if (nb[x][i] == y) {
            nb[x][i] = nb[x][k - 1];
            deg[x] = k - 1;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    push_log(1, u, v);
}

static void rem_edge(int u, int v) {
    rem_one(u, v);
    rem_one(v, u);
    push_log(0, u, v);
}

static void undo(void) {
    int save = logging;
    logging = 0;
    for (int i = nlog - 1; i >= 0; i--) {
        int u = lu[i], v = lv[i];
        if (lop[i] == 1) {
            rem_one(u, v);
            rem_one(v, u);
        } else {
            nb[u][deg[u]++] = v;
            nb[v][deg[v]++] = u;
        }
    }
    nlog = 0;
    logging = save;
}

static long long cost_fn_unused(void) { return 0; }

static int cost_fn(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cu)[MAXW] = RA;
    uint64_t (*nx)[MAXW] = RB;
    uint64_t (*tmp)[MAXW];
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cu[v][w] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx[v];
            const uint64_t *c = cu[v];
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *c2 = cu[nb[v][i]];
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        tmp = cu; cu = nx; nx = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++)
            tot += popc(cu[v][w]);
    return (int)((long long)n * n - tot);
}

static void snap(State *s) {
    s->n = n;
    for (int v = 0; v < n; v++) {
        s->deg[v] = deg[v];
        memcpy(s->nb[v], nb[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void restore(const State *s) {
    n = s->n;
    for (int v = 0; v < n; v++) {
        deg[v] = s->deg[v];
        memcpy(nb[v], s->nb[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void shuffle_ints(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void fill(void) {
    static int da[MAXV], db[MAXV];
    int changed = 1;
    while (changed) {
        changed = 0;
        int na = 0, nbb = 0;
        for (int v = 0; v < n; v++) {
            if (deg[v] < DEG) {
                if (side[v] == 0) da[na++] = v;
                else db[nbb++] = v;
            }
        }
        if (na == 0 || nbb == 0) break;
        shuffle_ints(da, na);
        shuffle_ints(db, nbb);
        for (int i = 0; i < na; i++) {
            int a = da[i];
            for (int j = 0; j < nbb; j++) {
                if (deg[a] >= DEG) break;
                int b = db[j];
                if (deg[b] < DEG && !adjq(a, b)) {
                    add_edge(a, b);
                    changed = 1;
                }
            }
        }
    }
}

/* Uniform random vertex on side s with (deg<DEG) if needdef, else (deg>0). -1 if none. */
static int pick_v(int s, int needdef) {
    int cnt = 0, pick = -1;
    for (int v = 0; v < n; v++) {
        if (side[v] != s) continue;
        int ok = needdef ? (deg[v] < DEG) : (deg[v] > 0);
        if (ok) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    }
    return pick;
}

static int switch_move(void) {
    int a1 = pick_v(0, 0);
    int a2 = pick_v(0, 0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
    int b1 = nb[a1][rndint(deg[a1])];
    int b2 = nb[a2][rndint(deg[a2])];
    if (b1 == b2) return 0;
    if (adjq(a1, b2) || adjq(a2, b1)) return 0;
    rem_edge(a1, b1);
    rem_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    return 1;
}

static int expand_move(void) {
    int a = pick_v(0, 1);
    int b = pick_v(1, 1);
    if (a < 0 || b < 0) return 0;
    int x = pick_v(0, 0);
    if (x < 0) return 0;
    int y = nb[x][rndint(deg[x])];
    if (adjq(a, y) || adjq(x, b)) return 0;
    rem_edge(x, y);
    add_edge(a, y);
    add_edge(x, b);
    return 1;
}

static void step(double T, int expand) {
    nlog = 0;
    logging = 1;
    log_overflow = 0;
    int moved = expand ? expand_move() : switch_move();
    if (!moved) moved = switch_move();
    if (!moved) { logging = 0; nlog = 0; return; }
    fill();
    int nc = cost_fn();
    logging = 0;
    if (nc <= cur || log_overflow || rnd01() < exp(-(double)(nc - cur) / T)) {
        cur = nc;
        nlog = 0;
    } else {
        undo();
    }
}

static void grow(void) {
    side[n] = 0; deg[n] = 0;
    side[n + 1] = 1; deg[n + 1] = 0;
    n += 2;
}

static int read_start(void) {
    memset(deg, 0, sizeof deg);
    int ni, mi;
    if (scanf("%d %d", &ni, &mi) != 2) return 0;
    if (ni <= 0 || mi <= 0 || ni > MAXV - 2 || mi > ni * DEG) return 0;
    int *eu = malloc(sizeof(int) * (size_t)mi * 2);
    if (!eu) return 0;
    int ok = 1;
    for (int i = 0; i < mi; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= ni || v >= ni || u == v) { ok = 0; break; }
        eu[2 * i] = u; eu[2 * i + 1] = v;
    }
    n = ni;
    if (ok) {
        for (int i = 0; i < mi && ok; i++) {
            int u = eu[2 * i], v = eu[2 * i + 1];
            if (deg[u] >= DEG || deg[v] >= DEG || adjq(u, v)) { ok = 0; break; }
            nb[u][deg[u]++] = v;
            nb[v][deg[v]++] = u;
        }
    }
    free(eu);
    if (!ok) { memset(deg, 0, sizeof deg); n = 0; return 0; }

    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    if (!col || !q) { free(col); free(q); memset(deg, 0, sizeof deg); n = 0; return 0; }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[u][i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[tail++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (ok) {
        for (int v = 0; v < n; v++) side[v] = col[v];
    }
    free(col);
    free(q);
    if (!ok) { memset(deg, 0, sizeof deg); n = 0; return 0; }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    slice_s = atof(argv[4]);
    int n0 = (argc > 5) ? atoi(argv[5]) : 2 * DEG;
    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEF12345ULL;
    if (rs == 0) rs = 1;
    T0C = clock();

    n = 0;
    if (!read_start()) {
        n0 &= ~1;
        if (n0 < 2) n0 = 2;
        if (n0 > MAXV - 2) n0 = MAXV - 2;
        memset(deg, 0, sizeof deg);
        n = n0;
        for (int v = 0; v < n; v++) side[v] = v & 1;
    }

    fill();
    cur = cost_fn();
    snap(&st_best);
    best_cost = cur;
    if (cur == 0) { snap(&st_res); have_valid = 1; }

    const int ITERS = 3000;
    int attempt = 0;
    while (elapsed() < slice_s) {
        if (cur == 0) {
            snap(&st_res);
            have_valid = 1;
            if (n + 2 > MAXV) break;
            grow();
            fill();
            cur = cost_fn();
            snap(&st_best);
            best_cost = cur;
            continue;
        }
        restore(&st_best);
        cur = best_cost;
        double Ta = (attempt == 0) ? 3.0 : 1.5;
        for (int it = 0; it < ITERS && cur != 0; it++) {
            if ((it & 15) == 0 && elapsed() >= slice_s) break;
            double frac = (double)it / ITERS;
            double T = Ta * pow(0.05 / Ta, frac);
            int ex = rnd01() < 0.35;
            step(T, ex);
            if (cur < best_cost) {
                best_cost = cur;
                snap(&st_best);
            }
        }
        if (cur == 0) { snap(&st_res); have_valid = 1; }
        attempt++;
    }

    if (!have_valid) {
        printf("0 0\n");
        return 0;
    }
    State *s = &st_res;
    int M = 0;
    for (int v = 0; v < s->n; v++)
        if (side[v] == 0) M += s->deg[v];
    printf("%d %d\n", s->n, M);
    for (int v = 0; v < s->n; v++) {
        if (side[v] != 0) continue;
        for (int i = 0; i < s->deg[v]; i++)
            printf("%d %d\n", v, s->nb[v][i]);
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions (kept from the parent).
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        # Araujo-Pardo & Lopez record for D = 3, d = q + 2 with q a prime power.
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold change: direct annealing over general bipartite graphs (not lifts),
    # growing the vertex count from the best valid start.
    slice_s = budget - 4.0
    remaining = budget - (time.monotonic() - start)
    if slice_s >= 1.0 and remaining > 3.0:
        slice_s = min(slice_s, remaining - 3.0)
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, (int(seed) % 1000000007) + 1, f"{slice_s:.2f}"],
                stdin_graph=best,
                timeout=slice_s + 6.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
