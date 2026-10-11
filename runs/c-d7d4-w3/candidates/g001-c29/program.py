import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow a bipartite graph one vertex at a time. Each new vertex is
# followed by simulated annealing on the number of vertex pairs at distance
# greater than D. Moves are edge addition, degree-preserving double-edge
# switches, and endpoint shifts. Every accepted state has max degree <= d,
# is bipartite by construction, and has cost 0. The best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXDEG 48
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2 + 16)
#define ITERS 6000
#define TEMP 0.5

static int d, D, N, W;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char am[MAXN][MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static double deadline;
static long long cur;

typedef struct { int t, u, v; } Op;
static Op logop[16];
static int nlog;

static int bu[MAXE], bv[MAXE], bestm, bestn;
static int have_best;

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndint(int k) { return (int)((rnd64() >> 33) % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost(void) {
    int n = N, w = W;
    uint64_t *cu = bufA, *nx = bufB;
    memset(cu, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cu[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nx + (size_t)v * w;
            const uint64_t *src = cu + (size_t)v * w;
            for (int k = 0; k < w; k++) dst[k] = src[k];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s2 = cu + (size_t)nb[v][i] * w;
                for (int k = 0; k < w; k++) dst[k] |= s2[k];
            }
        }
        uint64_t *t = cu;
        cu = nx;
        nx = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = cu + (size_t)v * w;
        for (int k = 0; k < w; k++) c += pc64(row[k]);
        bad += n - c;
    }
    return bad / 2;
}

static void del_slot(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void op_add(int u, int v) {
    am[u][v] = 1;
    am[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void op_rem(int u, int v) {
    am[u][v] = 0;
    am[v][u] = 0;
    del_slot(u, v);
    del_slot(v, u);
}

static void lop_add(int u, int v) {
    op_add(u, v);
    logop[nlog++] = (Op){1, u, v};
}

static void lop_rem(int u, int v) {
    op_rem(u, v);
    logop[nlog++] = (Op){0, u, v};
}

static void undo(void) {
    while (nlog > 0) {
        Op o = logop[--nlog];
        if (o.t) op_rem(o.u, o.v);
        else op_add(o.u, o.v);
    }
}

/* mode 0: any vertex on side s; mode 1: with deg < d; mode 2: with deg > 0 */
static int okv(int v, int s, int mode) {
    if (side[v] != s) return 0;
    if (mode == 1 && deg[v] >= d) return 0;
    if (mode == 2 && deg[v] == 0) return 0;
    return 1;
}

static int pick(int s, int mode) {
    for (int t = 0; t < 40; t++) {
        int v = rndint(N);
        if (okv(v, s, mode)) return v;
    }
    int cnt = 0, res = -1;
    for (int v = 0; v < N; v++) {
        if (okv(v, s, mode)) {
            cnt++;
            if (rndint(cnt) == 0) res = v;
        }
    }
    return res;
}

static int move_add(void) {
    int a = pick(0, 1);
    int b = pick(1, 1);
    if (a < 0 || b < 0 || am[a][b]) return 0;
    lop_add(a, b);
    return 1;
}

static int move_switch(void) {
    int a = pick(0, 2);
    if (a < 0) return 0;
    int b = nb[a][rndint(deg[a])];
    int c = pick(0, 2);
    if (c < 0 || c == a) return 0;
    int e = nb[c][rndint(deg[c])];
    if (b == e) return 0;
    if (am[a][e] || am[c][b]) return 0;
    lop_rem(a, b);
    lop_rem(c, e);
    lop_add(a, e);
    lop_add(c, b);
    return 1;
}

static int move_shift(void) {
    int a = pick(0, 2);
    if (a < 0) return 0;
    int b = nb[a][rndint(deg[a])];
    if (rndint(2) == 0) {
        int x = pick(0, 1);
        if (x < 0 || x == a || am[x][b]) return 0;
        lop_rem(a, b);
        lop_add(x, b);
        return 1;
    } else {
        int y = pick(1, 1);
        if (y < 0 || y == b || am[a][y]) return 0;
        lop_rem(a, b);
        lop_add(a, y);
        return 1;
    }
}

static int anneal(long long iters, double T) {
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now() > deadline) return 0;
        nlog = 0;
        double r = rnd01();
        int ok;
        if (r < 0.30) ok = move_add();
        else if (r < 0.65) ok = move_switch();
        else ok = move_shift();
        if (!ok) continue;
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo();
        }
    }
    return cur == 0;
}

static void snapshot(void) {
    int m = 0;
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (u < v && m < MAXE) {
                bu[m] = u;
                bv[m] = v;
                m++;
            }
        }
    }
    bestm = m;
    bestn = N;
    have_best = 1;
}

static void restore(void) {
    for (int i = 0; i < N; i++) {
        memset(am[i], 0, (size_t)N);
        deg[i] = 0;
    }
    N = bestn;
    W = (N + 63) / 64;
    for (int i = 0; i < bestm; i++) op_add(bu[i], bv[i]);
    nlog = 0;
    cur = 0;
}

static void add_vertex(int s) {
    int v = N;
    N++;
    W = (N + 63) / 64;
    side[v] = s;
    deg[v] = 0;
    for (int u = 0; u < v; u++) {
        am[u][v] = 0;
        am[v][u] = 0;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    deadline = now() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (d < 1 || d > MAXDEG - 2 || D < 2 || n0 >= MAXN - 400 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }

    memset(am, 0, sizeof am);
    memset(deg, 0, sizeof deg);
    if (n0 == 0) {
        N = 2 * d;
        for (int v = 0; v < N; v++) side[v] = (v >= d) ? 1 : 0;
        for (int a = 0; a < d; a++)
            for (int b = d; b < 2 * d; b++) op_add(a, b);
    } else {
        N = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
            if (am[u][v] || deg[u] >= d || deg[v] >= d) continue;
            op_add(u, v);
        }
        for (int v = 0; v < N; v++) side[v] = -1;
        static int qbuf[MAXN];
        for (int s = 0; s < N; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int h = 0, t = 0;
            qbuf[t++] = s;
            while (h < t) {
                int x = qbuf[h++];
                for (int i = 0; i < deg[x]; i++) {
                    int y = nb[x][i];
                    if (side[y] < 0) {
                        side[y] = 1 - side[x];
                        qbuf[t++] = y;
                    }
                }
            }
        }
    }
    W = (N + 63) / 64;
    nlog = 0;
    have_best = 0;

    cur = cost();
    if (cur > 0) anneal(1000000000LL, TEMP);
    if (cur == 0) snapshot();

    while (have_best && now() < deadline && N < MAXN - 1) {
        add_vertex(rndint(2));
        cur = cost();
        if (anneal(ITERS, TEMP)) {
            snapshot();
        } else {
            restore();
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestn, bestm);
    for (int i = 0; i < bestm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _twins(n, edges, d, rng):
    """Greedy non-adjacent twin duplication. Twins keep distances and bipartiteness."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, [tuple(x) for x in e]

    moore = lib.moore_bound(d, D)

    # Structured bases: W(q) for D >= 4, PG(2, q) for D >= 3.
    bases = []
    if D >= 4:
        g = _best_gq(d)
        if g is not None:
            bases.append(g)
    if D >= 3:
        p = _best_pg(d)
        if p is not None:
            bases.append(p)
    bases.sort(key=lambda g: -g[0])

    raw_starts = []
    for n0, e0 in bases:
        consider(n0, e0)
        raw_starts.append((n0, list(e0)))
        n1, e1 = _twins(n0, e0, d, rng)
        consider(n1, e1)

    if best_n >= moore:
        return best_n, best_e

    def remaining():
        return end - time.monotonic()

    def run_engine(n0, e0, k, until):
        secs = until - time.monotonic() - 1.0
        if secs < 1.0:
            return
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 7 + k, f"{secs:.2f}"],
                            stdin_graph=(n0, e0), timeout=secs + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    plans = [(best_n, list(best_e))]
    if raw_starts and raw_starts[0][0] != best_n:
        plans.append(raw_starts[0])
    shares = [0.6, 0.4] if len(plans) == 2 else [1.0]
    for k, (pn, pe) in enumerate(plans):
        rem = remaining()
        if rem < 3.0:
            break
        until = time.monotonic() + shares[k] * rem
        run_engine(pn, pe, k, until)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
