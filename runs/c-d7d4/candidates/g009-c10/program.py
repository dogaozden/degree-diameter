import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bounded-diameter vertex insertion with annealing repair.
#
# State: a bipartite graph with max degree d, kept valid (diameter <= D) at all
# times. One growth step inserts a vertex on a random side, joined to a greedy
# cover of the opposite side. Its neighbours are chosen so that their radius
# D-1 balls cover every old vertex. Spare degree is then filled, and a
# Metropolis walk over degree-preserving bipartite double-edge switches
# minimises the number of pairs at distance > D. Success keeps the larger graph.
# Failure rolls back to the last valid snapshot.
# Distances use bitset balls, so one cost evaluation is D rounds of OR-sweeps.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXD / 2)

static int d, D;
static int n, W;
static int col[MAXN], deg[MAXN];
static int nb[MAXN][MAXD];
static int eu[MAXE], ev[MAXE], nE;
static int ru[MAXE], rv[MAXE];
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t ballPrev[MAXN * MAXW], ballFull[MAXN * MAXW];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double t_budget = 10.0;
static clock_t t0;
static int time_up(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC > t_budget; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

typedef struct {
    int n, nE;
    int col[MAXN], deg[MAXN];
    int nb[MAXN][MAXD];
    int eu[MAXE], ev[MAXE];
} Snap;
static Snap good;

static void save_state(Snap *s) {
    s->n = n; s->nE = nE;
    memcpy(s->col, col, sizeof(int) * n);
    memcpy(s->deg, deg, sizeof(int) * n);
    memcpy(s->nb, nb, sizeof(int) * MAXD * n);
    memcpy(s->eu, eu, sizeof(int) * nE);
    memcpy(s->ev, ev, sizeof(int) * nE);
}

static void restore_state(const Snap *s) {
    n = s->n; W = (n + 63) / 64; nE = s->nE;
    memcpy(col, s->col, sizeof(int) * n);
    memcpy(deg, s->deg, sizeof(int) * n);
    memcpy(nb, s->nb, sizeof(int) * MAXD * n);
    memcpy(eu, s->eu, sizeof(int) * nE);
    memcpy(ev, s->ev, sizeof(int) * nE);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (nb[a][k] == b) return 1;
    return 0;
}

static void adj_replace(int x, int from, int to) {
    for (int k = 0; k < deg[x]; k++) if (nb[x][k] == from) { nb[x][k] = to; return; }
}

static void adj_remove(int x, int y) {
    for (int k = 0; k < deg[x]; k++) {
        if (nb[x][k] == y) { nb[x][k] = nb[x][deg[x] - 1]; deg[x]--; return; }
    }
}

static void add_edge(int a, int b) {
    if (col[a] == 1) { int t = a; a = b; b = t; }
    eu[nE] = a; ev[nE] = b; nE++;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void remove_edge(int a, int b) {
    if (col[a] == 1) { int t = a; a = b; b = t; }
    for (int i = 0; i < nE; i++) {
        if (eu[i] == a && ev[i] == b) {
            nE--; eu[i] = eu[nE]; ev[i] = ev[nE];
            break;
        }
    }
    adj_remove(a, b);
    adj_remove(b, a);
}

/* Edge i = (a,b), edge j = (c,e), with a,c on side 0. Becomes i = (a,e), j = (c,b).
   Applying it twice with the same i, j restores the original graph. */
static void do_switch(int i, int j) {
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    eu[i] = a; ev[i] = e;
    eu[j] = c; ev[j] = b;
    adj_replace(a, b, e);
    adj_replace(b, a, c);
    adj_replace(c, e, b);
    adj_replace(e, c, a);
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Join deficient opposite-side pairs greedily. Never increases the bad-pair count. */
static int fill_all(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    shuffle(L, nl);
    shuffle(R, nr);
    int added = 0;
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (deg[a] >= d) break;
            int b = R[j];
            if (deg[b] < d && !has_edge(a, b)) { add_edge(a, b); added++; }
        }
    }
    return added;
}

/* out[v] = bitset of vertices within distance r of v. */
static void compute_balls(int r, uint64_t *out) {
    uint64_t *cur = bufA, *nxt = bufB;
    size_t words = (size_t)n * W;
    memset(cur, 0, sizeof(uint64_t) * words);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt + (size_t)v * W;
            const uint64_t *y = cur + (size_t)v * W;
            memcpy(x, y, sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *z = cur + (size_t)nb[v][k] * W;
                for (int w = 0; w < W; w++) x[w] |= z[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    memcpy(out, cur, sizeof(uint64_t) * words);
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static int bad_pairs(void) {
    compute_balls(D, ballFull);
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *b = ballFull + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pc64(b[w]);
        tot += n - c;
    }
    return (int)(tot / 2);
}

/* Insert vertex n on `side`, joined to a greedy cover of the opposite side. */
static void insert_vertex(int side) {
    compute_balls(D - 1, ballPrev);
    uint64_t covered[MAXW];
    memset(covered, 0, sizeof covered);
    int cand[MAXN], nc = 0;
    char used[MAXN];
    memset(used, 0, sizeof used);
    for (int t = 0; t < n; t++) if (col[t] == 1 - side) cand[nc++] = t;
    int chosen[MAXD], nch = 0;
    for (int k = 0; k < d; k++) {
        int best = -1;
        double bs = -1.0;
        for (int i = 0; i < nc; i++) {
            int t = cand[i];
            if (used[t]) continue;
            const uint64_t *b = ballPrev + (size_t)t * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(b[w] & ~covered[w]);
            if (g == 0) continue;
            double sc = g + 0.5 * rnd01();
            if (sc > bs) { bs = sc; best = t; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        const uint64_t *b = ballPrev + (size_t)best * W;
        for (int w = 0; w < W; w++) covered[w] |= b[w];
    }
    int v = n;
    n++; W = (n + 63) / 64;
    col[v] = side; deg[v] = 0;
    for (int k = 0; k < nch; k++) {
        int t = chosen[k];
        if (deg[t] >= d) {
            int x = nb[t][rndi(deg[t])];
            remove_edge(t, x);
        }
        add_edge(t, v);
    }
}

/* Metropolis walk over double-edge switches. Returns 1 iff the cost reaches 0. */
static int anneal(int iters, double T) {
    int cur = bad_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && time_up()) break;
        if (fill_all() > 0) { cur = bad_pairs(); continue; }
        if (nE < 2) break;
        int i = rndi(nE), j = rndi(nE);
        if (i == j) continue;
        int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
        if (a == c || b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        do_switch(i, j);
        int nc = bad_pairs();
        int acc = (nc <= cur) || (rnd01() < exp(-(double)(nc - cur) / T));
        if (acc) cur = nc;
        else do_switch(i, j);
    }
    return cur == 0;
}

static long moore_bound(void) {
    if (d <= 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void giveup(void) {
    printf("0 0\n");
    exit(0);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    t_budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    t0 = clock();

    int N = 0, M = 0;
    if (scanf("%d %d", &N, &M) != 2) { N = 0; M = 0; }
    if (N == 0) {
        N = 2; M = 1; ru[0] = 0; rv[0] = 1;
    } else {
        if (N < 2 || N > MAXN - 2 || M < 0 || M > MAXE) giveup();
        for (int i = 0; i < M; i++) {
            if (scanf("%d %d", &ru[i], &rv[i]) != 2) giveup();
        }
    }
    if (d < 1 || d >= MAXD || D < 2) giveup();

    n = N; W = (n + 63) / 64;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < M; i++) {
        int u = ru[i], v = rv[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) giveup();
        if (deg[u] >= d || deg[v] >= d) giveup();
        int dup = 0;
        for (int k = 0; k < deg[u]; k++) if (nb[u][k] == v) dup = 1;
        if (dup) continue;
        nb[u][deg[u]++] = v;
        nb[v][deg[v]++] = u;
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (col[v] < 0) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) giveup();
            }
        }
    }
    nE = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] != 0) continue;
        for (int k = 0; k < deg[v]; k++) {
            eu[nE] = v; ev[nE] = nb[v][k]; nE++;
        }
    }

    fill_all();
    if (bad_pairs() > 0) {
        anneal(30000, 0.45);
        if (bad_pairs() != 0) giveup();
    }
    save_state(&good);

    long moore = moore_bound();
    int fails = 0;
    while (!time_up() && n < moore && n + 1 < MAXN && nE + d <= MAXE) {
        save_state(&good);
        insert_vertex(rndi(2));
        fill_all();
        int iters = 1500 + 400 * (fails < 20 ? fails : 20);
        if (anneal(iters, 0.45)) {
            fails = 0;
        } else {
            restore_state(&good);
            fails++;
        }
    }

    if (bad_pairs() != 0) restore_state(&good);
    printf("%d %d\n", n, nE);
    for (int i = 0; i < nE; i++) printf("%d %d\n", eu[i], ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: start graphs for the C engine.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q <= 8 for speed."""
    for q in range(min(d - 1, 8), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    cands = []
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            cands.append(pg)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            cands.append(gq)

    for n0, e0 in cands:
        if n0 > best_n and lib.is_valid(n0, e0, d, D):
            best_n, best_e = n0, list(e0)

    # Let the C engine grow the best start graph by insertion and annealing.
    moore = lib.moore_bound(d, D)
    budget = 0.72 * time_limit - 2.0
    if D >= 2 and budget >= 1.0 and best_n < moore:
        left = time_limit * 0.92 - (time.monotonic() - start)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(best_n, best_e), timeout=max(1.0, left))
            n, e = lib.parse_graph_text(out)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, list(e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
