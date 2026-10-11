import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine with two modes.
#
# mode 0 (difference covers, D = 3): find a k-subset S of Z_m (k = d) whose
#   nonzero differences cover Z_m \ {0}. The Haar graph H(m, S) (a_i ~ b_{i+s})
#   then has diameter 3 and degree k on 2m vertices. Simulated annealing over S
#   minimises the number of uncovered residues. m climbs from a start value and
#   the best m found is printed.
# mode 1 (penalty annealing): simulated annealing over bipartite graphs read from
#   stdin, with moves add / remove / double-edge swap. Energy = bad pairs
#   - BETA * nalive. The best valid graph (bad == 0, most vertices) is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 64
#define MAXM 1024

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

/* ------------------------------------------------------------------ */
/* mode 0: difference cover search                                     */
/* ------------------------------------------------------------------ */

static int CK, CM, ZEROS;
static int CS[MAXK];
static int CNT[MAXM];
static int INS[MAXM];

static void cov_dec(int old, int i) {
    for (int j = 0; j < CK; j++) {
        if (j == i) continue;
        int t = CS[j];
        int a = (old - t + CM) % CM;
        int b = (t - old + CM) % CM;
        if (--CNT[a] == 0) ZEROS++;
        if (--CNT[b] == 0) ZEROS++;
    }
}

static void cov_inc(int y, int i) {
    for (int j = 0; j < CK; j++) {
        if (j == i) continue;
        int t = CS[j];
        int a = (y - t + CM) % CM;
        int b = (t - y + CM) % CM;
        if (CNT[a]++ == 0) ZEROS--;
        if (CNT[b]++ == 0) ZEROS--;
    }
}

/* Returns 1 if a k-subset of Z_m covering all nonzero differences was found (in CS). */
static int find_cover(int m, int k, double deadline) {
    CM = m;
    CK = k;
    memset(CNT, 0, sizeof(int) * m);
    memset(INS, 0, sizeof(int) * m);
    for (int i = 0; i < k; i++) {
        int y;
        do { y = rndi(m); } while (INS[y]);
        INS[y] = 1;
        CS[i] = y;
    }
    ZEROS = m - 1;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) {
            if (i == j) continue;
            int a = (CS[i] - CS[j] + m) % m;
            if (CNT[a]++ == 0) ZEROS--;
        }
    double ts = elapsed();
    double span = deadline - ts;
    if (span < 0.01) span = 0.01;
    double T = 0.5;
    long it = 0;
    while (ZEROS > 0) {
        it++;
        if ((it & 4095) == 0) {
            double now = elapsed();
            if (now > deadline) return 0;
            double f = (now - ts) / span;
            if (f > 1.0) f = 1.0;
            T = 0.5 * pow(0.05, f);
        }
        int i = rndi(k);
        int y = rndi(m);
        if (INS[y]) continue;
        int old = CS[i];
        int z0 = ZEROS;
        cov_dec(old, i);
        cov_inc(y, i);
        int delta = ZEROS - z0;
        if (delta <= 0 || rndu() < exp(-delta / T)) {
            INS[old] = 0;
            INS[y] = 1;
            CS[i] = y;
        } else {
            cov_dec(y, i);
            cov_inc(old, i);
        }
    }
    return 1;
}

static void run_cover(int k, double budget, int mstart) {
    int cap = k * (k - 1) + 1;
    if (cap > MAXM - 1) cap = MAXM - 1;
    int m = mstart;
    if (m > cap) m = cap;
    if (m < k + 1) m = k + 1;
    int bestm = 0, fails = 0;
    int bestS[MAXK];
    while (m >= k + 1 && m <= cap) {
        double rem = budget - elapsed();
        if (rem <= 0.05) break;
        double slice = rem < 2.0 ? rem : 2.0;
        if (find_cover(m, k, elapsed() + slice)) {
            bestm = m;
            memcpy(bestS, CS, sizeof(int) * k);
            m++;
            fails = 0;
        } else {
            fails++;
            if (bestm == 0) m--;
            else if (fails >= 4) break;
        }
    }
    if (bestm == 0) { printf("0 0\n"); return; }
    printf("%d %d\n", 2 * bestm, k * bestm);
    for (int i = 0; i < bestm; i++)
        for (int j = 0; j < k; j++)
            printf("%d %d\n", i, bestm + (i + bestS[j]) % bestm);
}

/* ------------------------------------------------------------------ */
/* mode 1: penalty annealing on bipartite graphs                       */
/* ------------------------------------------------------------------ */

typedef struct {
    int alive[MAXN];
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int nalive;
    int cap;
} State;

static State cur, bak, best;
static int have_best = 0;
static int d, D;
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];

static int popc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) if (cur.adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    cur.adj[u][cur.deg[u]++] = v;
    cur.adj[v][cur.deg[v]++] = u;
}

static void del_one(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) {
        if (cur.adj[u][i] == v) {
            cur.adj[u][i] = cur.adj[u][cur.deg[u] - 1];
            cur.deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_one(u, v);
    del_one(v, u);
}

static long long compute_bad(void) {
    int cap = cur.cap;
    int W = (cap + 63) >> 6;
    if (W < 1) W = 1;
    for (int v = 0; v < cap; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        if (cur.alive[v]) reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < cur.deg[v]; i++) {
                int u = cur.adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < cap; v++) {
            if (!cur.alive[v]) continue;
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
        }
    }
    long long tot = 0;
    for (int v = 0; v < cap; v++) {
        if (!cur.alive[v]) continue;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(reach[v][w]);
        tot += cur.nalive - pc;
    }
    return tot / 2;
}

static int move_add(void) {
    int w = -1;
    for (int i = 0; i < MAXN; i++) if (!cur.alive[i]) { w = i; break; }
    if (w < 0) return 0;
    int side = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < cur.cap; v++)
        if (cur.alive[v] && cur.col[v] == 1 - side) cand[nc++] = v;
    if (nc == 0) return 0;
    int k = nc < d ? nc : d;
    for (int i = 0; i < k; i++) {
        int j = i + rndi(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    cur.alive[w] = 1;
    cur.col[w] = side;
    cur.deg[w] = 0;
    cur.nalive++;
    if (w + 1 > cur.cap) cur.cap = w + 1;
    for (int i = 0; i < k; i++) {
        int p = cand[i];
        if (cur.deg[p] >= d) {
            int q = cur.adj[p][rndi(cur.deg[p])];
            del_edge(p, q);
        }
        add_edge(w, p);
    }
    return 1;
}

static int move_remove(void) {
    if (cur.nalive <= 2) return 0;
    int w, tries = 0;
    do {
        w = rndi(cur.cap);
        tries++;
    } while (!cur.alive[w] && tries < 100000);
    if (!cur.alive[w]) return 0;
    while (cur.deg[w] > 0) {
        int u = cur.adj[w][0];
        del_edge(w, u);
    }
    cur.alive[w] = 0;
    cur.nalive--;
    return 1;
}

static int move_swap(void) {
    int u, x, tries = 0;
    do {
        u = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[u] || cur.deg[u] == 0) && tries < 100000);
    if (!cur.alive[u] || cur.deg[u] == 0) return 0;
    int v = cur.adj[u][rndi(cur.deg[u])];
    int s = cur.col[u];
    tries = 0;
    do {
        x = rndi(cur.cap);
        tries++;
    } while ((!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) && tries < 100000);
    if (!cur.alive[x] || cur.deg[x] == 0 || cur.col[x] != s) return 0;
    int y = cur.adj[x][rndi(cur.deg[x])];
    if (x == u || y == v) return 0;
    if (has_edge(u, y) || has_edge(x, v)) return 0;
    del_edge(u, v);
    del_edge(x, y);
    add_edge(u, y);
    add_edge(x, v);
    return 1;
}

static void run_anneal(double budget) {
    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2 || N0 < 1 || N0 > MAXN - 64) { printf("0 0\n"); return; }
    memset(&cur, 0, sizeof(cur));
    cur.cap = N0;
    cur.nalive = N0;
    for (int i = 0; i < N0; i++) cur.alive[i] = 1;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N0 || v >= N0 || u == v) continue;
        if (cur.deg[u] >= d || cur.deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int i = 0; i < N0; i++) cur.col[i] = -1;
    for (int s = 0; s < N0; s++) {
        if (cur.col[s] >= 0) continue;
        cur.col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < cur.deg[u]; i++) {
                int v = cur.adj[u][i];
                if (cur.col[v] < 0) {
                    cur.col[v] = 1 - cur.col[u];
                    queue[qt++] = v;
                }
            }
        }
    }
    for (int u = 0; u < N0; u++) {
        for (int i = cur.deg[u] - 1; i >= 0; i--) {
            if (i >= cur.deg[u]) continue;
            int v = cur.adj[u][i];
            if (cur.col[v] == cur.col[u]) del_edge(u, v);
        }
    }

    long long bad = compute_bad();
    const double BETA = 2.0;
    const double T0 = 2.0, T1 = 0.03;
    double E = (double)bad - BETA * cur.nalive;
    if (bad == 0) {
        memcpy(&best, &cur, sizeof(State));
        have_best = 1;
    }

    double t_start = elapsed();
    while (1) {
        double el = elapsed();
        if (el > budget) break;
        double frac = (budget > 0) ? el / budget : 1.0;
        if (frac > 1.0) frac = 1.0;
        double T = T0 * pow(T1 / T0, frac);
        (void)t_start;

        memcpy(&bak, &cur, sizeof(State));
        double r = rndu();
        int ok;
        if (r < 0.35) ok = move_add();
        else if (r < 0.45) ok = move_remove();
        else ok = move_swap();
        if (!ok) continue;

        bad = compute_bad();
        double E2 = (double)bad - BETA * cur.nalive;
        if (E2 <= E || rndu() < exp(-(E2 - E) / T)) {
            E = E2;
            if (bad == 0 && (!have_best || cur.nalive > best.nalive)) {
                memcpy(&best, &cur, sizeof(State));
                have_best = 1;
            }
        } else {
            memcpy(&cur, &bak, sizeof(State));
        }
    }

    State *s = have_best ? &best : &cur;
    static int id[MAXN];
    int n = 0;
    for (int i = 0; i < s->cap; i++) id[i] = s->alive[i] ? n++ : -1;
    long m = 0;
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] > u) m++;
    }
    printf("%d %ld\n", n, m);
    for (int u = 0; u < s->cap; u++) {
        if (!s->alive[u]) continue;
        for (int i = 0; i < s->deg[u]; i++) {
            int v = s->adj[u][i];
            if (v > u) printf("%d %d\n", id[u], id[v]);
        }
    }
}

/* ------------------------------------------------------------------ */

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int mode = atoi(argv[5]);
    int mstart = argc > 6 ? atoi(argv[6]) : 0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (mode == 0) {
        if (d < 2 || d > MAXK - 1) { printf("0 0\n"); return 0; }
        int cap = d * (d - 1) + 1;
        if (mstart <= 0) mstart = (int)(0.8 * cap);
        run_cover(d, budget, mstart);
        return 0;
    }
    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    run_anneal(budget);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective planes (D = 3) and the
# generalized quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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
# C wrapper.
# ----------------------------------------------------------------------------

def _c_run(d, D, seed, budget, mode, mstart, graph=None):
    """Run the C engine; return (n, edges) or None on any failure."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mode, mstart],
                        stdin_graph=graph, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 1:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: best of arc-extended PG graphs and the C difference-cover search
#           (Haar graph of diameter 3), then C penalty annealing from the best.
#   D == 4: W(q) start, then C penalty annealing.
#   else  : K_{d,d} start, then C penalty annealing.
# Calibration cases already at the Moore bound skip the annealing phase.
# Every candidate is checked with lib.is_valid; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    def elapsed():
        return time.monotonic() - start

    # Always-valid fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            for g in _arc_extensions(d, start + 0.06 * T, random.Random(seed * 7919 + d)):
                consider(g)
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    if D == 3 and d >= 2:
        cap = d * (d - 1) + 1
        cover_budget = 0.58 * T - elapsed() - 1.0
        if cover_budget >= 1.0:
            consider(_c_run(d, D, seed, cover_budget, 0, int(0.8 * cap)))

    if D >= 2 and best[0] < lib.moore_bound(d, D):
        anneal_budget = 0.88 * T - elapsed() - 1.0
        if anneal_budget >= 1.0:
            consider(_c_run(d, D, seed, anneal_budget, 1, 0, best))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
