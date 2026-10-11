"""Program for diameter-3 bipartite graphs.

Baseline (safe): projective-plane Moore graphs, Araujo-Pardo-Lopez graphs, and projective
plane arc extensions built in Python. These are always valid.

Bold path (d = q a prime power, d-1 not a prime power, D = 3, d <= 20): start from
PG(2,q) incidence, delete one point P, the points of a line L0 not through P, the lines
through P and L0. Every surviving vertex then has degree exactly q = d, so the graph is
bipartite with max degree d, but its diameter is too large. The C engine
(simulated annealing over induced subgraphs) searches for the largest vertex subset that
is still valid. Its output is re-checked in Python and kept only if it beats the baseline.
"""
import math  # noqa: F401  (kept for parity with the C-side formulas)
import random
import time

import lib

PRUNE_C = r'''
/* Largest valid induced subgraph search for bipartite diameter-D graphs.
 *
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m edges "u v" (bipartite, max degree may exceed d).
 * stdout: "n m" then m edges of the best valid induced subgraph (relabelled 0..k-1),
 *         or "0 0" if none was found.
 *
 * Method: keep a set of alive vertices. Energy = (#pairs at distance > D among alive
 * vertices) + 3 * (sum of alive-degree excess over d). Start with greedy deletion of
 * the worst vertex until energy 0, then annealing with swap moves at fixed size; whenever
 * energy reaches 0 the size is increased by reviving a deleted vertex, and stagnation
 * causes deletion.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 40
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static unsigned char alive[MAXN];
static unsigned char best_alive[MAXN];
static int badv[MAXN], exv[MAXN];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int stale = 1;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Energy of the current alive set; fills badv (unreached alive partners) and exv (excess). */
static long evaluate(void) {
    int na = 0;
    for (int v = 0; v < n; v++) na += alive[v];
    memset(RA, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++)
        if (alive[v]) RA[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    uint64_t *cur = RA, *nxt = RB;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            if (!alive[v]) {
                memset(dst, 0, sizeof(uint64_t) * (size_t)W);
                continue;
            }
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (!alive[u]) continue;
                const uint64_t *s = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long bad2 = 0, exc = 0;
    for (int v = 0; v < n; v++) {
        if (!alive[v]) {
            badv[v] = 0;
            exv[v] = 0;
            continue;
        }
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = na - c;
        bad2 += na - c;
        int ad = 0;
        for (int i = 0; i < deg[v]; i++) ad += alive[adj[v][i]];
        exv[v] = ad > d ? ad - d : 0;
        exc += exv[v];
    }
    return bad2 / 2 + 3 * exc;
}

static long eval_now(void) {
    stale = 0;
    return evaluate();
}

static void refresh(void) {
    if (stale) eval_now();
}

static int count_alive(void) {
    int c = 0;
    for (int v = 0; v < n; v++) c += alive[v];
    return c;
}

/* Alive vertex with the largest local violation (random tie-break), or -1. */
static int pick_worst(void) {
    refresh();
    int best = -1, bs = -1, ties = 0;
    for (int v = 0; v < n; v++) {
        if (!alive[v]) continue;
        int s = badv[v] + 3 * exv[v];
        if (s > bs) {
            bs = s;
            best = v;
            ties = 1;
        } else if (s == bs && rndint(++ties) == 0) {
            best = v;
        }
    }
    return best;
}

/* Random vertex with alive == want (want 0: dead, want 1: alive), or -1. */
static int pick_rand(int want) {
    int start = rndint(n);
    for (int k = 0; k < n; k++) {
        int v = (start + k) % n;
        if ((alive[v] != 0) == (want != 0)) return v;
    }
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.85;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0 ||
        d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        alive[v] = 1;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || deg[u] >= MAXD || deg[v] >= MAXD) {
            printf("0 0\n");
            return 0;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }
    W = (n + 63) / 64;

    int best_cnt = 0;
    long E = eval_now();

    /* Greedy deletion of the worst vertex until the energy is zero. */
    while (E > 0 && now() < t_end) {
        int v = pick_worst();
        if (v < 0) break;
        alive[v] = 0;
        E = eval_now();
    }

    if (E == 0) {
        int c = count_alive();
        if (c > best_cnt) {
            best_cnt = c;
            memcpy(best_alive, alive, (size_t)n);
        }
    }

    long minE = E;
    long stall = 0;
    const double TEMP = 0.8;
    while (now() < t_end) {
        if (E == 0) {
            int c = count_alive();
            if (c > best_cnt) {
                best_cnt = c;
                memcpy(best_alive, alive, (size_t)n);
            }
            int b = pick_rand(0);
            if (b < 0) break;          /* everything alive and valid */
            alive[b] = 1;
            E = eval_now();
            minE = E;
            stall = 0;
            continue;
        }

        int a = rnd01() < 0.5 ? pick_worst() : pick_rand(1);
        if (a < 0) break;
        int b = pick_rand(0);
        if (b < 0) {                   /* no deleted vertex: shrink instead */
            alive[a] = 0;
            E = eval_now();
            minE = E;
            stall = 0;
            continue;
        }

        alive[a] = 0;
        alive[b] = 1;
        long nE = eval_now();
        if (nE <= E || rnd01() < exp(-(double)(nE - E) / TEMP)) {
            E = nE;
        } else {
            alive[a] = 1;
            alive[b] = 0;
            stale = 1;                 /* arrays describe the rejected state */
        }

        if (E < minE) {
            minE = E;
            stall = 0;
        } else if (++stall > 3000) {
            int v = pick_worst();
            if (v >= 0) {
                alive[v] = 0;
                E = eval_now();
            }
            minE = E;
            stall = 0;
        }
    }

    if (best_cnt == 0) {
        printf("0 0\n");
        return 0;
    }
    /* Re-verify the best set before printing. */
    for (int v = 0; v < n; v++) alive[v] = best_alive[v];
    if (eval_now() != 0) {
        printf("0 0\n");
        return 0;
    }
    static int idx[MAXN];
    int k = 0;
    for (int v = 0; v < n; v++) idx[v] = alive[v] ? k++ : -1;
    long me = 0;
    for (int u = 0; u < n; u++) {
        if (!alive[u]) continue;
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (alive[v] && u < v) me++;
        }
    }
    printf("%d %ld\n", k, me);
    for (int u = 0; u < n; u++) {
        if (!alive[u]) continue;
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u][i];
            if (alive[v] && u < v) printf("%d %d\n", idx[u], idx[v]);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3), as in the parent.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements with every target hit <= s times."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, list(range(2 * m, 2 * m + na)), list(range(2 * m + na, n))


def _fill_ab(n, edges, d, A, B):
    """Greedily add A-B edges while both endpoints have spare degree."""
    deg = [0] * n
    have = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        have.add((u, v) if u < v else (v, u))
    E = list(edges)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (a, b) if a < b else (b, a)
            if key in have:
                continue
            have.add(key)
            deg[a] += 1
            deg[b] += 1
            E.append(key)
    return n, E


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, one per prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline)
        SB = _greedy_side(m, s, line_points, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c, A, B = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append(_fill_ab(n_c, e_c, d, A, B))
    return out


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


# ----------------------------------------------------------------------------
# Bold path: PG(2,q) with one point, one line and their pencil/line removed.
# Every surviving vertex has degree exactly q, so with d = q the start has max
# degree d and is bipartite; C prunes it to a valid diameter-3 induced subgraph.
# ----------------------------------------------------------------------------

def _pg_minus_structure(q):
    """Return (n, edges) of PG(2,q) minus point P, the points of line L0 (P not on L0),
    the lines through P, and L0. Surviving degrees are all q."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]          # point -> lines
    lp = [[] for _ in range(m)]          # line -> points
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    P = 0
    L0 = next(j for j in range(m) if P not in lp[j])
    X = set(lp[L0]) | {P}                # deleted points
    Y = set(pl[P]) | {L0}                # deleted lines
    idx = {}
    for p in range(m):
        if p not in X:
            idx[p] = len(idx)
    for j in range(m):
        if j not in Y:
            idx[m + j] = len(idx)
    E = [(idx[u], idx[v]) for u, v in edges if u in idx and v in idx]
    return len(idx), E


def _max_degree(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return max(deg, default=0)


def _bold_applicable(d, D):
    return (D == 3 and 4 <= d <= 20 and lib.is_prime_power(d)
            and not lib.is_prime_power(d - 1))


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        try:
            if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = (cand[0], cand[1])
        except Exception:
            pass

    if D >= 3:
        try:
            consider(known_start(d, D))
        except Exception:
            pass
        try:
            rng = random.Random(seed * 7919 + d)
            for cand in sorted(_arc_candidates(d, t0 + 0.2 * time_limit, rng),
                               key=lambda t: -t[0]):
                consider(cand)
        except Exception:
            pass

    if _bold_applicable(d, D):
        try:
            budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
            if budget > 2.0:
                n0, e0 = _pg_minus_structure(d)
                if _max_degree(n0, e0) <= d:
                    text = lib.run_c(PRUNE_C, [d, D, seed, round(budget, 2)],
                                     stdin_graph=(n0, e0), timeout=budget + 5)
                    n, e = lib.parse_graph_text(text)
                    consider((n, e))
        except Exception:
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
