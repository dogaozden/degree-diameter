import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: insertion + simulated-annealing repair on general bipartite graphs.
#
# Starting from a valid graph, repeatedly insert one vertex on the side with
# free degree, wire it to free opposite-side vertices, then anneal with
# degree-preserving edge swaps and add/remove moves. The cost is the number of
# unordered vertex pairs at distance > D (computed with bitset BFS). The first
# zero-cost graph becomes the new incumbent. The output is always a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXDEG 64
#define MAXE 40000
#define ITERS 6000L

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXDEG];
    int ne;
    int eu[MAXE];   /* endpoint on side 0 */
    int ev[MAXE];   /* endpoint on side 1 */
} State;

static State S_best, S_work;
static uint64_t BUFA[MAXN][MAXW], BUFB[MAXN][MAXW];
static int DD, DIAM;
static uint64_t rs = 88172645463325252ULL;
static int defA[MAXN], defB[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++) if (s->nb[a][k] == b) return 1;
    return 0;
}
static void nb_push(State *s, int v, int x) { s->nb[v][s->deg[v]++] = x; }
static void nb_del(State *s, int v, int x) {
    for (int k = 0; k < s->deg[v]; k++) {
        if (s->nb[v][k] == x) {
            s->nb[v][k] = s->nb[v][s->deg[v] - 1];
            s->deg[v]--;
            return;
        }
    }
}
static void nb_sub(State *s, int v, int old, int nw) {
    for (int k = 0; k < s->deg[v]; k++) if (s->nb[v][k] == old) { s->nb[v][k] = nw; return; }
}
/* a on side 0, b on side 1 */
static void add_edge(State *s, int a, int b) {
    s->eu[s->ne] = a; s->ev[s->ne] = b; s->ne++;
    nb_push(s, a, b); nb_push(s, b, a);
}
static void remove_edge_idx(State *s, int i) {
    int a = s->eu[i], b = s->ev[i];
    nb_del(s, a, b); nb_del(s, b, a);
    s->ne--;
    s->eu[i] = s->eu[s->ne];
    s->ev[i] = s->ev[s->ne];
}
/* (a,b),(c,e) -> (a,e),(c,b). Applying it again to the same indices undoes it. */
static int swap_edges(State *s, int i, int j) {
    int a = s->eu[i], b = s->ev[i], c = s->eu[j], e = s->ev[j];
    if (i == j || a == c || b == e) return 0;
    if (has_edge(s, a, e) || has_edge(s, c, b)) return 0;
    nb_sub(s, a, b, e); nb_sub(s, e, c, a);
    nb_sub(s, c, e, b); nb_sub(s, b, a, c);
    s->eu[i] = a; s->ev[i] = e;
    s->eu[j] = c; s->ev[j] = b;
    return 1;
}

/* Number of unordered pairs at distance > DIAM. Zero means valid diameter. */
static int cost(const State *s) {
    int n = s->n;
    if (n <= 1) return 0;
    int W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = BUFA;
    uint64_t (*nxt)[MAXW] = BUFB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < s->deg[v]; k++) {
                const uint64_t *src = cur[s->nb[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static int load_graph(State *s, int n, int m, const int *tu, const int *tv) {
    static int q[MAXN];
    memset(s, 0, sizeof(*s));
    s->n = n;
    for (int i = 0; i < m; i++) {
        int u = tu[i], v = tv[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(s, u, v)) return 0;
        if (s->deg[u] >= MAXDEG || s->deg[v] >= MAXDEG) return 0;
        nb_push(s, u, v); nb_push(s, v, u);
    }
    for (int v = 0; v < n; v++) if (s->deg[v] > DD) return 0;
    for (int v = 0; v < n; v++) s->side[v] = -1;
    for (int st = 0; st < n; st++) {
        if (s->side[st] != -1) continue;
        int qh = 0, qt = 0;
        s->side[st] = 0;
        q[qt++] = st;
        while (qh < qt) {
            int x = q[qh++];
            for (int k = 0; k < s->deg[x]; k++) {
                int y = s->nb[x][k];
                if (s->side[y] == -1) {
                    s->side[y] = 1 - s->side[x];
                    q[qt++] = y;
                } else if (s->side[y] == s->side[x]) {
                    return 0;
                }
            }
        }
    }
    memset(s->deg, 0, sizeof(s->deg));
    s->ne = 0;
    for (int i = 0; i < m; i++) {
        int u = tu[i], v = tv[i];
        if (s->side[u] == 0) add_edge(s, u, v);
        else add_edge(s, v, u);
    }
    return 1;
}

static int insert_vertex(State *s) {
    static int cand[MAXN];
    if (s->n >= MAXN) return 0;
    int sd = rndint(2);
    for (int attempt = 0; attempt < 2; attempt++) {
        int nc = 0;
        for (int u = 0; u < s->n; u++)
            if (s->side[u] != sd && s->deg[u] < DD) cand[nc++] = u;
        if (nc > 0) {
            for (int i = nc - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
            }
            int k = nc < DD ? nc : DD;
            int v = s->n;
            s->side[v] = sd;
            s->deg[v] = 0;
            s->n++;
            for (int i = 0; i < k; i++) {
                int u = cand[i];
                if (sd == 0) add_edge(s, v, u);
                else add_edge(s, u, v);
            }
            return 1;
        }
        sd = 1 - sd;
    }
    int v = s->n;
    s->side[v] = rndint(2);
    s->deg[v] = 0;
    s->n++;
    return 1;
}

static int anneal(State *s, long iters, double T0, double T1, time_t deadline) {
    int c = cost(s);
    if (c == 0) return 1;
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 63) == 0 && time(NULL) >= deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        double r = rnd01();
        int c2 = 0, accept = 0;
        if (r < 0.85) {
            if (s->ne < 2) continue;
            int i = rndint(s->ne), j = rndint(s->ne);
            if (!swap_edges(s, i, j)) continue;
            c2 = cost(s);
            accept = (c2 <= c) || (rnd01() < exp(-(double)(c2 - c) / T));
            if (accept) c = c2;
            else swap_edges(s, i, j);
        } else if (r < 0.97) {
            int na = 0, nb2 = 0;
            for (int v = 0; v < s->n; v++) {
                if (s->deg[v] < DD) {
                    if (s->side[v] == 0) defA[na++] = v;
                    else defB[nb2++] = v;
                }
            }
            if (na == 0 || nb2 == 0) continue;
            int x = defA[rndint(na)], y = defB[rndint(nb2)];
            if (has_edge(s, x, y)) continue;
            add_edge(s, x, y);
            c2 = cost(s);
            accept = (c2 <= c) || (rnd01() < exp(-(double)(c2 - c) / T));
            if (accept) c = c2;
            else remove_edge_idx(s, s->ne - 1);
        } else {
            if (s->ne < 1) continue;
            int i = rndint(s->ne);
            int a = s->eu[i], b = s->ev[i];
            remove_edge_idx(s, i);
            c2 = cost(s);
            accept = (c2 <= c) || (rnd01() < exp(-(double)(c2 - c) / T));
            if (accept) c = c2;
            else add_edge(s, a, b);
        }
    }
    return c == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    long budget = atol(argv[4]);
    time_t t0 = time(NULL);
    time_t deadline = t0 + (time_t)budget;
    (void)t0;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    int *tu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *tv = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &tu[i], &tv[i]) != 2) { printf("0 0\n"); return 0; }
    }
    if (!load_graph(&S_best, n, m, tu, tv)) { printf("0 0\n"); return 0; }
    free(tu);
    free(tv);

    if (cost(&S_best) != 0) {
        S_work = S_best;
        if (anneal(&S_work, 100000L, 1.2, 0.1, deadline)) S_best = S_work;
        else { printf("0 0\n"); return 0; }
    }

    while (time(NULL) < deadline && S_best.n < MAXN) {
        S_work = S_best;
        if (!insert_vertex(&S_work)) break;
        if (anneal(&S_work, ITERS, 1.2, 0.08, deadline)) S_best = S_work;
    }

    printf("%d %d\n", S_best.n, S_best.ne);
    for (int i = 0; i < S_best.ne; i++) printf("%d %d\n", S_best.eu[i], S_best.ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: arc-extended projective planes (diameter 3) and the
# generalized quadrangle W(q) (diameter 4). These give the starting graph.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements with every target hit at most s times."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
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
# Driver: best Python construction, then the C insertion/annealing engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        rng = random.Random(seed * 7919 + d)
        cands = _arc_extensions(d, t0 + 0.15 * time_limit, rng)
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Skip the search when the Moore bound is already met (e.g. calibration cases).
    ub = lib.moore_bound(d, D)
    if best_n < ub:
        remaining = time_limit - (time.monotonic() - t0)
        budget = int(min(0.8 * time_limit, remaining - 6.0))
        if budget >= 3:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                                 stdin_graph=best, timeout=budget + 30.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
