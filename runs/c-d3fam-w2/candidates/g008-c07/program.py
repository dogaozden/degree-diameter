"""Island program for the D = 3 targets (d = 11, 13, 15).

Python builds the best known start: the Araujo-Pardo and Lopez record, a projective plane,
or a PG-based extension. Then C runs a different search from the parent, which used
Haar graphs, voltage lifts and swap annealing with random restarts. The new C engine treats
D = 3 as a covering problem. In a bipartite graph of diameter 3, two vertices on the same side
must share a neighbour, so the search minimises the number of same-side pairs with no common
neighbour. A degree-preserving 2-switch changes that count in O(d) time. Half of the proposals
are targeted: they pick an uncovered same-side pair and create a common neighbour for it. The
engine grows the graph one vertex pair at a time and anneals after each insertion. Every
accepted state is checked by a full BFS. The Python fallback is always valid, so a C failure
only costs time.

For D != 3 the program returns the Python construction without calling C. This island does
not score those cases, so the parent's C search for D >= 4 is intentionally dropped here.
"""
import itertools
import random
import time

import lib

GQ_Q_MAX = 7      # largest q for which W(q) is built in Python (D >= 4 only)
TIME_FRAC = 0.85  # fraction of time_limit given to the C engine

C_SOURCE = r'''
/* Bipartite degree-diameter search for D = 3 by covering annealing.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the best valid graph found.
 *
 * With D = 3 and a bipartite graph, every pair on the same side must have a common neighbour.
 * cnt[x][y] = number of common neighbours of same-side pair (x,y); cost = number of same-side
 * pairs with cnt 0. Degree-preserving 2-switches update cnt in O(d). A state with cost 0 is
 * accepted only after a full BFS shows diameter <= D.
 * Growth: insert one vertex per side (rewiring d-1 edges), anneal, keep on success.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 600
#define MAXD 32

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
} Graph;

static int d, D;
static double t_end;
static Graph cur, best;
static int cnt[MAXV][MAXV];
static long cost;
static int list0[MAXV], n0, list1[MAXV], n1;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ edge primitives */

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void raw_add(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void half_del(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void raw_del(Graph *g, int u, int v) {
    half_del(g, u, v);
    half_del(g, v, u);
}

/* Change the common-neighbour count of the same-side pair (x,y) by dl, keeping cost exact. */
static void bump(int x, int y, int dl) {
    int c = cnt[x][y];
    if (dl > 0) {
        if (c == 0) cost--;
        c++;
    } else {
        c--;
        if (c == 0) cost++;
    }
    cnt[x][y] = c;
    cnt[y][x] = c;
}

/* Add edge (a,b) to cur, updating cnt and cost. */
static void add_e(int a, int b) {
    for (int i = 0; i < cur.deg[b]; i++) {
        int x = cur.adj[b][i];
        if (x != a) bump(a, x, 1);
    }
    for (int i = 0; i < cur.deg[a]; i++) {
        int y = cur.adj[a][i];
        if (y != b) bump(b, y, 1);
    }
    raw_add(&cur, a, b);
}

/* Remove edge (a,b) from cur, updating cnt and cost. */
static void rem_e(int a, int b) {
    for (int i = 0; i < cur.deg[b]; i++) {
        int x = cur.adj[b][i];
        if (x != a) bump(a, x, -1);
    }
    for (int i = 0; i < cur.deg[a]; i++) {
        int y = cur.adj[a][i];
        if (y != b) bump(b, y, -1);
    }
    raw_del(&cur, a, b);
}

/* Recompute cnt, cost and the side lists of cur from scratch. */
static void rebuild(void) {
    int N = cur.n;
    memset(cnt, 0, sizeof cnt);
    for (int b = 0; b < N; b++)
        for (int i = 0; i < cur.deg[b]; i++)
            for (int j = i + 1; j < cur.deg[b]; j++) {
                int x = cur.adj[b][i], y = cur.adj[b][j];
                cnt[x][y]++;
                cnt[y][x]++;
            }
    n0 = n1 = 0;
    for (int v = 0; v < N; v++) {
        if (cur.side[v]) list1[n1++] = v;
        else list0[n0++] = v;
    }
    cost = 0;
    for (int i = 0; i < n0; i++)
        for (int j = i + 1; j < n0; j++)
            if (cnt[list0[i]][list0[j]] == 0) cost++;
    for (int i = 0; i < n1; i++)
        for (int j = i + 1; j < n1; j++)
            if (cnt[list1[i]][list1[j]] == 0) cost++;
}

/* ------------------------------------------------------------ validity */

/* Every pair within distance D (BFS from each vertex). */
static int full_ok(const Graph *g) {
    static int dist[MAXV], q[MAXV];
    for (int s = 0; s < g->n; s++) {
        for (int v = 0; v < g->n; v++) dist[v] = -1;
        int h = 0, t = 0, reached = 1;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    reached++;
                    q[t++] = u;
                }
            }
        }
        if (reached != g->n) return 0;
    }
    return 1;
}

static int valid_graph(const Graph *g) {
    if (g->n <= 0 || g->n > MAXV) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
        }
    }
    return full_ok(g);
}

/* ------------------------------------------------------------ I/O and start graphs */

static void make_kdd(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) raw_add(g, a, d + b);
}

static void read_start(void) {
    static Graph tmp;
    static int q[MAXV];
    int n, m;
    best.n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV || m < 0) return;
    tmp.n = n;
    for (int v = 0; v < n; v++) {
        tmp.deg[v] = 0;
        tmp.side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return;
        if (tmp.deg[u] >= MAXD || tmp.deg[v] >= MAXD) return;
        if (has_edge(&tmp, u, v)) return;
        raw_add(&tmp, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (tmp.side[s] != 255) continue;
        int h = 0, t = 0;
        tmp.side[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < tmp.deg[v]; i++) {
                int u = tmp.adj[v][i];
                if (tmp.side[u] == 255) {
                    tmp.side[u] = 1 - tmp.side[v];
                    q[t++] = u;
                } else if (tmp.side[u] == tmp.side[v]) {
                    return;
                }
            }
        }
    }
    if (valid_graph(&tmp)) best = tmp;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ------------------------------------------------------------ annealing */

/* Propose a degree-preserving 2-switch: remove (a1,b1),(a2,b2), add (a1,b2),(a2,b1). */
static int propose(int *A1, int *B1, int *A2, int *B2) {
    int a1, b1, a2, b2;
    if (rndint(2) == 0) {
        /* Targeted: a1 gains a common neighbour with an uncovered same-side partner y. */
        a1 = list0[rndint(n0)];
        if (cur.deg[a1] == 0) return 0;
        static int zs[MAXV];
        int nz = 0;
        for (int i = 0; i < n0; i++) {
            int y = list0[i];
            if (y != a1 && cnt[a1][y] == 0) zs[nz++] = y;
        }
        if (nz == 0) return 0;
        int y = zs[rndint(nz)];
        if (cur.deg[y] == 0) return 0;
        b2 = cur.adj[y][rndint(cur.deg[y])];
        if (cur.deg[b2] == 0) return 0;
        a2 = cur.adj[b2][rndint(cur.deg[b2])];
        b1 = cur.adj[a1][rndint(cur.deg[a1])];
    } else {
        a1 = list0[rndint(n0)];
        if (cur.deg[a1] == 0) return 0;
        b1 = cur.adj[a1][rndint(cur.deg[a1])];
        a2 = list0[rndint(n0)];
        if (cur.deg[a2] == 0) return 0;
        b2 = cur.adj[a2][rndint(cur.deg[a2])];
    }
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(&cur, a1, b2) || has_edge(&cur, a2, b1)) return 0;
    *A1 = a1;
    *B1 = b1;
    *A2 = a2;
    *B2 = b2;
    return 1;
}

/* Anneal swaps on cur until cost 0 with full validity, or until the deadline. */
static int anneal(double until) {
    double T = 0.7;
    long it = 0;
    for (;;) {
        it++;
        if (cost == 0 && (it & 63) == 1 && full_ok(&cur)) return 1;
        if ((it & 255) == 0 && now() > until) return 0;
        int a1, b1, a2, b2;
        if (!propose(&a1, &b1, &a2, &b2)) continue;
        long old = cost;
        rem_e(a1, b1);
        rem_e(a2, b2);
        add_e(a1, b2);
        add_e(a2, b1);
        long dl = cost - old;
        if (dl > 0 && rnd01() >= exp(-(double)dl / T)) {
            rem_e(a2, b1);
            rem_e(a1, b2);
            add_e(a1, b1);
            add_e(a2, b2);
        }
        T *= 0.99997;
        if (T < 0.12) T = 0.7;
    }
}

/* Add one vertex per side to cur. The new vertices x (side 0) and y (side 1) take d-1 edges
 * from disjoint old edges (a,b) by the rule del(a,b), add(x,b), add(y,a), plus the edge (x,y). */
static int insert_pair(void) {
    if (cur.n + 2 > moore_bound() || cur.n + 2 > MAXV) return 0;
    static int used[MAXV];
    static int stamp = 0;
    stamp++;
    int x = cur.n, y = cur.n + 1;
    cur.n += 2;
    cur.deg[x] = cur.deg[y] = 0;
    cur.side[x] = 0;
    cur.side[y] = 1;
    used[x] = used[y] = stamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = list0[rndint(n0)];
        if (cur.deg[a] == 0) continue;
        int b = cur.adj[a][rndint(cur.deg[a])];
        if (used[a] == stamp || used[b] == stamp) continue;
        raw_del(&cur, a, b);
        raw_add(&cur, x, b);
        raw_add(&cur, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    raw_add(&cur, x, y);
    rebuild();
    return 1;
}

/* Grow best one pair at a time. Each attempt starts from best with a new random insertion. */
static void grow(void) {
    while (now() < t_end) {
        double rem = t_end - now();
        double slice = rem / 4.0;
        if (slice < 3.0) slice = rem;
        cur = best;
        if (!insert_pair()) return;
        double until = now() + slice;
        if (until > t_end) until = t_end;
        if (anneal(until)) best = cur;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start();
    if (best.n == 0) make_kdd(&best);
    if (D == 3 && d >= 3 && best.n < moore_bound()) grow();
    if (!valid_graph(&best)) make_kdd(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- Python constructions

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best known construction Python builds directly for (d, D), or None."""
    if D == 3:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)       # Moore graph, optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                return lib.araujo_lopez_graph(d - 2)           # record 2(q^2+q+5), q = d-2
            except ValueError:
                return None
        return None
    if D >= 4:
        return _best_gq(d)
    return None


def _two_colour(n, edges):
    """Proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree (keeps bipartite)."""
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices whose neighbourhoods cover all radius-(D-1) balls (keeps diameter D)."""
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _finish(cands, d, D):
    """Largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]           # K_{d,d}: always valid

    start = None
    try:
        start = known_start(d, D)
    except Exception:
        start = None
    if start is not None and not lib.is_valid(start[0], start[1], d, D):
        start = None
    if start is not None:
        cands.append(start)
    elif d >= 3 and D == 3:
        try:
            base = _pg_base(d)
            if base is not None:
                cands.append(base)
                aug = _augment(base[0], base[1], d, seed)
                cands.append(_extend(aug[0], aug[1], d, D, rng,
                                     time.monotonic() + 0.05 * time_limit))
        except Exception:
            pass

    best = _finish(cands, d, D)

    # The covering search is only used for the D = 3 targets.
    if D != 3 or d < 3:
        return best

    # Moore-extremal start: nothing to search for.
    if start is not None and start[0] >= lib.moore_bound(d, D):
        return best

    budget = TIME_FRAC * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 1.0:
        stdin_graph = best if best[0] > 2 * d else None
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=stdin_graph, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass                                    # keep the valid Python fallback
    return best
