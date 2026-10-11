"""Diameter-3 bipartite search: arc-extended projective plane starts plus a C engine.

Starts: arc-extended PG(2,q) incidence graphs (plus W(q) for D >= 4) and K_{d,d}.

C engine, two phases:
  1. Greedy augmentation (as before): add a vertex joined to a greedy set cover T of
     spare vertices, accepted only if every vertex is within D-1 of T.
  2. NEW: annealed insertion. When greedy stalls, add a vertex on a random side, attach it
     greedily to spare vertices, then anneal the whole graph with degree- and bipartition-
     preserving moves (double-edge swaps, edge adds, edge removals). The objective is the
     number of vertex pairs at distance > D. A move is kept by the Metropolis rule. If the
     objective reaches 0 the graph is valid with one more vertex; otherwise it is rolled back.

Python re-checks every output with lib.is_valid and keeps a valid fallback.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static uint64_t tb[WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int sN;
static int sdeg[MAXN];
static int sadj[MAXN][MAXDEG];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double unif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of all vertices within distance r of src. */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* ---- edge primitives ---- */
static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}
static void del_arc(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
}
static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Number of ordered vertex pairs (v,w), v != w, at distance > Dist. */
static long bad_count(void) {
    long bad = 0;
    for (int v = 0; v < N; v++) {
        ball_of(v, Dist, tb);
        int c = 0;
        for (int i = 0; i < W; i++) c += popc(tb[i]);
        bad += N - c;
    }
    return bad;
}

static void save_state(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(int) * N);
    memcpy(sadj, adj, sizeof(int) * N * MAXDEG);
}
static void restore_state(void) {
    N = sN;
    W = (N + 63) / 64;
    memcpy(deg, sdeg, sizeof(int) * N);
    memcpy(adj, sadj, sizeof(int) * N * MAXDEG);
}

/* Greedy augmentation: add one vertex on side X joined to a set cover of balls. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = 0;
    N++;
    W = (N + 63) / 64;
    for (int k = 0; k < nt; k++) add_edge(x, T[k]);
    recompute_balls();
    return 1;
}

/* ---- annealed insertion (new) ---- */
typedef struct { int type, a, b, c, d; } Move;

/* Random edge oriented so that a is on side 0 and b on side 1. */
static int rand_edge(int *a, int *b) {
    for (int t = 0; t < 64; t++) {
        int u = rndint(N);
        if (!deg[u]) continue;
        int w = adj[u][rndint(deg[u])];
        if (side[u] == 0) { *a = u; *b = w; }
        else { *a = w; *b = u; }
        return 1;
    }
    return 0;
}

static int rand_spare(int s) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] < Dd) return v;
    }
    return -1;
}

/* Propose a degree- and bipartition-preserving move and apply it. */
static int propose(Move *m) {
    int r = rndint(100);
    if (r < 70) {                      /* double-edge swap */
        int a, b, c, d;
        if (!rand_edge(&a, &b) || !rand_edge(&c, &d)) return 0;
        if (a == c || b == d) return 0;
        if (has_edge(a, d) || has_edge(c, b)) return 0;
        del_edge(a, b);
        del_edge(c, d);
        add_edge(a, d);
        add_edge(c, b);
        m->type = 1; m->a = a; m->b = b; m->c = c; m->d = d;
        return 1;
    } else if (r < 92) {               /* add an edge between spare vertices */
        int a = rand_spare(0), b = rand_spare(1);
        if (a < 0 || b < 0 || has_edge(a, b)) return 0;
        add_edge(a, b);
        m->type = 2; m->a = a; m->b = b;
        return 1;
    } else {                           /* remove an edge */
        int a, b;
        if (!rand_edge(&a, &b)) return 0;
        del_edge(a, b);
        m->type = 3; m->a = a; m->b = b;
        return 1;
    }
}

static void undo(const Move *m) {
    if (m->type == 1) {
        del_edge(m->a, m->d);
        del_edge(m->c, m->b);
        add_edge(m->a, m->b);
        add_edge(m->c, m->d);
    } else if (m->type == 2) {
        del_edge(m->a, m->b);
    } else {
        add_edge(m->a, m->b);
    }
}

/* Add a vertex on side X and anneal until every pair is within Dist.
   Returns 1 on success (graph grows by one valid vertex), 0 after rollback. */
static int try_insert(int X, int iters, double T0) {
    if (N + 1 >= MAXN) return 0;
    save_state();
    int x = N;
    side[x] = X;
    deg[x] = 0;
    N++;
    W = (N + 63) / 64;
    int cnt = 0;
    for (int t = 0; t < 8 * N && cnt < Dd; t++) {
        int v = rndint(N - 1);
        if (side[v] == X || deg[v] >= Dd || has_edge(x, v)) continue;
        add_edge(x, v);
        cnt++;
    }
    long bad = bad_count();
    for (int it = 0; it < iters && bad > 0; it++) {
        double T = T0 * (1.0 - (double)it / iters) + 0.02;
        Move m;
        if (!propose(&m)) continue;
        long nb = bad_count();
        long dl = nb - bad;
        if (dl <= 0 || unif() < exp(-(double)dl / T)) bad = nb;
        else undo(&m);
    }
    if (bad == 0) {
        recompute_balls();
        return 1;
    }
    restore_state();
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int iters = (argc > 5) ? atoi(argv[5]) : 800;
    double T0 = (argc > 6) ? atof(argv[6]) : 1.5;
    if (iters < 1) iters = 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int gfail = 0, afail = 0;
    while (elapsed() < t_end && N < MAXN - 2) {
        int X = rndint(2);
        if (try_add(X)) {
            gfail = 0;
            afail = 0;
            continue;
        }
        gfail++;
        if (gfail < 4) continue;          /* greedy stalled: switch to annealing */
        if (try_insert(X, iters, T0)) {
            gfail = 0;
            afail = 0;
        } else {
            afail++;
            if (afail > 40) break;
        }
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""

ITERS = 800
T0 = 1.5


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# C driver.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", ITERS, f"{T0:.3f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.20 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.20 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    # Most of the time goes to the largest starts; each run augments the previous result.
    plan = starts[:2]
    for idx in range(len(plan) + 1):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if idx < len(plan):
            src = plan[idx]
            share = remaining * (0.6 if idx == 0 else 0.4)
        else:
            src = best
            share = remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
