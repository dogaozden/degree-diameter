"""Vertex-growth search for bipartite graphs with max degree d and diameter D.

Pipeline:
1. Python builds valid starting graphs: Haar K_{d,d}, the projective plane
   incidence graph PG(2, q), the Araujo-Pardo-Lopez graph, and arc-extended
   projective plane graphs (the parent's best source). Each is checked with
   lib.is_valid, and the largest valid one is kept.
2. The C engine takes that graph and grows it one vertex at a time. Adding a
   vertex v connects it greedily to spare-degree vertices on the other side. Then
   simulated annealing over degree-respecting moves (add an edge into spare
   capacity, degree-preserving double edge swap, or shift one endpoint of an edge)
   minimises the number of vertex pairs at distance > D. Reaching zero commits the
   larger graph. Otherwise the state is restored to the last valid graph.
3. Python re-validates the C output and falls back to the best Python graph.
"""
import itertools
import math
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

#define MAXN 1200
#define MAXDEG 128
#define MAXW ((MAXN + 63) / 64)

static int d_, D_;
static int n;
static int side[MAXN];
static int deg[MAXN];
static int adjl[MAXN][MAXDEG];
static unsigned char adjm[MAXN][MAXN];

static int bestn = 0;
static int bdeg[MAXN];
static int badj[MAXN][MAXDEG];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static uint64_t ball[2][MAXN][MAXW];

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D_ (unreachable counts as bad). */
static long long bad_pairs(void) {
    int nw = (n + 63) >> 6;
    int cur = 0;
    for (int v = 0; v < n; v++) {
        memset(ball[0][v], 0, sizeof(uint64_t) * nw);
        ball[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = ball[nx][v];
            memcpy(dst, ball[cur][v], sizeof(uint64_t) * nw);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = ball[cur][adjl[v][k]];
                for (int w = 0; w < nw; w++) dst[w] |= src[w];
            }
        }
        cur = nx;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc64(ball[cur][v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void add_edge(int a, int b) {
    adjl[a][deg[a]++] = b;
    adjl[b][deg[b]++] = a;
    adjm[a][b] = 1;
    adjm[b][a] = 1;
}

static void rem_from(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adjl[a][k] == b) {
            adjl[a][k] = adjl[a][--deg[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    rem_from(a, b);
    rem_from(b, a);
    adjm[a][b] = 0;
    adjm[b][a] = 0;
}

typedef struct {
    int nr;
    int ra[2], rb[2];
    int na;
    int aa[2], ab[2];
} Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_edge(m->ra[i], m->rb[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->aa[i], m->ab[i]);
}

static void revert_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->aa[i], m->ab[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ra[i], m->rb[i]);
}

/* Random vertex on side s; needspare: deg < d_, otherwise deg > 0. */
static int pick_vertex(int s, int needspare) {
    for (int t = 0; t < 400; t++) {
        int v = rndint(n);
        if (side[v] != s) continue;
        if (needspare ? (deg[v] < d_) : (deg[v] > 0)) return v;
    }
    return -1;
}

static int gen_add(Move *m) {
    int x = pick_vertex(0, 1), y = pick_vertex(1, 1);
    if (x < 0 || y < 0 || adjm[x][y]) return 0;
    m->nr = 0;
    m->na = 1;
    m->aa[0] = x;
    m->ab[0] = y;
    return 1;
}

/* Degree-preserving double edge swap: (a,b),(c,dd) -> (a,dd),(c,b). */
static int gen_swap(Move *m) {
    int a = pick_vertex(0, 0), c = pick_vertex(0, 0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adjl[a][rndint(deg[a])];
    int dd = adjl[c][rndint(deg[c])];
    if (b == dd) return 0;
    if (adjm[a][dd] || adjm[c][b]) return 0;
    m->nr = 2;
    m->ra[0] = a; m->rb[0] = b;
    m->ra[1] = c; m->rb[1] = dd;
    m->na = 2;
    m->aa[0] = a; m->ab[0] = dd;
    m->aa[1] = c; m->ab[1] = b;
    return 1;
}

/* Move one endpoint of an existing edge onto a spare-degree vertex. */
static int gen_shift(Move *m) {
    int a = pick_vertex(0, 0);
    if (a < 0) return 0;
    int b = adjl[a][rndint(deg[a])];
    if (rndint(2)) {
        int x = pick_vertex(0, 1);
        if (x < 0 || x == a || adjm[x][b]) return 0;
        m->nr = 1; m->ra[0] = a; m->rb[0] = b;
        m->na = 1; m->aa[0] = x; m->ab[0] = b;
    } else {
        int y = pick_vertex(1, 1);
        if (y < 0 || y == b || adjm[a][y]) return 0;
        m->nr = 1; m->ra[0] = a; m->rb[0] = b;
        m->na = 1; m->aa[0] = a; m->ab[0] = y;
    }
    return 1;
}

static void save_best(void) {
    bestn = n;
    for (int v = 0; v < n; v++) {
        bdeg[v] = deg[v];
        memcpy(badj[v], adjl[v], sizeof(int) * deg[v]);
    }
}

static void restore_best(void) {
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++) adjm[v][adjl[v][k]] = 0;
    n = bestn;
    for (int v = 0; v < n; v++) {
        deg[v] = bdeg[v];
        memcpy(adjl[v], badj[v], sizeof(int) * bdeg[v]);
        for (int k = 0; k < deg[v]; k++) adjm[v][adjl[v][k]] = 1;
    }
    deg[n] = 0;
}

/* Vertex n-1 was just added with deg 0. Try to make the graph valid by annealing. */
static int attempt(clock_t dl, long maxsteps) {
    int v = n - 1;
    int order[MAXN];
    int cnt = 0;
    for (int u = 0; u < v; u++)
        if (side[u] != side[v]) order[cnt++] = u;
    for (int i = cnt - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = order[i];
        order[i] = order[j];
        order[j] = t;
    }
    for (int i = 0; i < cnt && deg[v] < d_; i++)
        if (deg[order[i]] < d_) add_edge(v, order[i]);

    long long cost = bad_pairs();
    const double T0 = 2.0, T1 = 0.05;
    for (long s = 0; s < maxsteps && cost > 0; s++) {
        if ((s & 255) == 0 && clock() > dl) break;
        double T = T0 * pow(T1 / T0, (double)s / (double)maxsteps);
        Move m;
        double r = rnd01();
        int ok;
        if (r < 0.2) ok = gen_add(&m);
        else if (r < 0.6) ok = gen_swap(&m);
        else ok = gen_shift(&m);
        if (!ok) continue;
        apply_move(&m);
        long long c2 = bad_pairs();
        long long delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = c2;
        else revert_move(&m);
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = 88172645463325252ULL ^ (seed * 0x9E3779B97F4A7C15ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d_ < 1 || d_ > MAXDEG - 8 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    clock_t dl = clock() + (clock_t)(budget * CLOCKS_PER_SEC);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || n0 > MAXN || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
            deg[u] >= d_ || deg[v] >= d_) { ok = 0; break; }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    if (n == 0) {
        n = 2 * d_;
        for (int u = 0; u < d_; u++)
            for (int v = d_; v < 2 * d_; v++) add_edge(u, v);
    }

    /* Bipartition by BFS. */
    int col[MAXN], q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t && ok) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adjl[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[t++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) side[v] = col[v];

    if (bad_pairs() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    int fails = 0;
    while (clock() < dl && bestn + 1 < MAXN) {
        n = bestn + 1;
        side[n - 1] = rndint(2);
        deg[n - 1] = 0;
        long maxsteps = 20000L * (1 + fails / 4);
        if (attempt(dl, maxsteps)) {
            save_best();
            fails = 0;
        } else {
            restore_best();
            fails++;
        }
    }
    restore_best();

    int m = 0;
    for (int v = 0; v < bestn; v++)
        for (int k = 0; k < bdeg[v]; k++)
            if (badj[v][k] > v) m++;
    printf("%d %d\n", bestn, m);
    for (int v = 0; v < bestn; v++)
        for (int k = 0; k < bdeg[v]; k++)
            if (badj[v][k] > v) printf("%d %d\n", v, badj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with deletions.
# Used only as a source of starting graphs; every candidate is validated.
# ----------------------------------------------------------------------------

_LS_ITERS = 12000


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


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by <= caps[t] elements of S."""
    m = len(caps)
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(m))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy capacitated set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, caps, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the capacitated set problem."""
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= caps[t]:
                if not cur:
                    ok = False
                    break
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _best_side(m, caps, nbr, rng, deadline, seeds):
    """Best capacitated set found by greedy, supplied seeds, then local search."""
    cands = [_greedy_side(m, caps, nbr, rng, 12, deadline)]
    for S in seeds:
        if _loads_ok(S, caps, nbr):
            cands.append(list(S))
    start = max(cands, key=len)
    return _local_search(m, caps, nbr, start, rng, deadline, _LS_ITERS)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences, as (point, line) pairs."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus A-vertices and B-vertices."""
    Rset = set(R)
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
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
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs[trial] if trial < len(rs) else rng.choice(rs)
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r > 0 else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            seeds = [conic] if not R else []
            SA = _best_side(m, capL, point_lines, rng, q_deadline, seeds)
            SB = _best_side(m, capP, line_points, rng, q_deadline, seeds)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
            if trial > 40:
                break
    out.sort(key=lambda t: -t[0])
    return out[:30]


def _largest_pp_leq(x, lo):
    """Largest prime power q with lo <= q <= x, or None."""
    for q in range(x, lo - 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    hard = t0 + 0.85 * time_limit - 1.0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Starting graphs with diameter 3 (valid for any D >= 3).
    q = _largest_pp_leq(d - 1, 2)
    if q is not None:
        consider(*lib.projective_plane_incidence(q))
    qa = _largest_pp_leq(d - 2, 3)
    if qa is not None:
        try:
            consider(*lib.araujo_lopez_graph(qa))
        except ValueError:
            pass
    arc_deadline = t0 + 0.3 * (hard - t0)
    for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
        consider(n_c, e_c)

    # Vertex-growth search in C, starting from the best valid graph found so far.
    budget = hard - time.monotonic() - 2.0
    if budget >= 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 5.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
