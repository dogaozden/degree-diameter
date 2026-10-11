import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: "spare-slot vertex insertion with degree-preserving repair".
#
# State: a bipartite graph (sides 0/1), max degree d, cost = number of unordered
# vertex pairs at distance > D (bitset BFS). Moves:
#   * 2-switch (p,q),(p2,q2) -> (p,q2),(p2,q): keeps every degree and bipartiteness;
#     accepted by Metropolis on the cost.
#   * saturate: greedily add edges between spare vertices on opposite sides. This
#     never raises the cost, so it runs after every insertion.
#   * grow: add one vertex on a random side, join it to d vertices on the other
#     side (spare ones first, then "steal" one edge from a saturated vertex).
# Whenever cost hits 0 we save the graph as the anchor and grow again. If the
# search stagnates, we restore the anchor and retry the insertion with new randomness.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1100
#define MAXDEG 128
#define NW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2)
#define STAG_LIMIT 40000

static int DD, DIAM, n;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static unsigned char am[MAXN][MAXN];
static int slist[2][MAXN];
static int nside[2];
static uint64_t RA[MAXN][NW];
static uint64_t RB[MAXN][NW];
static int anc_n, anc_m, have_valid;
static int anc_side[MAXN];
static int anc_eu[MAXE], anc_ev[MAXE];
static int last_p, last_q, last_p2, last_q2;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static clock_t c0;
static time_t w0;

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static unsigned rndi(unsigned k) { return (unsigned)(rnd64() % k); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rm_nb(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    am[a][b] = 1;
    am[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    am[a][b] = 0;
    am[b][a] = 0;
    rm_nb(a, b);
    rm_nb(b, a);
}

static void clear_graph(void) {
    memset(am, 0, sizeof am);
    memset(deg, 0, sizeof deg);
    nside[0] = 0;
    nside[1] = 0;
    n = 0;
}

static long long eval_bad(void) {
    int nw = (n + 63) >> 6;
    uint64_t (*cur)[NW] = RA;
    uint64_t (*nxt)[NW] = RB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt[v];
            const uint64_t *self = cur[v];
            for (int w = 0; w < nw; w++) o[w] = self[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *in = cur[nb[v][k]];
                for (int w = 0; w < nw; w++) o[w] |= in[w];
            }
        }
        uint64_t (*tmp)[NW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long unreached = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc64(cur[v][w]);
        unreached += n - c;
    }
    return unreached / 2;
}

static void saturate(void) {
    int m0 = nside[0], m1 = nside[1];
    if (m0 == 0 || m1 == 0) return;
    for (int i = 0; i < m0; i++) {
        int p = slist[0][i];
        if (deg[p] >= DD) continue;
        int off = (int)rndi((unsigned)m1);
        for (int k = 0; k < m1 && deg[p] < DD; k++) {
            int q = slist[1][(off + k) % m1];
            if (deg[q] < DD && !am[p][q]) add_edge(p, q);
        }
    }
}

static void shuffle_list(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = (int)rndi((unsigned)(i + 1));
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static void grow_vertex(void) {
    int s = (int)(rnd64() & 1ULL);
    int t = 1 - s;
    int v = n++;
    side[v] = s;
    deg[v] = 0;
    slist[s][nside[s]++] = v;
    shuffle_list(slist[t], nside[t]);
    for (int i = 0; i < nside[t] && deg[v] < DD; i++) {
        int u = slist[t][i];
        if (deg[u] < DD) add_edge(u, v);
    }
    for (int i = 0; i < nside[t] && deg[v] < DD; i++) {
        int u = slist[t][i];
        if (am[u][v] || deg[u] < DD) continue;
        int x = nb[u][rndi((unsigned)deg[u])];
        del_edge(u, x);
        add_edge(u, v);
    }
    saturate();
}

static int last_valid_switch;

static int try_switch(void) {
    if (nside[0] < 2 || nside[1] < 2) return 0;
    int p = slist[0][rndi((unsigned)nside[0])];
    int p2 = slist[0][rndi((unsigned)nside[0])];
    if (p == p2 || deg[p] == 0 || deg[p2] == 0) return 0;
    int q = nb[p][rndi((unsigned)deg[p])];
    int q2 = nb[p2][rndi((unsigned)deg[p2])];
    if (q == q2 || am[p][q2] || am[p2][q]) return 0;
    del_edge(p, q);
    del_edge(p2, q2);
    add_edge(p, q2);
    add_edge(p2, q);
    last_p = p;
    last_q = q;
    last_p2 = p2;
    last_q2 = q2;
    return 1;
}

static void undo_switch(void) {
    del_edge(last_p, last_q2);
    del_edge(last_p2, last_q);
    add_edge(last_p, last_q);
    add_edge(last_p2, last_q2);
}

static void build_complete(int d) {
    clear_graph();
    n = 2 * d;
    for (int v = 0; v < n; v++) {
        side[v] = (v < d) ? 0 : 1;
        slist[side[v]][nside[side[v]]++] = v;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(i, d + j);
}

static int load_graph(int n0, int m0, const int *eu, const int *ev) {
    clear_graph();
    if (n0 < 1 || n0 > MAXN - 4) return 0;
    n = n0;
    for (int i = 0; i < m0; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) return 0;
        if (am[a][b]) return 0;
        if (deg[a] >= DD || deg[b] >= DD) return 0;
        add_edge(a, b);
    }
    int col[MAXN];
    int queue[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s0 = 0; s0 < n; s0++) {
        if (col[s0] >= 0) continue;
        col[s0] = 0;
        int h = 0, t = 0;
        queue[t++] = s0;
        while (h < t) {
            int u = queue[h++];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue[t++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) {
        side[v] = col[v];
        slist[side[v]][nside[side[v]]++] = v;
    }
    return 1;
}

static void save_anchor(void) {
    anc_n = n;
    anc_m = 0;
    for (int v = 0; v < n; v++) {
        anc_side[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (u > v) {
                anc_eu[anc_m] = v;
                anc_ev[anc_m] = u;
                anc_m++;
            }
        }
    }
}

static void restore_anchor(void) {
    clear_graph();
    n = anc_n;
    for (int v = 0; v < n; v++) {
        side[v] = anc_side[v];
        slist[side[v]][nside[side[v]]++] = v;
    }
    for (int i = 0; i < anc_m; i++) add_edge(anc_eu[i], anc_ev[i]);
}

static int time_up(double budget) {
    double el = (double)(clock() - c0) / (double)CLOCKS_PER_SEC;
    if (el >= budget) return 1;
    return difftime(time(NULL), w0) >= budget + 1.0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    c0 = clock();
    w0 = time(NULL);
    if (d < 1 || DIAM < 1 || d > MAXDEG - 2 || 2 * d > MAXN - 4) {
        printf("0 0\n");
        return 0;
    }
    DD = d;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    int loaded = 0;
    if (n0 > 0 && m0 >= 0 && m0 <= MAXE) {
        int *eu = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
        int *ev = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
        int good = 1;
        for (int i = 0; i < m0 && good; i++) {
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) good = 0;
        }
        if (good) loaded = load_graph(n0, m0, eu, ev);
        free(eu);
        free(ev);
    }
    if (!loaded) build_complete(d);

    long long cur = eval_bad();
    saturate();
    cur = eval_bad();
    have_valid = (cur == 0);
    save_anchor();

    double T = 0.2 + rndu();
    long long stag = 0;

    while (!time_up(budget)) {
        if (cur == 0) {
            have_valid = 1;
            save_anchor();
            if (n >= MAXN - 3) break;
            grow_vertex();
            cur = eval_bad();
            stag = 0;
            T = 0.2 + rndu();
            continue;
        }
        if (stag >= STAG_LIMIT) {
            restore_anchor();
            if (n >= MAXN - 3) break;
            grow_vertex();
            cur = eval_bad();
            stag = 0;
            T = 0.2 + rndu();
            continue;
        }
        stag++;
        if (!try_switch()) continue;
        long long nxt = eval_bad();
        if (nxt <= cur) {
            cur = nxt;
        } else {
            double x = (double)(nxt - cur);
            if (rndu() < exp(-x / T)) cur = nxt;
            else undo_switch();
        }
    }
    if (cur == 0) {
        have_valid = 1;
        save_anchor();
    }
    if (have_valid) {
        printf("%d %d\n", anc_n, anc_m);
        for (int i = 0; i < anc_m; i++) printf("%d %d\n", anc_eu[i], anc_ev[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python construction: PG(2,q) incidence extended by arcs (diameter 3).
# Old vertices have degree q+1; spare degree s = d-q-1 is used by new vertices.
# ----------------------------------------------------------------------------

def _pg(q):
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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _arc_candidate(q, s, rng, deadline):
    """PG(2,q) plus a new point-side vertex per S-point and a new line-side vertex per S-line."""
    m, edges, point_lines, line_points, index = _pg(q)
    cands = []
    if s >= 1:
        cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
    if s >= 2:
        F = lib.GF(q)
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        cands.append(cs)
    S = max(cands, key=len, default=[])
    if not _loads_ok(S, s, m, point_lines, line_points):
        return None
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, y))
    return 2 * m + 2 * k, E


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _candidates(d, D, rng, deadline):
    """Valid starting graphs (K_{d,d} always, plus construction candidates)."""
    out = [lib.haar_graph(d, range(d))]
    if D >= 3:
        for q in range(2, min(d - 1, 23) + 1):
            if time.monotonic() > deadline:
                break
            if not lib.is_prime_power(q):
                continue
            cand = _arc_candidate(q, d - q - 1, rng, deadline)
            if cand is not None:
                out.append(cand)
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            out.append(gq)
    return [(n, e) for n, e in out if lib.is_valid(n, e, d, D)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed * 7919 + d)
    cands = _candidates(d, D, rng, t0 + 0.1 * time_limit)
    n_best, e_best = max(cands, key=lambda t: t[0])

    # Calibration cases already at the Moore bound need no search.
    if n_best >= lib.moore_bound(d, D):
        return n_best, e_best

    elapsed = time.monotonic() - t0
    budget = 0.78 * time_limit - elapsed - 1.0
    if budget < 1.0:
        return n_best, e_best

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n_best, e_best), timeout=budget + 2.0)
        n2, e2 = lib.parse_graph_text(out)
        if n2 > n_best and lib.is_valid(n2, e2, d, D):
            return n2, e2
    except Exception:
        pass
    return n_best, e_best
