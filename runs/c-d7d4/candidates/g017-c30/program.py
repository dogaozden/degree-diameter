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

#define MAXN 4096
#define MAXW 64
#define MAXDEG 64
#define ANN_ITERS 3000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int col[MAXN];
} Snap;

static int g_d = 0, g_D = 0;
static int nv = 0;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int cand[MAXN];
static char used[MAXN];
static Snap cur_s, best_s;
static clock_t g_deadline;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdouble(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}
static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void add_arc(int a, int b) { adj[a][deg[a]++] = b; }
static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }
static void del_edge(int a, int b) { del_arc(a, b); del_arc(b, a); }

/* ball[v] = bitmask of vertices within distance steps of v */
static void balls(int steps, uint64_t out[][MAXW]) {
    int W = (nv + 63) >> 6;
    for (int v = 0; v < nv; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < steps; s++) {
        for (int v = 0; v < nv; v++) {
            for (int w = 0; w < W; w++) RB[v][w] = out[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = out[adj[v][k]];
                for (int w = 0; w < W; w++) RB[v][w] |= src[w];
            }
        }
        for (int v = 0; v < nv; v++)
            for (int w = 0; w < W; w++) out[v][w] = RB[v][w];
    }
}

/* number of unordered pairs at distance > g_D (unreachable counts) */
static long cost_bad(void) {
    balls(g_D, RA);
    int W = (nv + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < nv; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(RA[v][w]);
        bad += nv - c;
    }
    return bad / 2;
}

static int pick_def(int side) {
    for (int t = 0; t < 32; t++) {
        int v = rint_(nv);
        if (col[v] == side && deg[v] < g_d) return v;
    }
    return -1;
}

/* Simulated annealing over bipartite double-edge switches and edge additions.
   Returns 1 if the graph reaches cost 0 (valid). Works on the current state. */
static int anneal(int iters, double T0, double T1) {
    long cur = cost_bad();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && clock() >= g_deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (rdouble() < 0.2) {
            int a = pick_def(0), b = pick_def(1);
            if (a < 0 || b < 0 || has_edge(a, b)) continue;
            add_edge(a, b);
            cur = cost_bad();
            continue;
        }
        int a = rint_(nv);
        if (col[a] != 0 || deg[a] == 0) continue;
        int b = adj[a][rint_(deg[a])];
        int c = rint_(nv);
        if (c == a || col[c] != 0 || deg[c] == 0) continue;
        int e = adj[c][rint_(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost_bad();
        if (nw <= cur || rdouble() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static int count_cands(int side) {
    int nc = 0;
    for (int v = 0; v < nv; v++)
        if (col[v] == side && deg[v] < g_d) cand[nc++] = v;
    return nc;
}

/* NEW: insert a vertex whose neighbours greedily cover all vertices within
   distance D-1 (so the new vertex is within D of everything when fully covered).
   Partial covers are allowed; annealing repairs the rest. */
static int insert_vertex(void) {
    if (nv >= MAXN - 1) return 0;
    int c = rint_(2);
    int nc = count_cands(1 - c);
    if (nc == 0) {
        c = 1 - c;
        nc = count_cands(1 - c);
    }
    if (nc == 0) return 0;
    int W = (nv + 63) >> 6;
    balls(g_D - 1, RA);
    uint64_t U[MAXW];
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (nv & 63) U[W - 1] = (1ULL << (nv & 63)) - 1ULL;
    for (int i = 0; i < nc; i++) used[i] = 0;
    int chosen[MAXDEG];
    int nch = 0;
    while (nch < g_d) {
        int best = -1, bestg = 0, ties = 0;
        for (int i = 0; i < nc; i++) {
            if (used[i]) continue;
            int s = cand[i], g = 0;
            for (int w = 0; w < W; w++) g += pc64(RA[s][w] & U[w]);
            if (g > bestg) {
                bestg = g;
                best = i;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rint_(ties) == 0) best = i;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        int s = cand[best];
        chosen[nch++] = s;
        for (int w = 0; w < W; w++) U[w] &= ~RA[s][w];
    }
    if (nch == 0) return 0;
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    for (int k = 0; k < nch; k++) add_edge(v, chosen[k]);
    return 1;
}

static void remove_vertex(int v) {
    while (deg[v] > 0) del_edge(v, adj[v][0]);
    int L = nv - 1;
    if (v != L) {
        for (int k = 0; k < deg[L]; k++) {
            int u = adj[L][k];
            for (int j = 0; j < deg[u]; j++) {
                if (adj[u][j] == L) {
                    adj[u][j] = v;
                    break;
                }
            }
        }
        deg[v] = deg[L];
        col[v] = col[L];
        memcpy(adj[v], adj[L], sizeof(int) * (size_t)deg[L]);
    }
    deg[L] = 0;
    nv--;
}

static void save_snap(Snap *s) {
    s->n = nv;
    for (int v = 0; v < nv; v++) {
        s->deg[v] = deg[v];
        s->col[v] = col[v];
        memcpy(s->adj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static void load_snap(const Snap *s) {
    nv = s->n;
    for (int v = 0; v < nv; v++) {
        deg[v] = s->deg[v];
        col[v] = s->col[v];
        memcpy(adj[v], s->adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

/* K_{d,d} (valid for D >= 2) or K_2 (for D = 1). */
static void make_fallback(void) {
    int k = (g_D < 2) ? 1 : g_d;
    nv = 2 * k;
    for (int v = 0; v < nv; v++) {
        deg[v] = 0;
        col[v] = (v < k) ? 0 : 1;
    }
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) add_edge(i, k + j);
}

static int load_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    nv = n;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) return 0;
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) return 0;
        if (has_edge(a, b)) continue;
        if (deg[a] >= g_d || deg[b] >= g_d) return 0;
        add_edge(a, b);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    static int stack[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    stack[sp++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_graph(void) {
    long m = 0;
    for (int v = 0; v < nv; v++) m += deg[v];
    m /= 2;
    printf("%d %ld\n", nv, m);
    for (int v = 0; v < nv; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < adj[v][k]) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    g_d = atoi(argv[1]);
    g_D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double limit = atof(argv[4]);
    g_deadline = clock() + (clock_t)(limit * (double)CLOCKS_PER_SEC);
    if (g_d < 1 || g_d > MAXDEG || g_D < 1) {
        printf("0 0\n");
        return 0;
    }

    int ok = load_start();
    if (ok) {
        if (g_D >= 2 && cost_bad() != 0) anneal(300000, 1.0, 0.05);
        if (cost_bad() != 0) ok = 0;
    }
    if (!ok) make_fallback();

    if (g_D >= 2 && g_d >= 2) {
        save_snap(&best_s);
        save_snap(&cur_s);
        const double T0s[3] = {0.4, 0.8, 1.5};
        while (clock() < g_deadline) {
            load_snap(&cur_s);
            int okmove;
            if (rint_(10) < 6) {
                okmove = insert_vertex();
            } else {
                int r = 1 + rint_(3);
                for (int i = 0; i < r && nv > 2; i++) remove_vertex(rint_(nv));
                int ins = r + rint_(2);
                okmove = 1;
                for (int i = 0; i < ins; i++)
                    if (!insert_vertex()) break;
            }
            if (!okmove) continue;
            if (anneal(ANN_ITERS, T0s[rint_(3)], 0.05)) {
                if (nv >= best_s.n - 2) save_snap(&cur_s);
                if (nv > best_s.n) save_snap(&best_s);
            }
        }
        load_snap(&best_s);
    }
    print_graph();
    return 0;
}
"""


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


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d (q = smallest prime power >= d)."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
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


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Thinning a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured small base (W(q) or PG(2,q)) grown, twin trials
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  C engine: insert vertices with greedy cover, anneal bipartite switches,
#      remove/reinsert kicks, keep the largest valid graph
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T_end = t0 + max(0.5, 0.85 * time_limit - 1.0)
    span = T_end - t0

    def at(f):
        return t0 + f * span

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured small base, grown, then randomized twin trials.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.22):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.22):
                r = _deletion_trial(d, D, rn, re, rng, at(0.22))
                if r is None:
                    break
                consider(*r)

    # Phase C: C engine searches from the best valid graph found so far.
    if D >= 2 and d >= 2:
        left = T_end - time.monotonic() - 0.3
        if left > 0.2:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{left:.2f}"],
                                 stdin_graph=(best_n, best_e), timeout=left + 5.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
