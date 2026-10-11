import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: annealed double-edge switches on a bipartite graph, with
# kill-repair-regrow (random and BFS-local kills). Degree is preserved by the
# switches, so the bipartition and the degree bound stay fixed. The output is
# always a valid graph (diameter cost 0) or the input graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define W 16
#define MAXE (MAXN * MAXD / 2)

typedef uint64_t Row[W];

typedef struct {
    int n, m;
    int eu[MAXE], ev[MAXE];
    int col[MAXN];
} Snap;

static int N = 0, DEG = 3, DD = 3;
static unsigned char A[MAXN][MAXN];
static int deg[MAXN];
static int nbr[MAXN][MAXD];
static int col[MAXN];
static Row BA[MAXN], BB[MAXN], COV[MAXN];
static Snap BEST, TMP, INPUT;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void rm_nbr(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (nbr[u][k] == v) {
            nbr[u][k] = nbr[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}
static void add_edge(int u, int v) {
    A[u][v] = 1; A[v][u] = 1;
    nbr[u][deg[u]++] = v;
    nbr[v][deg[v]++] = u;
}
static void del_edge(int u, int v) {
    A[u][v] = 0; A[v][u] = 0;
    rm_nbr(u, v); rm_nbr(v, u);
}

static void load(const Snap *s) {
    for (int i = 0; i < N; i++) {
        memset(A[i], 0, (size_t)N);
        deg[i] = 0;
    }
    N = s->n;
    for (int i = 0; i < N; i++) {
        col[i] = s->col[i];
        deg[i] = 0;
    }
    for (int j = 0; j < s->m; j++) add_edge(s->eu[j], s->ev[j]);
}

static void save(Snap *s) {
    s->n = N;
    s->m = 0;
    for (int u = 0; u < N; u++) {
        for (int k = 0; k < deg[u]; k++) {
            int v = nbr[u][k];
            if (u < v) {
                s->eu[s->m] = u;
                s->ev[s->m] = v;
                s->m++;
            }
        }
    }
    for (int i = 0; i < N; i++) s->col[i] = col[i];
}

static Row *balls(int r) {
    Row *X = BA, *Y = BB;
    int nw = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        memset(X[v], 0, sizeof(Row));
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            memcpy(Y[v], X[v], (size_t)nw * 8);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = X[nbr[v][k]];
                for (int w = 0; w < nw; w++) Y[v][w] |= src[w];
            }
        }
        Row *t = X; X = Y; Y = t;
    }
    return X;
}

static long long cost(void) {
    Row *B = balls(DD);
    int nw = (N + 63) >> 6;
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += __builtin_popcountll(B[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Add one vertex on side c, joined greedily to a cover of the old vertices. */
static int grow(int c) {
    if (N + 1 >= MAXN) return 0;
    Row *B = balls(DD - 1);
    int nw = (N + 63) >> 6;
    memcpy(COV, B, sizeof(Row) * (size_t)N);
    Row cov;
    memset(cov, 0, sizeof cov);
    unsigned char used[MAXN];
    memset(used, 0, sizeof used);
    int chosen[MAXD];
    int nch = 0;
    for (int pick = 0; pick < DEG; pick++) {
        int best = -1, bg = 0;
        int st = rndi(N);
        for (int t = 0; t < N; t++) {
            int s = (st + t) % N;
            if (col[s] == c || deg[s] >= DEG || used[s]) continue;
            int g = 0;
            for (int q = 0; q < nw; q++) g += __builtin_popcountll(COV[s][q] & ~cov[q]);
            if (g > bg) { bg = g; best = s; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int q = 0; q < nw; q++) cov[q] |= COV[best][q];
    }
    if (nch == 0) return 0;
    int nv = N;
    N++;
    col[nv] = c;
    deg[nv] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], nv);
    return nch;
}

/* Join random deficient opposite-side pairs. */
static void fill(void) {
    for (int t = 0; t < 20 * N; t++) {
        int a = rndi(N), b = rndi(N);
        if (col[a] == col[b]) continue;
        if (col[a] == 1) { int tmp = a; a = b; b = tmp; }
        if (deg[a] >= DEG || deg[b] >= DEG || A[a][b]) continue;
        add_edge(a, b);
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static long long anneal(int iters, double temp, double deadline) {
    long long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now_s() > deadline) break;
        int a = rndi(N);
        if (col[a] != 0 || deg[a] == 0) continue;
        int b = nbr[a][rndi(deg[a])];
        int c = rndi(N);
        if (c == a || col[c] != 0 || deg[c] == 0) continue;
        int e = nbr[c][rndi(deg[c])];
        if (A[a][e] || A[c][b]) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long long nc = cost();
        int acc = nc <= cur;
        if (!acc) acc = rnd01() < exp(-(double)(nc - cur) / temp);
        if (acc) {
            cur = nc;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur;
}

/* Remove k vertices (random or BFS-local) from src into dst. */
static void make_kill(const Snap *src, int k, int local, Snap *dst) {
    load(src);
    int dead[MAXN];
    memset(dead, 0, sizeof dead);
    if (!local) {
        for (int i = 0; i < k; i++) dead[rndi(N)] = 1;
    } else {
        int q[MAXN];
        int qh = 0, qt = 0, cnt = 0;
        int s = rndi(N);
        dead[s] = 1; cnt = 1; q[qt++] = s;
        while (qh < qt && cnt < k) {
            int v = q[qh++];
            for (int j = 0; j < deg[v] && cnt < k; j++) {
                int u = nbr[v][j];
                if (!dead[u]) {
                    dead[u] = 1; cnt++;
                    q[qt++] = u;
                }
            }
        }
    }
    int newid[MAXN];
    int nn = 0;
    for (int v = 0; v < N; v++) newid[v] = dead[v] ? -1 : nn++;
    dst->n = nn;
    for (int v = 0; v < N; v++)
        if (newid[v] >= 0) dst->col[newid[v]] = col[v];
    dst->m = 0;
    for (int j = 0; j < src->m; j++) {
        int a = newid[src->eu[j]], b = newid[src->ev[j]];
        if (a >= 0 && b >= 0) {
            dst->eu[dst->m] = a;
            dst->ev[dst->m] = b;
            dst->m++;
        }
    }
}

static void print_snap(const Snap *s) {
    printf("%d %d\n", s->n, s->m);
    for (int j = 0; j < s->m; j++) printf("%d %d\n", s->eu[j], s->ev[j]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double deadline = now_s() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n <= 0 || n >= MAXN - 2 || m < 0 || m > MAXE || d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    static int dc[MAXN];
    N = n;
    int bad = 0;
    for (int j = 0; j < m && !bad; j++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { bad = 1; break; }
        if (a < 0 || b < 0 || a >= n || b >= n || a == b || A[a][b]) { bad = 1; break; }
        A[a][b] = 1; A[b][a] = 1;
        dc[a]++; dc[b]++;
        INPUT.eu[j] = a;
        INPUT.ev[j] = b;
    }
    for (int i = 0; i < n && !bad; i++)
        if (dc[i] > d) bad = 1;
    for (int i = 0; i < n; i++) memset(A[i], 0, (size_t)n);
    N = 0;
    if (bad) { printf("0 0\n"); return 0; }
    INPUT.n = n;
    INPUT.m = m;
    for (int i = 0; i < n; i++) INPUT.col[i] = 0;
    DEG = d;
    DD = D;
    load(&INPUT);

    /* Bipartition by BFS. */
    static int q[MAXN];
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n && !bad; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && !bad) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nbr[u][k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[qt++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                    break;
                }
            }
        }
    }
    if (bad) { printf("0 0\n"); return 0; }

    if (cost() == 0) {
        save(&BEST);
    } else {
        if (anneal(400000, 0.4, deadline) == 0) save(&BEST);
    }
    if (BEST.n == 0) { printf("0 0\n"); return 0; }

    const int ITERS = 1500;
    while (now_s() < deadline) {
        int r = rndi(10);
        int grows = 1;
        if (r < 4) {
            load(&BEST);
        } else {
            int local = (r >= 7);
            int k = local ? 2 + rndi(5) : 1 + rndi(4);
            if (k >= BEST.n - 2) k = 1;
            make_kill(&BEST, k, local, &TMP);
            load(&TMP);
            grows = k + 1;
        }
        for (int g = 0; g < grows && N + 1 < MAXN; g++) grow(rndi(2));
        fill();
        long long c = anneal(ITERS, 0.6, deadline);
        if (c == 0 && N >= BEST.n) save(&BEST);
    }
    print_snap(&BEST);
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
    """Dense structured graph with degree at least d, to be thinned into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared helpers.
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices at distance <= D-1."""
    if D < 2:
        return n, edges
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
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
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
# Thin a dense structured graph into a valid one.
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
    """One thinning trial from the dense raw graph. Returns (n, edges) or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver. Python builds a structured start (Phases A and B). C then runs the
# annealed kill-repair-regrow search from the best valid graph for the rest of
# the budget. Every candidate passes lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base, grown, then twin trials.
    if D >= 2:
        base = None
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
            consider(n1, e1)
            base_n, base_e = n0, list(e0)
        else:
            base_n, base_e = best_n, list(best_e)
        trial_end = at(0.10)
        while time.monotonic() < trial_end and best_n < bound:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense structured graph.
    if D >= 2 and best_n < bound and time.monotonic() < at(0.25):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.25):
                r = _deletion_trial(d, D, rn, re, rng, at(0.25))
                if r is None:
                    break
                consider(*r)

    # Phase C: C annealing and LNS from the best valid graph.
    if D >= 2 and best_n < bound:
        end = start + 0.85 * time_limit - 1.0
        budget = end - time.monotonic()
        if budget >= 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
