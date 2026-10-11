import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXM 60000
#define MAXDG 64
#define W 16

static int d, D, n, m;
static int col[MAXN], deg[MAXN];
static int eu[MAXM], ev[MAXM];
static unsigned char A[MAXN][MAXN];
static int ad[MAXN][MAXDG], dg[MAXN];
static uint64_t B[2][MAXN][W];
static uint64_t rs = 88172645463325252ULL;
static double tend;
static int tu[MAXM], tv[MAXM];

typedef struct {
    int n, m;
    int col[MAXN], deg[MAXN];
    int eu[MAXM], ev[MAXM];
} Snap;
static Snap cur_s, best_s;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return (double)clock() / CLOCKS_PER_SEC >= tend; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Fills B with balls of radius r; returns the buffer index holding them. */
static int compute_ball(int r) {
    int w = (n + 63) >> 6;
    int cur = 0;
    for (int i = 0; i < n; i++) dg[i] = 0;
    for (int i = 0; i < m; i++) {
        ad[eu[i]][dg[eu[i]]++] = ev[i];
        ad[ev[i]][dg[ev[i]]++] = eu[i];
    }
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) B[0][v][k] = 0;
        B[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < w; k++) {
                uint64_t x = B[cur][v][k];
                for (int j = 0; j < dg[v]; j++) x |= B[cur][ad[v][j]][k];
                B[nx][v][k] = x;
            }
        }
        cur = nx;
    }
    return cur;
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static int cost(void) {
    int w = (n + 63) >> 6;
    int b = compute_ball(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int k = 0; k < w; k++) pc += popc(B[b][v][k]);
        bad += n - pc;
    }
    return (int)(bad / 2);
}

static void add_edge(int x, int y) {
    if (col[x] == 1) { int t = x; x = y; y = t; }
    eu[m] = x; ev[m] = y; m++;
    A[x][y] = A[y][x] = 1;
    deg[x]++; deg[y]++;
}

static void del_edge(int i) {
    int x = eu[i], y = ev[i];
    A[x][y] = A[y][x] = 0;
    deg[x]--; deg[y]--;
    m--;
    eu[i] = eu[m]; ev[i] = ev[m];
}

/* Add a vertex on the opposite side of `side`, joined to a greedy cover of `side`. */
static void add_vertex(int side) {
    static int used[MAXN];
    int chosen[MAXDG];
    int nc = 0;
    int b = compute_ball(D - 1);
    int w = (n + 63) >> 6;
    uint64_t cov[W];
    for (int k = 0; k < w; k++) cov[k] = 0;
    for (int i = 0; i < n; i++) used[i] = 0;
    for (int t = 0; t < d; t++) {
        int best = -1;
        double bg = -1.0;
        for (int s = 0; s < n; s++) {
            if (col[s] != side || used[s]) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += popc(B[b][s][k] & ~cov[k]);
            double sc = g + 0.5 * rndd();
            if (sc > bg) { bg = sc; best = s; }
        }
        if (best < 0 || (int)bg < 1) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int k = 0; k < w; k++) cov[k] |= B[b][best][k];
    }
    int v = n;
    n++;
    col[v] = 1 - side;
    deg[v] = 0;
    for (int k = 0; k < n; k++) { A[v][k] = 0; A[k][v] = 0; }
    for (int q = 0; q < nc; q++) {
        int s = chosen[q];
        if (deg[s] >= d && m > 0) {
            int st = rndi(m), idx = -1;
            for (int t = 0; t < m; t++) {
                int i = (st + t) % m;
                if (eu[i] == s || ev[i] == s) { idx = i; break; }
            }
            if (idx >= 0) del_edge(idx);
        }
        if (deg[s] < d) add_edge(s, v);
    }
}

/* Join random deficient opposite-side pairs (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    if (!nl || !nr) return;
    int tries = 4 * (nl + nr) + 10;
    for (int t = 0; t < tries; t++) {
        int a = L[rndi(nl)], b = R[rndi(nr)];
        if (deg[a] < d && deg[b] < d && !A[a][b]) add_edge(a, b);
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. Returns 1 if cost 0. */
static int anneal(long iters) {
    int c = cost();
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 15) == 0 && timeup()) break;
        if (m < 2) break;
        int i = rndi(m), j = rndi(m);
        if (i == j) continue;
        int a = eu[i], b = ev[i], x = eu[j], e = ev[j];
        if (a == x || b == e) continue;
        if (A[a][e] || A[x][b]) continue;
        A[a][b] = A[b][a] = 0;
        A[x][e] = A[e][x] = 0;
        A[a][e] = A[e][a] = 1;
        A[x][b] = A[b][x] = 1;
        eu[i] = a; ev[i] = e;
        eu[j] = x; ev[j] = b;
        int nc = cost();
        int delta = nc - c;
        if (delta <= 0 || (delta == 1 && rndd() < 0.1) || (delta == 2 && rndd() < 0.01)) {
            c = nc;
        } else {
            A[a][e] = A[e][a] = 0;
            A[x][b] = A[b][x] = 0;
            A[a][b] = A[b][a] = 1;
            A[x][e] = A[e][x] = 1;
            eu[i] = a; ev[i] = b;
            eu[j] = x; ev[j] = e;
        }
    }
    return c == 0;
}

static void save(Snap *s) {
    s->n = n; s->m = m;
    memcpy(s->col, col, sizeof(int) * n);
    memcpy(s->deg, deg, sizeof(int) * n);
    memcpy(s->eu, eu, sizeof(int) * m);
    memcpy(s->ev, ev, sizeof(int) * m);
}

static void load(const Snap *s) {
    for (int i = 0; i < m; i++) { A[eu[i]][ev[i]] = 0; A[ev[i]][eu[i]] = 0; }
    n = s->n; m = s->m;
    memcpy(col, s->col, sizeof(int) * n);
    memcpy(deg, s->deg, sizeof(int) * n);
    memcpy(eu, s->eu, sizeof(int) * m);
    memcpy(ev, s->ev, sizeof(int) * m);
    for (int i = 0; i < m; i++) { A[eu[i]][ev[i]] = 1; A[ev[i]][eu[i]] = 1; }
}

/* Remove vertex x, moving the last vertex into its label. */
static void kill_vertex(int x) {
    for (int i = m - 1; i >= 0; i--) {
        if (eu[i] == x || ev[i] == x) del_edge(i);
    }
    int last = n - 1;
    if (x != last) {
        for (int i = 0; i < m; i++) {
            if (eu[i] == last) eu[i] = x;
            if (ev[i] == last) ev[i] = x;
        }
        for (int j = 0; j < n; j++) {
            A[x][j] = A[last][j];
            A[j][x] = A[j][last];
        }
        col[x] = col[last];
        deg[x] = deg[last];
    }
    for (int j = 0; j < n; j++) { A[last][j] = 0; A[j][last] = 0; }
    n--;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atol(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tend = (double)clock() / CLOCKS_PER_SEC + atof(argv[4]);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 < 1 || n0 >= MAXN - 2 || m0 < 0 || m0 > MAXM || d < 1 || d > MAXDG - 4 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &tu[i], &tv[i]) != 2) { printf("0 0\n"); return 0; }
        if (tu[i] < 0 || tu[i] >= n0 || tv[i] < 0 || tv[i] >= n0) { printf("0 0\n"); return 0; }
    }

    /* Bipartition the input. */
    for (int i = 0; i < n0; i++) { dg[i] = 0; col[i] = -1; }
    for (int i = 0; i < m0; i++) {
        if (dg[tu[i]] >= MAXDG || dg[tv[i]] >= MAXDG) { printf("0 0\n"); return 0; }
        ad[tu[i]][dg[tu[i]]++] = tv[i];
        ad[tv[i]][dg[tv[i]]++] = tu[i];
    }
    static int stk[MAXN];
    int ok = 1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int j = 0; j < dg[u]; j++) {
                int v = ad[u][j];
                if (col[v] < 0) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) ok = 0;
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    /* Build state. */
    n = n0; m = 0;
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int i = 0; i < m0; i++) {
        if (tu[i] == tv[i] || A[tu[i]][tv[i]]) continue;
        add_edge(tu[i], tv[i]);
    }
    if (!anneal(20000)) { printf("0 0\n"); return 0; }

    save(&best_s);
    save(&cur_s);

    while (!timeup()) {
        int r = rndi(10);
        if (r < 7 && n < MAXN - 2) {
            add_vertex(rndi(2));
            fill();
            if (anneal(2000)) {
                save(&cur_s);
                if (n > best_s.n) save(&best_s);
            } else {
                load(&cur_s);
            }
        } else {
            int k = 1 + rndi(2);
            for (int t = 0; t < k && n > 3; t++) kill_vertex(rndi(n));
            fill();
            int good = anneal(2000);
            if (good && n >= best_s.n - 3) {
                save(&cur_s);
            } else if (good) {
                load(&best_s);
                save(&cur_s);
            } else {
                load(&cur_s);
            }
        }
    }

    printf("%d %d\n", best_s.n, best_s.m);
    for (int i = 0; i < best_s.m; i++) printf("%d %d\n", best_s.eu[i], best_s.ev[i]);
    return 0;
}
"""


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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication: a non-adjacent twin v' of v (same neighbourhood) keeps the
# diameter bound for D >= 2 and the bipartition, and needs only spare degree.
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end_all = start + 0.9 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.3 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C annealing engine: kill / add-and-repair moves with bitset distance cost.
    if D >= 2 and d <= 60:
        budget = end_all - time.monotonic() - 1.0
        if budget > 0.5:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
