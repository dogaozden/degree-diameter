import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving bipartite annealing, cover-based vertex insertion,
# and kill-repair moves, all on a valid graph. Every improvement is accepted only
# at zero bad pairs, so the output is valid whenever it is nonempty.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define WMAX 32
#define ITERS 800

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static int N, DD, DIAM, WN;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t bufA[MAXN][WMAX], bufB[MAXN][WMAX], bufT[MAXN][WMAX];
static uint64_t rs = 88172645463325252ULL;
static double tlimit = 1.0;
static clock_t t0;
static State cur_s, best_s;
static int dA[MAXN], dB[MAXN];
static int used[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }
static int pc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int find_idx(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return i;
    return -1;
}
static int has_edge(int a, int b) { return find_idx(a, b) >= 0; }
static void del_half(int a, int b) {
    int i = find_idx(a, b);
    if (i >= 0) adj[a][i] = adj[a][--deg[a]];
}
static void del_edge(int a, int b) { del_half(a, b); del_half(b, a); }
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void compute_balls(int r, uint64_t out[MAXN][WMAX]) {
    WN = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < WN; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < WN; w++) bufT[v][w] = out[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = out[adj[v][i]];
                for (int w = 0; w < WN; w++) bufT[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < WN; w++) out[v][w] = bufT[v][w];
    }
}

static long cost(void) {
    compute_balls(DIAM, bufA);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < WN; w++) c += pc(bufA[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void fill(void) {
    int na = 0, nb = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= DD) continue;
        if (col[v] == 0) dA[na++] = v; else dB[nb++] = v;
    }
    if (na == 0 || nb == 0) return;
    long tries = 30L * (na + nb);
    for (long t = 0; t < tries; t++) {
        int a = dA[rndi(na)], b = dB[rndi(nb)];
        if (deg[a] < DD && deg[b] < DD && !has_edge(a, b)) add_edge(a, b);
    }
}

static void add_vertex_cover(int side) {
    if (N >= MAXN - 1) return;
    compute_balls(DIAM - 1, bufB);
    uint64_t cov[WMAX];
    for (int w = 0; w < WN; w++) cov[w] = 0;
    for (int v = 0; v < N; v++) used[v] = 0;
    int chosen[MAXD], nc = 0;
    for (int k = 0; k < DD; k++) {
        int best = -1, bestg = 0;
        for (int c = 0; c < N; c++) {
            if (col[c] != side || used[c]) continue;
            int g = 0;
            for (int w = 0; w < WN; w++) g += pc(bufB[c][w] & ~cov[w]);
            if (g > bestg || (g == bestg && g > 0 && rndi(2) == 0)) { bestg = g; best = c; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < WN; w++) cov[w] |= bufB[best][w];
    }
    if (nc == 0) return;
    int v = N++;
    col[v] = 1 - side;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (deg[c] >= DD) {
            int t = adj[c][rndi(deg[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
}

static void kill_vertex(int x) {
    while (deg[x] > 0) del_edge(x, adj[x][deg[x] - 1]);
    int last = N - 1;
    if (x != last) {
        deg[x] = deg[last];
        for (int i = 0; i < deg[x]; i++) adj[x][i] = adj[last][i];
        col[x] = col[last];
        for (int i = 0; i < deg[x]; i++) {
            int t = adj[x][i];
            for (int j = 0; j < deg[t]; j++) if (adj[t][j] == last) adj[t][j] = x;
        }
    }
    N--;
}

static void save_state(State *s) {
    s->n = N;
    for (int v = 0; v < N; v++) {
        s->deg[v] = deg[v];
        s->col[v] = col[v];
        for (int i = 0; i < deg[v]; i++) s->adj[v][i] = adj[v][i];
    }
}

static void load_state(const State *s) {
    N = s->n;
    for (int v = 0; v < N; v++) {
        deg[v] = s->deg[v];
        col[v] = s->col[v];
        for (int i = 0; i < deg[v]; i++) adj[v][i] = s->adj[v][i];
    }
}

static long anneal(int iters) {
    long cur = cost();
    static int s0[MAXN];
    int ns0 = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0 && deg[v] > 0) s0[ns0++] = v;
    if (ns0 < 2) return cur;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && elapsed() > tlimit) break;
        int a = s0[rndi(ns0)], c = s0[rndi(ns0)];
        if (a == c || deg[a] == 0 || deg[c] == 0) continue;
        int b = adj[a][rndi(deg[a])];
        int e = adj[c][rndi(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long nc = cost();
        if (nc <= cur || (nc == cur + 1 && rndi(100) < 3)) {
            cur = nc;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur;
}

static void output_state(const State *s) {
    long m = 0;
    for (int v = 0; v < s->n; v++) m += s->deg[v];
    m /= 2;
    printf("%d %ld\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (v < s->adj[v][i]) printf("%d %d\n", v, s->adj[v][i]);
}

static void set_complete_bip(int d) {
    N = 2 * d;
    for (int v = 0; v < N; v++) { deg[v] = 0; col[v] = v < d ? 0 : 1; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            add_edge(a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    tlimit = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    DD = d;
    if (d < 1 || d > MAXD || DIAM < 2) { printf("0 0\n"); return 0; }
    t0 = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int ok = 1;
    if (n >= 1 && n <= MAXN) {
        N = n;
        for (int v = 0; v < N; v++) deg[v] = 0;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
                deg[u] >= DD || deg[v] >= DD || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
    } else {
        ok = 0;
    }
    if (!ok) {
        set_complete_bip(d);
    } else {
        static int queue[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt) {
                int u = queue[qh++];
                for (int i = 0; i < deg[u]; i++) {
                    int w = adj[u][i];
                    if (col[w] < 0) { col[w] = 1 - col[u]; queue[qt++] = w; }
                }
            }
        }
    }

    if (cost() != 0) {
        anneal(20000);
        if (cost() != 0) set_complete_bip(d);
    }
    save_state(&best_s);

    while (elapsed() < tlimit) {
        if (N < best_s.n - 2) load_state(&best_s);
        save_state(&cur_s);
        if (rndi(100) < 75 || N < 4) add_vertex_cover(rndi(2));
        else kill_vertex(rndi(N));
        fill();
        long c = anneal(ITERS);
        if (c == 0) {
            if (N > best_s.n) save_state(&best_s);
        } else {
            load_state(&cur_s);
        }
    }
    output_state(&best_s);
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d and q <= 16."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
# Driver: structured base and twin trials in Python, then the C annealing engine
# starts from the best valid graph. Every candidate passes lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.80 * time_limit
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

    if D >= 2:
        base = None
        if D >= 4:
            base = _best_gq(d)
        if base is None and D >= 3:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

        trial_end = start + 0.20 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(best_n, best_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2:
        budget = end - time.monotonic()
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
