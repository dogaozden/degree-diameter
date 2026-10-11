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
#define MAXW ((MAXN + 63) / 64)
#define MAXD 24

static int D, DEG, n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t BA[MAXN][MAXW], BB[MAXN][MAXW], BALL[MAXN][MAXW];
static int sN, sdeg[MAXN], sadj[MAXN][MAXD], scol[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    for (int i = 0; i < deg[v]; i++) if (adj[v][i] == old) { adj[v][i] = nw; return; }
}

static void add_edge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }

static void del_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (int i = 0; i < deg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}

/* out[v] = bitset of vertices within distance r of v. */
static void balls(int r, uint64_t out[][MAXW]) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(out[v], 0, sizeof(uint64_t) * W);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            memcpy(BB[v], out[v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) BB[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < n; v++) memcpy(out[v], BB[v], sizeof(uint64_t) * W);
    }
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long cost(void) {
    int W = (n + 63) >> 6;
    balls(D, BA);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(BA[v][w]);
        bad += n - pc;
    }
    return bad / 2;
}

/* Random bipartite double-edge switch a-b, c-e -> a-e, c-b (a,c colour 0; b,e colour 1). */
static int pick_switch(int *pa, int *pb, int *pc, int *pe) {
    for (int t = 0; t < 200; t++) {
        int a = rndint(n);
        if (col[a] != 0 || deg[a] == 0) continue;
        int c = rndint(n);
        if (col[c] != 0 || deg[c] == 0 || c == a) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        *pa = a; *pb = b; *pc = c; *pe = e;
        return 1;
    }
    return 0;
}

static void apply_switch(int a, int b, int c, int e) {
    replace_nb(a, b, e);
    replace_nb(b, a, c);
    replace_nb(c, e, b);
    replace_nb(e, c, a);
}

static void undo_switch(int a, int b, int c, int e) {
    replace_nb(a, e, b);
    replace_nb(e, a, c);
    replace_nb(c, b, e);
    replace_nb(b, c, a);
}

static long anneal(int iters, long cur, double T0, double T1) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now() > t_end) break;
        int a, b, c, e;
        if (!pick_switch(&a, &b, &c, &e)) break;
        apply_switch(a, b, c, e);
        long nw = cost();
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nw;
        else undo_switch(a, b, c, e);
    }
    return cur;
}

/* Join deficient opposite-side pairs (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < DEG) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) { int j = rndint(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t; }
    for (int i = nr - 1; i > 0; i--) { int j = rndint(i + 1); int t = R[i]; R[i] = R[j]; R[j] = t; }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < DEG; j++) {
            int b = R[j];
            if (deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add a vertex on one side, joined greedily to a cover of the other side's (D-1)-balls. */
static void add_vertex(void) {
    if (n >= MAXN - 2) return;
    int s = rndint(2);
    balls(D - 1, BALL);
    int W = (n + 63) >> 6;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD];
    int nch = 0;
    for (int k = 0; k < DEG; k++) {
        int best = -1, bg = 0;
        for (int c = 0; c < n; c++) {
            if (col[c] != 1 - s) continue;
            int used = 0;
            for (int i = 0; i < nch; i++) if (chosen[i] == c) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(BALL[c][w] & ~cov[w]);
            if (g > bg || (g == bg && g > 0 && rndint(2))) { bg = g; best = c; }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= BALL[best][w];
    }
    int v = n;
    col[v] = 1 - (1 - s);
    col[v] = s;
    deg[v] = 0;
    n++;
    for (int i = 0; i < nch; i++) {
        int t = chosen[i];
        if (deg[t] >= DEG) {
            int x = adj[t][rndint(deg[t])];
            del_edge(t, x);
        }
        add_edge(t, v);
    }
}

static void save_state(void) {
    sN = n;
    memcpy(sdeg, deg, sizeof(int) * n);
    memcpy(sadj, adj, sizeof(int) * MAXD * n);
    memcpy(scol, col, sizeof(int) * n);
}

static void restore_state(void) {
    n = sN;
    memcpy(deg, sdeg, sizeof(int) * n);
    memcpy(adj, sadj, sizeof(int) * MAXD * n);
    memcpy(col, scol, sizeof(int) * n);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    DEG = d;

    int N, M;
    if (scanf("%d %d", &N, &M) != 2 || N < 1 || N >= MAXN - 2 || d < 1 || d >= MAXD - 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    n = N;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < M; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    static int q[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int i = 0; i < deg[x]; i++) {
                int y = adj[x][i];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; }
                else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
            }
        }
    }

    t_end = now() + budget;
    long cur = cost();
    if (cur > 0) cur = anneal(20000, cur, 1.0, 0.05);

    int fails = 0;
    while (cur == 0 && now() < t_end) {
        save_state();
        if (fails % 8 == 7) {
            int k = 0, tries = 0;
            while (k < 30 && tries < 5000) {
                tries++;
                int a, b, c, e;
                if (pick_switch(&a, &b, &c, &e)) { apply_switch(a, b, c, e); k++; }
            }
            cur = cost();
            cur = anneal(4000, cur, 0.8, 0.05);
        } else {
            add_vertex();
            fill();
            cur = cost();
            cur = anneal(1500, cur, 0.6, 0.05);
        }
        if (cur == 0) {
            fails = 0;
        } else {
            restore_state();
            cur = 0;
            fails++;
        }
    }

    long m2 = 0;
    for (int v = 0; v < n; v++) m2 += deg[v];
    printf("%d %ld\n", n, m2 / 2);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python constructions).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for growing and duplicating graphs.
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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


# ----------------------------------------------------------------------------
# C stage: add-one-vertex, repair by bipartite switches, perturb on stall.
# ----------------------------------------------------------------------------

def _c_search(d, D, n, edges, seconds, seed):
    """Run the C engine from (n, edges) for about `seconds` CPU seconds. Returns (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}"],
                    stdin_graph=(n, edges), timeout=seconds + 8.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    try:
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
                n1, e1 = _grow(n0, e0, d, D, start + 0.08 * time_limit, rng)
                consider(n1, e1)

        # Short randomized twin-duplication pipelines from the structured base.
        if D >= 2:
            trial_end = start + 0.2 * time_limit
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)

        # Main stage: C engine adds vertices and repairs them with switch annealing.
        moore = lib.moore_bound(d, D)
        end = start + 0.86 * time_limit
        seconds = end - time.monotonic() - 4.0
        if D >= 2 and d <= 20 and best_n < moore and moore < 2000 and seconds > 3:
            n2, e2 = _c_search(d, D, best_n, best_e, seconds, seed % 1000003 + 1)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
