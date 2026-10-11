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

#define NMAX 4096
#define WMAX 64
#define DMAX 32
#define STALL 1500
#define TEMP 0.7

static int N, Dg, DIAM;
static int deg[NMAX];
static int adj[NMAX][DMAX];
static int col[NMAX];
static uint64_t bufA[NMAX][WMAX];
static uint64_t bufB[NMAX][WMAX];
static uint64_t (*Ball)[WMAX];

static int sN;
static int sdeg[NMAX];
static int sadj[NMAX][DMAX];
static int scol[NMAX];
static int have_valid = 0;

static int pa, pb, pc, pe;
static char picked[NMAX];
static int fl[2][NMAX];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static uint8_t pc16[65536];
static void init_pc(void) {
    for (int i = 1; i < 65536; i++) pc16[i] = (uint8_t)(pc16[i >> 1] + (i & 1));
}
static int popc64(uint64_t x) {
    return pc16[x & 0xffff] + pc16[(x >> 16) & 0xffff] + pc16[(x >> 32) & 0xffff] + pc16[(x >> 48) & 0xffff];
}

/* Sum over unordered pairs of the number of pairs at distance > DIAM. */
static long long compute_bad(void) {
    int w = (N + 63) >> 6;
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * w);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt[v];
            memcpy(dst, cur[v], sizeof(uint64_t) * w);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[adj[v][i]];
                for (int k = 0; k < w; k++) dst[k] |= src[k];
            }
        }
        uint64_t (*tmp)[WMAX] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc64(cur[v][k]);
        tot += N - c;
    }
    Ball = cur;
    return tot / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void rep(int a, int old, int nw) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == old) { adj[a][i] = nw; return; }
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void rm_nb(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
}
static void del_edge(int a, int b) { rm_nb(a, b); rm_nb(b, a); }

/* Edges (a,b),(c,e) become (a,e),(c,b). Degrees are preserved. */
static void swap2(int a, int b, int c, int e) {
    rep(a, b, e);
    rep(b, a, c);
    rep(c, e, b);
    rep(e, c, a);
}

static int try_swap(void) {
    int a = rndint(N);
    if (deg[a] == 0) return 0;
    int b = adj[a][rndint(deg[a])];
    int c = rndint(N);
    if (c == a || col[c] != col[a] || deg[c] == 0) return 0;
    int e = adj[c][rndint(deg[c])];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
    swap2(a, b, c, e);
    pa = a; pb = b; pc = c; pe = e;
    return 1;
}

static void saturate(void) {
    int fn[2] = {0, 0};
    for (int v = 0; v < N; v++) if (deg[v] < Dg) fl[col[v]][fn[col[v]]++] = v;
    for (int s = 0; s < 2; s++)
        for (int i = fn[s] - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = fl[s][i]; fl[s][i] = fl[s][j]; fl[s][j] = t;
        }
    for (int i = 0; i < fn[0]; i++) {
        int a = fl[0][i];
        for (int j = 0; j < fn[1] && deg[a] < Dg; j++) {
            int b = fl[1][j];
            if (deg[b] < Dg && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add one vertex. Uses the balls of the current VALID graph to pick a
   covering neighbourhood, then steals edges if slots remain. Returns 0 on failure
   (state unchanged). */
static int grow_step(void) {
    compute_bad();
    int No = N;
    int w = (No + 63) >> 6;
    int c = rndint(2);
    uint64_t cov[WMAX];
    memset(cov, 0, sizeof cov);
    int v = N;
    col[v] = c;
    deg[v] = 0;
    N++;
    int nc = 0, chosen[DMAX];
    while (nc < Dg) {
        int best = -1;
        long long bk = -1;
        for (int s = 0; s < No; s++) {
            if (col[s] == c || deg[s] >= Dg || picked[s]) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += popc64(Ball[s][k] & ~cov[k]);
            long long key = (long long)g * 4096 + rndint(4096);
            if (key > bk) { bk = key; best = s; }
        }
        if (best < 0) break;
        picked[best] = 1;
        chosen[nc++] = best;
        for (int k = 0; k < w; k++) cov[k] |= Ball[best][k];
    }
    for (int i = 0; i < nc; i++) {
        picked[chosen[i]] = 0;
        add_edge(v, chosen[i]);
    }
    int tries = 0;
    while (deg[v] < Dg && tries < 200) {
        tries++;
        int y = rndint(No);
        if (col[y] == c || deg[y] != Dg || has_edge(v, y)) continue;
        int z = adj[y][rndint(deg[y])];
        del_edge(y, z);
        add_edge(v, y);
    }
    if (deg[v] == 0) {
        N--;
        return 0;
    }
    saturate();
    return 1;
}

static void snapshot(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(int) * N);
    memcpy(sadj, adj, sizeof(int) * DMAX * N);
    memcpy(scol, col, sizeof(int) * N);
    have_valid = 1;
}

static void restore(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof(int) * N);
    memcpy(adj, sadj, sizeof(int) * DMAX * N);
    memcpy(col, scol, sizeof(int) * N);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dg = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    double deadline = now() + tl;
    init_pc();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || n > NMAX / 2 || Dg < 1 || Dg > DMAX || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    int bad_input = 0;
    N = n;
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad_input = 1; break; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || deg[u] >= Dg || deg[v] >= Dg || has_edge(u, v)) {
            bad_input = 1;
            break;
        }
        add_edge(u, v);
    }
    if (bad_input) { printf("0 0\n"); return 0; }

    /* Bipartition by BFS. */
    for (int i = 0; i < n; i++) col[i] = -1;
    static int stack[NMAX];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int x = adj[u][i];
                if (col[x] < 0) { col[x] = 1 - col[u]; stack[sp++] = x; }
                else if (col[x] == col[u]) bad_input = 1;
            }
        }
    }
    if (bad_input) { printf("0 0\n"); return 0; }

    long long bad = compute_bad();
    if (bad == 0) snapshot();
    int stall = 0;
    while (now() < deadline) {
        if (bad == 0) {
            snapshot();
            stall = 0;
            if (N >= NMAX - 2) break;
            if (!grow_step()) continue;
            bad = compute_bad();
            continue;
        }
        if (try_swap()) {
            long long nb = compute_bad();
            long long delta = nb - bad;
            if (delta <= 0 || rnd01() < exp(-(double)delta / TEMP)) {
                bad = nb;
            } else {
                swap2(pa, pe, pc, pb);
            }
        }
        if (++stall > STALL) {
            stall = 0;
            if (have_valid) {
                restore();
                bad = compute_bad();
            }
        }
    }
    if (bad == 0) snapshot();
    if (!have_valid) { printf("0 0\n"); return 0; }

    int M = 0;
    for (int v = 0; v < sN; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[v][i] > v) M++;
    printf("%d %d\n", sN, M);
    for (int v = 0; v < sN; v++)
        for (int i = 0; i < sdeg[v]; i++)
            if (sadj[v][i] > v) printf("%d %d\n", v, sadj[v][i]);
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
    """Incidence graph of points and lines of the generalized quadrangle W(q); degree q + 1, diameter 4."""
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
    """Generalized quadrangle W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python growth pipeline: twins and cover vertices, used as the start for C.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods are cover sets of all vertices."""
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
            for attempt in range(40):
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
    """Greedily join deficient opposite-side vertices in random order."""
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


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured start: PG(2,q) for D = 3, W(q) for D = 4.
    base = None
    if D == 3:
        base = _best_pg(d)
    elif D == 4:
        base = _best_gq(d)
    if base is not None:
        consider(base[0], base[1])
        n2, e2 = _pipeline(base[0], base[1], d, D, start + 0.2 * time_limit, rng)
        consider(n2, e2)

    # Bold branch: C annealing growth from the best graph found so far.
    # Each vertex is added by a covering neighbourhood, then 2-switch annealing
    # on the number of pairs at distance > D. Only valid states are emitted.
    c_end = start + 0.85 * time_limit
    hard_end = start + 0.95 * time_limit
    now = time.monotonic()
    if now < c_end - 1.0:
        try:
            text = lib.run_c(
                C_SOURCE,
                [d, D, int(seed) % (2 ** 31), round(c_end - now, 2)],
                stdin_graph=best,
                timeout=max(1.0, hard_end - now),
            )
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
