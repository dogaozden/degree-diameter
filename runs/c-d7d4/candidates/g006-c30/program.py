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

#define MAXN 2048
#define MAXW 32
#define MAXD 128
#define ANNEAL_ITERS 1500

typedef uint64_t BSet[MAXW];

static unsigned char A[MAXN][MAXN];
static unsigned char SA[MAXN][MAXN];
static unsigned char BA_[MAXN][MAXN];
static int deg[MAXN], col[MAXN];
static int sdeg[MAXN], scol[MAXN], SN;
static int bcol[MAXN], bestN;
static int NB[MAXN][MAXD], nbc[MAXN];
static BSet BUF1[MAXN], BUF2[MAXN];
static int N, DDEG, DIAM;
static uint64_t rs = 88172645463325252ULL;
static clock_t T0;
static double TBUD;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) {
    if (k <= 0) return 0;
    return (int)(rnext() % (uint64_t)k);
}

static int timeup(void) {
    return (double)(clock() - T0) / CLOCKS_PER_SEC > TBUD;
}

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void addE(int a, int b) {
    A[a][b] = 1;
    A[b][a] = 1;
    deg[a]++;
    deg[b]++;
}

static void delE(int a, int b) {
    A[a][b] = 0;
    A[b][a] = 0;
    deg[a]--;
    deg[b]--;
}

static void build_nb(void) {
    for (int v = 0; v < N; v++) {
        nbc[v] = 0;
        for (int u = 0; u < N; u++)
            if (A[v][u]) NB[v][nbc[v]++] = u;
    }
}

/* Bitset of vertices within distance r of each vertex. */
static BSet *balls(int r) {
    int n = N, w = (n + 63) >> 6;
    BSet *cur = BUF1, *nxt = BUF2;
    build_nb();
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(BSet));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *t = nxt[v];
            memcpy(t, cur[v], sizeof(uint64_t) * w);
            for (int k = 0; k < nbc[v]; k++) {
                const uint64_t *s = cur[NB[v][k]];
                for (int q = 0; q < w; q++) t[q] |= s[q];
            }
        }
        BSet *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    return cur;
}

/* Ordered pairs at distance > DIAM (0 iff valid diameter). */
static long cost(void) {
    BSet *b = balls(DIAM);
    int w = (N + 63) >> 6;
    long reach = 0;
    for (int v = 0; v < N; v++)
        for (int q = 0; q < w; q++) reach += pc(b[v][q]);
    return (long)N * N - reach;
}

static int rand_nbr(int s) {
    int c = 0;
    for (int u = 0; u < N; u++) c += A[s][u];
    if (c == 0) return -1;
    int k = rndint(c);
    for (int u = 0; u < N; u++) {
        if (A[s][u]) {
            if (k == 0) return u;
            k--;
        }
    }
    return -1;
}

/* Append a vertex on the opposite side of `side`, joined to a greedy cover. */
static void add_vertex(int side) {
    int n = N, w = (n + 63) >> 6;
    if (n >= MAXN - 1) return;
    BSet *b = balls(DIAM > 0 ? DIAM - 1 : 0);
    BSet cov;
    memset(cov, 0, sizeof cov);
    int chosen[MAXD];
    int nc = 0;
    unsigned char used[MAXN];
    memset(used, 0, sizeof(unsigned char) * n);
    for (int it = 0; it < DDEG; it++) {
        int best = -1, bg = -1, ties = 0;
        for (int s = 0; s < n; s++) {
            if (col[s] != side || used[s]) continue;
            int g = 0;
            for (int q = 0; q < w; q++) g += pc(b[s][q] & ~cov[q]);
            if (g > bg) {
                bg = g;
                best = s;
                ties = 1;
            } else if (g == bg && g > 0) {
                ties++;
                if (rndint(ties) == 0) best = s;
            }
        }
        if (best < 0 || bg <= 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int q = 0; q < w; q++) cov[q] |= b[best][q];
    }
    for (int u = 0; u <= n; u++) {
        A[u][n] = 0;
        A[n][u] = 0;
    }
    int v = n;
    N = n + 1;
    col[v] = 1 - side;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (deg[s] >= DDEG) {
            int t = rand_nbr(s);
            if (t >= 0) delE(s, t);
        }
        addE(s, v);
    }
}

/* Remove vertex x (swap-remove with the last vertex). */
static void kill_vertex(int x) {
    for (int u = 0; u < N; u++)
        if (A[x][u]) delE(x, u);
    int last = N - 1;
    if (x != last) {
        for (int u = 0; u < N; u++) A[x][u] = A[last][u];
        for (int u = 0; u < N; u++) A[u][x] = A[u][last];
        deg[x] = deg[last];
        col[x] = col[last];
    }
    for (int u = 0; u < N; u++) {
        A[last][u] = 0;
        A[u][last] = 0;
    }
    deg[last] = 0;
    col[last] = 0;
    N--;
}

/* Add cross-side edges between deficient vertices. */
static void fill(void) {
    int n = N;
    if (n == 0) return;
    int off = rndint(n);
    for (int i = 0; i < n; i++) {
        int a = (i + off) % n;
        if (col[a] != 0 || deg[a] >= DDEG) continue;
        for (int j = 0; j < n && deg[a] < DDEG; j++) {
            int b = (j + off) % n;
            if (col[b] != 1 || deg[b] >= DDEG || A[a][b]) continue;
            addE(a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static int anneal(int iters) {
    long cur = cost();
    int n = N;
    for (int it = 0; it < iters && cur > 0; it++) {
        if (timeup()) break;
        int a = rndint(n);
        if (col[a] != 0 || deg[a] == 0) continue;
        int b = rand_nbr(a);
        int c = rndint(n);
        if (c == a || col[c] != 0 || deg[c] == 0) continue;
        int e = rand_nbr(c);
        if (b < 0 || e < 0) continue;
        if (A[a][e] || A[c][b] || b == e) continue;
        delE(a, b);
        delE(c, e);
        addE(a, e);
        addE(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 2 && rndint(10) == 0)) {
            cur = nw;
        } else {
            delE(a, e);
            delE(c, b);
            addE(a, b);
            addE(c, e);
        }
    }
    return cur == 0;
}

static void snap(void) {
    SN = N;
    for (int v = 0; v < N; v++) {
        memcpy(SA[v], A[v], N);
        sdeg[v] = deg[v];
        scol[v] = col[v];
    }
}

static void restore(void) {
    for (int v = 0; v < N; v++) memset(A[v], 0, N);
    N = SN;
    for (int v = 0; v < N; v++) {
        memcpy(A[v], SA[v], N);
        deg[v] = sdeg[v];
        col[v] = scol[v];
    }
}

static void save_best(void) {
    bestN = N;
    for (int v = 0; v < N; v++) {
        memcpy(BA_[v], A[v], N);
        bcol[v] = col[v];
    }
}

static void load_best(void) {
    for (int v = 0; v < N; v++) memset(A[v], 0, N);
    N = bestN;
    for (int v = 0; v < N; v++) {
        memcpy(A[v], BA_[v], N);
        col[v] = bcol[v];
    }
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int u = 0; u < N; u++) c += A[v][u];
        deg[v] = c;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TBUD = atof(argv[4]);
    if (d < 1 || d > MAXD - 1 || D < 2) return 1;
    DDEG = d;
    DIAM = D;
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    T0 = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n > 0) {
        if (n > MAXN) return 1;
        N = n;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u == v || u < 0 || v < 0 || u >= N || v >= N || A[u][v]) continue;
            addE(u, v);
        }
        for (int v = 0; v < N; v++) col[v] = -1;
        static int stk[MAXN];
        for (int s = 0; s < N; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp) {
                int x = stk[--sp];
                for (int y = 0; y < N; y++) {
                    if (A[x][y] && col[y] == -1) {
                        col[y] = 1 - col[x];
                        stk[sp++] = y;
                    }
                }
            }
        }
    } else {
        N = 2 * d;
        for (int v = 0; v < N; v++) col[v] = (v < d) ? 0 : 1;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) addE(a, d + b);
    }

    save_best();
    int stall = 0;
    while (!timeup()) {
        int curN = N;
        snap();
        if (rndint(100) < 55) {
            add_vertex(rndint(2));
        } else {
            int k = 1 + rndint(2);
            for (int i = 0; i < k && N > 2; i++) kill_vertex(rndint(N));
        }
        fill();
        int ok = anneal(ANNEAL_ITERS);
        if (ok && N >= curN - 1) {
            if (N > bestN) {
                save_best();
                stall = 0;
            } else {
                stall++;
            }
        } else {
            restore();
            stall++;
        }
        if (stall > 300 && N < bestN) {
            load_best();
            stall = 0;
        }
    }

    int m2 = 0;
    for (int u = 0; u < bestN; u++)
        for (int v = u + 1; v < bestN; v++)
            if (BA_[u][v]) m2++;
    printf("%d %d\n", bestN, m2);
    for (int u = 0; u < bestN; u++)
        for (int v = u + 1; v < bestN; v++)
            if (BA_[u][v]) printf("%d %d\n", u, v);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared Python helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _greedy_cover(cands, ball, full, d, rng, randomize):
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
    """Greedily add vertices whose neighbourhoods cover all vertices on one side."""
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
    """Join deficient opposite-side vertices in random order (keeps validity)."""
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
# Python kill-repair-regrow LNS, anchored to its best graph.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Entry point: structured base, Python growth, then the C search engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base_n, base_e = best_n, list(best_e)
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
        consider(n1, e1)

    # Randomized twin-duplication pipelines.
    trial_end = start + 0.18 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Short Python LNS.
    _lns(best_n, best_e, d, D, start + 0.28 * time_limit, rng, consider)

    # C engine: add/kill/repair with bitset-based bad-pair annealing.
    c_end = start + 0.85 * time_limit
    budget = c_end - time.monotonic() - 1.0
    if budget >= 1.0 and d <= 120 and best_n < 2000:
        try:
            txt = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                            stdin_graph=(best_n, best_e),
                            timeout=max(3.0, start + 0.93 * time_limit - time.monotonic()))
            consider(*lib.parse_graph_text(txt))
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
