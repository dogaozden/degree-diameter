import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define NMAX 1024
#define DMAX 64
#define WMAX 16

typedef struct {
    int n;
    int deg[NMAX];
    int adj[NMAX][DMAX];
    int col[NMAX];
} State;

typedef uint64_t Row[WMAX];

static State cur, bak, best;
static Row bufA[NMAX], bufB[NMAX];
static int PP[NMAX * NMAX];
static int D, dd;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return k <= 0 ? 0 : (int)(rnd64() % (uint64_t)k); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int pc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static int has_nb(const State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] == v) return 1;
    return 0;
}
/* replace neighbour old by nw in adj[u] */
static void rep(State *s, int u, int old, int nw) {
    for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] == old) { s->adj[u][i] = nw; return; }
}
/* delete v from adj[u] */
static void del_nb(State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] == v) {
        s->adj[u][i] = s->adj[u][s->deg[u] - 1];
        s->deg[u]--;
        return;
    }
}
static void add_edge(State *s, int u, int v) {
    s->adj[u][s->deg[u]++] = v;
    s->adj[v][s->deg[v]++] = u;
}

/* ball[v] = bitmask of vertices within distance r of v */
static Row *compute_ball(const State *s, int r) {
    int n = s->n, W = (n + 63) >> 6;
    Row *A = bufA, *B = bufB;
    memset(A, 0, sizeof(Row) * (size_t)n);
    for (int v = 0; v < n; v++) A[v][v >> 6] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) B[v][w] = A[v][w];
            for (int i = 0; i < s->deg[v]; i++) {
                int u = s->adj[v][i];
                for (int w = 0; w < W; w++) B[v][w] |= A[u][w];
            }
        }
        Row *t = A; A = B; B = t;
    }
    return A;
}

/* number of unordered pairs at distance > D */
static long cost(const State *s) {
    int n = s->n, W = (n + 63) >> 6;
    Row *b = compute_ball(s, D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(b[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* degree-preserving bipartite switches minimising bad pairs; true if cost reaches 0 */
static int anneal(State *s, int iters, double deadline) {
    long c = cost(s);
    for (int it = 0; it < iters && c > 0; it++) {
        if ((it & 31) == 0 && now_s() > deadline) break;
        int n = s->n;
        int a = rndint(n), c2 = rndint(n);
        if (a == c2 || s->col[a] != 0 || s->col[c2] != 0) continue;
        if (s->deg[a] == 0 || s->deg[c2] == 0) continue;
        int b = s->adj[a][rndint(s->deg[a])];
        int e = s->adj[c2][rndint(s->deg[c2])];
        if (has_nb(s, a, e) || has_nb(s, c2, b)) continue;
        rep(s, a, b, e); rep(s, e, c2, a); rep(s, c2, e, b); rep(s, b, a, c2);
        long nc = cost(s);
        if (nc <= c || (nc == c + 1 && rndint(100) < 5)) {
            c = nc;
        } else {
            rep(s, a, e, b); rep(s, e, a, c2); rep(s, c2, b, e); rep(s, b, c2, a);
        }
    }
    return c == 0;
}

/* add cross-side edges between deficient vertices in random order */
static void fill(State *s) {
    int n = s->n, cnt = 0;
    for (int a = 0; a < n; a++) {
        if (s->col[a] != 0 || s->deg[a] >= dd) continue;
        for (int b = 0; b < n; b++) {
            if (s->col[b] != 1 || s->deg[b] >= dd) continue;
            if (has_nb(s, a, b)) continue;
            PP[cnt++] = a * NMAX + b;
        }
    }
    for (int i = cnt - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = PP[i]; PP[i] = PP[j]; PP[j] = t;
    }
    for (int i = 0; i < cnt; i++) {
        int a = PP[i] / NMAX, b = PP[i] % NMAX;
        if (s->deg[a] < dd && s->deg[b] < dd && !has_nb(s, a, b)) add_edge(s, a, b);
    }
}

/* new vertex on the side opposite `side`, joined to a greedy cover of `side` */
static void add_vertex(State *s, int side) {
    int n = s->n;
    if (n >= NMAX - 1) return;
    Row *b = compute_ball(s, D - 1);
    int W = (n + 63) >> 6;
    uint64_t cov[WMAX];
    memset(cov, 0, sizeof cov);
    int chosen[DMAX], nc = 0;
    for (int k = 0; k < dd; k++) {
        int bv = -1;
        double bs = -1.0;
        for (int v = 0; v < n; v++) {
            if (s->col[v] != side) continue;
            int used = 0;
            for (int i = 0; i < nc; i++) if (chosen[i] == v) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc(b[v][w] & ~cov[w]);
            double sc = g + 0.5 * (double)(rnd64() % 1000) / 1000.0;
            if (sc > bs) { bs = sc; bv = v; }
        }
        if (bv < 0) break;
        chosen[nc++] = bv;
        for (int w = 0; w < W; w++) cov[w] |= b[bv][w];
    }
    int v = n;
    s->n = n + 1;
    s->deg[v] = 0;
    s->col[v] = 1 - side;
    for (int i = 0; i < nc; i++) {
        int u = chosen[i];
        if (s->deg[u] >= dd) {
            int t = s->adj[u][rndint(s->deg[u])];
            del_nb(s, u, t);
            del_nb(s, t, u);
        }
        add_edge(s, u, v);
    }
}

/* delete vertex x, moving the last vertex into its slot */
static void remove_vertex(State *s, int x) {
    int last = s->n - 1;
    for (int i = 0; i < s->deg[x]; i++) del_nb(s, s->adj[x][i], x);
    s->deg[x] = 0;
    if (x != last) {
        for (int i = 0; i < s->deg[last]; i++) rep(s, s->adj[last][i], last, x);
        s->deg[x] = s->deg[last];
        for (int i = 0; i < s->deg[last]; i++) s->adj[x][i] = s->adj[last][i];
        s->col[x] = s->col[last];
    }
    s->deg[last] = 0;
    s->n = last;
}

static int q_buf[NMAX];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)atoll(argv[3]);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    dd = d;
    if (dd > DMAX - 1) dd = DMAX - 1;
    double deadline = now_s() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 0 || n > NMAX - 1) n = 0;
    if (n == 0) { printf("0 0\n"); return 0; }
    memset(&cur, 0, sizeof cur);
    cur.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (cur.deg[u] >= dd || cur.deg[v] >= dd || has_nb(&cur, u, v)) continue;
        add_edge(&cur, u, v);
    }
    for (int v = 0; v < n; v++) cur.col[v] = -1;
    for (int s0 = 0; s0 < n; s0++) {
        if (cur.col[s0] != -1) continue;
        cur.col[s0] = 0;
        int qh = 0, qt = 0;
        q_buf[qt++] = s0;
        while (qh < qt) {
            int x = q_buf[qh++];
            for (int i = 0; i < cur.deg[x]; i++) {
                int y = cur.adj[x][i];
                if (cur.col[y] == -1) { cur.col[y] = 1 - cur.col[x]; q_buf[qt++] = y; }
            }
        }
    }

    best = cur;
    if (D >= 2) {
        while (now_s() < deadline) {
            bak = cur;
            int mode = rndint(10);
            if (mode < 4 || cur.n < 4) {
                add_vertex(&cur, rndint(2));
            } else {
                int k = 1 + rndint(2);
                for (int j = 0; j < k && cur.n > 3; j++) remove_vertex(&cur, rndint(cur.n));
                int adds = k + (mode >= 8 ? 1 : 0);
                for (int j = 0; j < adds; j++) add_vertex(&cur, rndint(2));
            }
            fill(&cur);
            if (anneal(&cur, 600, deadline)) {
                if (cur.n > best.n) best = cur;
                if (cur.n < bak.n - 1) cur = bak;
                else if (cur.n + 3 < best.n) cur = best;
            } else {
                cur = bak;
            }
        }
    }

    long me = 0;
    for (int v = 0; v < best.n; v++)
        for (int i = 0; i < best.deg[v]; i++) if (best.adj[v][i] > v) me++;
    printf("%d %ld\n", best.n, me);
    for (int v = 0; v < best.n; v++)
        for (int i = 0; i < best.deg[v]; i++) {
            int u = best.adj[v][i];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
'''


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
    """Incidence graph of points and lines of the generalized quadrangle W(q); order 2(q+1)(q^2+1), diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q kept small for Python speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 8 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=200):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 steps."""
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
    """Join deficient opposite-side vertices in random order (keeps bipartite, degrees, validity)."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=200):
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
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
# Python fallback search (used only if the C engine fails).
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


def _anneal(adj, color, D, rng, iters, deadline):
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
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.05):
            cur = new
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    """Python kill-repair-regrow search; used only as a fallback."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
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
        if not _anneal(adj, color, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)

    # Already at the Moore bound: nothing more to find.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    if D >= 2:
        # Short Python pre-phase: randomized twin/cover pipelines from the base.
        base_n, base_e = best_n, list(best_e)
        pre_end = start + 0.12 * time_limit
        while time.monotonic() < pre_end:
            n, e = _trial(base_n, base_e, d, D, rng, pre_end)
            consider(n, e)

        # Main stage: C annealing engine starting from the best graph so far.
        elapsed = time.monotonic() - start
        c_budget = 0.80 * time_limit - elapsed - 2.0
        if c_budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=c_budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                # C engine unavailable or failed: use the Python search for the remaining time.
                _lns(best_n, best_e, d, D, deadline, rng, consider)

        # Leftover time (if any) goes to the Python search.
        if time.monotonic() < deadline - 0.5:
            _lns(best_n, best_e, d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
