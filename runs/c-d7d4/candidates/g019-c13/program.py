import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 40
#define W 18

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} State;

static State cur, snap, best;
static int have_best = 0, best_n = 0;
static int dd, DD;
static uint64_t rs = 88172645463325252ULL;
static uint64_t ballA[MAXN][W];
static uint64_t tmpB[MAXN][W];
static clock_t t0;
static double tlim;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int has_edge(const State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(State *s, int u, int v) {
    s->adj[u][s->deg[u]++] = v;
    s->adj[v][s->deg[v]++] = u;
}

static void del_half(State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) {
        if (s->adj[u][i] == v) {
            s->adj[u][i] = s->adj[u][--s->deg[u]];
            return;
        }
    }
}

static void del_edge(State *s, int u, int v) {
    del_half(s, u, v);
    del_half(s, v, u);
}

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* out[v] = bitset of vertices within distance r of v. */
static void compute_ball(const State *s, int r, uint64_t out[][W]) {
    int n = s->n, w = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(out[v], 0, sizeof(uint64_t) * W);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < r; step++) {
        for (int v = 0; v < n; v++) {
            uint64_t *t = tmpB[v];
            memcpy(t, out[v], sizeof(uint64_t) * w);
            for (int i = 0; i < s->deg[v]; i++) {
                const uint64_t *o = out[s->adj[v][i]];
                for (int k = 0; k < w; k++) t[k] |= o[k];
            }
        }
        for (int v = 0; v < n; v++) memcpy(out[v], tmpB[v], sizeof(uint64_t) * w);
    }
}

/* Number of unordered pairs at distance greater than DD (unreachable counts). */
static long long cost_of(const State *s) {
    compute_ball(s, DD, ballA);
    int n = s->n, w = (n + 63) / 64;
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += pc(ballA[v][k]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add a vertex on the opposite side of `side`, joined to a greedy cover of `side`. */
static void add_vertex(State *s, int side) {
    int n = s->n, w = (n + 63) / 64;
    compute_ball(s, DD - 1, ballA);
    uint64_t cov[W];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD];
    int nc = 0;
    int v = n;
    s->n = n + 1;
    s->deg[v] = 0;
    s->col[v] = 1 - side;
    for (int it = 0; it < dd; it++) {
        int bs = -1;
        double bg = -1.0;
        for (int x = 0; x < n; x++) {
            if (s->col[x] != side) continue;
            int used = 0;
            for (int i = 0; i < nc; i++) if (chosen[i] == x) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += pc(ballA[x][k] & ~cov[k]);
            double sc = (double)g + 0.5 * rndf();
            if (sc > bg) { bg = sc; bs = x; }
        }
        if (bs < 0) break;
        chosen[nc++] = bs;
        for (int k = 0; k < w; k++) cov[k] |= ballA[bs][k];
    }
    for (int i = 0; i < nc; i++) {
        int x = chosen[i];
        if (s->deg[x] >= dd) {
            int t = s->adj[x][rndi(s->deg[x])];
            del_edge(s, x, t);
        }
        add_edge(s, x, v);
    }
}

/* Delete vertex x; the last vertex is relabelled into slot x. */
static void remove_vertex(State *s, int x) {
    int n = s->n;
    for (int i = 0; i < s->deg[x]; i++) {
        int u = s->adj[x][i];
        del_half(s, u, x);
    }
    s->deg[x] = 0;
    int last = n - 1;
    if (x != last) {
        s->deg[x] = s->deg[last];
        for (int i = 0; i < s->deg[last]; i++) s->adj[x][i] = s->adj[last][i];
        s->col[x] = s->col[last];
        for (int i = 0; i < s->deg[x]; i++) {
            int u = s->adj[x][i];
            for (int j = 0; j < s->deg[u]; j++) {
                if (s->adj[u][j] == last) { s->adj[u][j] = x; break; }
            }
        }
    }
    s->n = n - 1;
}

/* Add cross-side edges between deficient vertices in random order. */
static void fill(State *s) {
    int n = s->n;
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (s->deg[v] >= dd) continue;
        if (s->col[v] == 0) L[nl++] = v; else R[nr++] = v;
    }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && s->deg[a] < dd; j++) {
            int b = R[j];
            if (s->deg[b] < dd && !has_edge(s, a, b)) add_edge(s, a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static long long anneal(State *s, long long cur_c, int iters, double T) {
    static int side0[MAXN];
    int n = s->n, ns = 0, n1 = 0;
    for (int v = 0; v < n; v++) {
        if (s->col[v] == 0) side0[ns++] = v; else n1++;
    }
    if (ns < 2 || n1 < 1) return cur_c;
    for (int it = 0; it < iters && cur_c > 0; it++) {
        int a = side0[rndi(ns)];
        int c = side0[rndi(ns)];
        if (c == a || s->deg[a] == 0 || s->deg[c] == 0) continue;
        int b = s->adj[a][rndi(s->deg[a])];
        int e = s->adj[c][rndi(s->deg[c])];
        if (has_edge(s, a, e) || has_edge(s, c, b)) continue;
        del_edge(s, a, b);
        del_edge(s, c, e);
        add_edge(s, a, e);
        add_edge(s, c, b);
        long long nw = cost_of(s);
        int acc = 0;
        if (nw <= cur_c) acc = 1;
        else if (T > 0 && rndf() < exp(-(double)(nw - cur_c) / T)) acc = 1;
        if (acc) {
            cur_c = nw;
        } else {
            del_edge(s, a, e);
            del_edge(s, c, b);
            add_edge(s, a, b);
            add_edge(s, c, e);
        }
    }
    return cur_c;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    tlim = atof(argv[4]);
    dd = d;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    t0 = clock();
    if (dd < 1 || dd > MAXD || DD < 2) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 64) { printf("0 0\n"); return 0; }
    memset(&cur, 0, sizeof cur);
    cur.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (cur.deg[u] >= dd || cur.deg[v] >= dd || has_edge(&cur, u, v)) continue;
        add_edge(&cur, u, v);
    }

    static int stk[MAXN];
    for (int v = 0; v < n; v++) cur.col[v] = -1;
    int ok = 1;
    for (int s0 = 0; s0 < n && ok; s0++) {
        if (cur.col[s0] != -1) continue;
        cur.col[s0] = 0;
        int sp = 0;
        stk[sp++] = s0;
        while (sp && ok) {
            int u = stk[--sp];
            for (int i = 0; i < cur.deg[u]; i++) {
                int w = cur.adj[u][i];
                if (cur.col[w] == -1) {
                    cur.col[w] = 1 - cur.col[u];
                    stk[sp++] = w;
                } else if (cur.col[w] == cur.col[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    long long c0 = cost_of(&cur);
    if (c0 > 0) c0 = anneal(&cur, c0, 200000, 0.3);
    if (c0 == 0) {
        best = cur;
        have_best = 1;
        best_n = cur.n;
    }
    if (!have_best) { printf("0 0\n"); return 0; }

    cur = best;
    int no_imp = 0;
    while (elapsed() < tlim) {
        snap = cur;
        if (rndi(10) < 6 && cur.n + 1 < MAXN - 1) {
            add_vertex(&cur, rndi(2));
        } else {
            int k = 1 + rndi(2);
            for (int i = 0; i < k && cur.n > 4; i++) remove_vertex(&cur, rndi(cur.n));
        }
        fill(&cur);
        long long c = cost_of(&cur);
        c = anneal(&cur, c, 1500, 0.4);
        if (c == 0) {
            if (cur.n > best_n) {
                best = cur;
                best_n = cur.n;
                no_imp = 0;
            } else {
                no_imp++;
            }
            if (cur.n < best_n - 3) cur = best;
        } else {
            cur = snap;
            no_imp++;
        }
        if (no_imp > 400) {
            cur = best;
            no_imp = 0;
        }
    }

    int cnt = 0;
    for (int u = 0; u < best.n; u++)
        for (int i = 0; i < best.deg[u]; i++)
            if (u < best.adj[u][i]) cnt++;
    printf("%d %d\n", best.n, cnt);
    for (int u = 0; u < best.n; u++)
        for (int i = 0; i < best.deg[u]; i++)
            if (u < best.adj[u][i]) printf("%d %d\n", u, best.adj[u][i]);
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
# Bipartite voltage lifts over small (cyclic or semidirect) groups.
# ----------------------------------------------------------------------------

def _pick_group(order, rng):
    """Return (order, mul) for a cyclic or a semidirect group of the given order."""
    if order >= 4 and rng.random() < 0.5:
        ks = [k for k in range(2, 13) if order % k == 0 and order // k >= 2]
        rng.shuffle(ks)
        for k in ks:
            m = order // k
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                r = rng.choice(rs)
                try:
                    o, mul, _ = lib.semidirect_group(m, k, r)
                    return o, mul
                except ValueError:
                    continue
    o, mul, _ = lib.cyclic_group(order)
    return o, mul


def _init_darts(s, d, order, rng):
    """Darts (u, v, g): A vertex u, B vertex v (local), voltage g. Each vertex gets d darts."""
    slots = [v for v in range(s) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    seen = set()
    for u in range(s):
        for j in range(d):
            v = slots[u * d + j]
            for _ in range(60):
                g = rng.randrange(order)
                if (u, v, g) not in seen:
                    break
            else:
                return None
            seen.add((u, v, g))
            darts.append((u, v, g))
    return darts


def _lift(s, darts, order, mul):
    """Lift the base graph: A side is 0..s-1, B side is s..2s-1."""
    return lib.group_lift(2 * s, [(u, s + v, g) for u, v, g in darts], order, mul)


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Hill-climb voltages of small bipartite base lifts until a diameter-D lift appears."""
    base_pick = (1, 1, 2, 2, 3)
    while time.monotonic() < deadline:
        s = rng.choice(base_pick)
        base_n = 2 * s
        lo = best_n // base_n
        order = lo + 1 + rng.randrange(0, max(2, lo // 8 + 1))
        order, mul = _pick_group(order, rng)
        darts = _init_darts(s, d, order, rng)
        if darts is None:
            continue
        n, e = _lift(s, darts, order, mul)
        cost = lib.bad_pairs(n, e, D)
        steps = 0
        while cost > 0 and steps < 250 and time.monotonic() < deadline:
            steps += 1
            i = rng.randrange(len(darts))
            u, v, old = darts[i]
            g2 = rng.randrange(order)
            if g2 == old or (u, v, g2) in set(darts):
                continue
            darts[i] = (u, v, g2)
            n2, e2 = _lift(s, darts, order, mul)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cost or rng.random() < 0.02:
                cost, n, e = c2, n2, e2
            else:
                darts[i] = (u, v, old)
        if cost == 0 and time.monotonic() < deadline:
            consider(n, e)
            n3, e3 = _grow(n, e, d, D, deadline, rng)
            consider(n3, e3)
            best_n = max(best_n, n3)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) or PG(2,q)) grown, twin trials
#   L  voltage lifts over small groups
#   C  C engine: vertex add/remove, anneal repair, from the best valid graph
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), valid for every d >= 1 and D >= 2.
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

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base and twin trials.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.06), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.10)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.16):
        _lift_search(d, D, best_n, rng, at(0.16), consider)

    # Phase C: C engine from the best valid graph found so far.
    if D >= 2 and d >= 2 and best_n >= 2:
        budget = start + 0.88 * time_limit - time.monotonic() - 2.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
