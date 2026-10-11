"""Structured base (generalized quadrangle or projective plane), Python twin/cover growth,
then a C engine that grows the best graph by vertex insertion with bitset-based repair.

C engine: each attempt inserts one vertex joined to a greedy cover of the opposite side
(balls of radius D-1 as bitsets). Opposite-side deficient pairs are filled, then bipartite
double-edge switches anneal the number of pairs at distance > D to zero. Failed attempts are
rolled back through an edge journal. Successes are followed by redundant-edge pruning, which
frees degree for later insertions. After repeated failures the engine takes a plateau walk
of cost-preserving switches.
"""
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

#define MAXN 1600
#define MAXW (MAXN / 64 + 2)
#define MAXD 40
#define JMAX (1 << 20)
#define ANNEAL_IT 1500

static int dd, DD;
static int n;
static int color[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static uint64_t BUF[2][MAXN][MAXW];
static uint64_t CB[MAXN][MAXW];
static int JT[JMAX][3];
static int jn = 0, jactive = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t t_end;
static int used[MAXN];
static int cand[MAXN];
static int S0[MAXN];
static int ns0 = 0;
static int EA[MAXN * MAXD], EB[MAXN * MAXD];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle_int(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static void raw_del_one(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][--deg[a]];
            return;
        }
    }
}

static void raw_add(int a, int b) {
    A[a][b] = 1;
    A[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void raw_rem(int a, int b) {
    A[a][b] = 0;
    A[b][a] = 0;
    raw_del_one(a, b);
    raw_del_one(b, a);
}

static void J_add(int a, int b) {
    raw_add(a, b);
    if (jactive) {
        JT[jn][0] = 1;
        JT[jn][1] = a;
        JT[jn][2] = b;
        jn++;
    }
}

static void J_rem(int a, int b) {
    raw_rem(a, b);
    if (jactive) {
        JT[jn][0] = 0;
        JT[jn][1] = a;
        JT[jn][2] = b;
        jn++;
    }
}

static void undo_to(int mark) {
    while (jn > mark) {
        jn--;
        if (JT[jn][0]) raw_rem(JT[jn][1], JT[jn][2]);
        else raw_add(JT[jn][1], JT[jn][2]);
    }
}

/* Bitmask of vertices within distance r of each vertex; returns buffer index. */
static int compute_balls(int r) {
    int W = (n + 63) >> 6;
    int cur = 0;
    for (int v = 0; v < n; v++) {
        memset(BUF[0][v], 0, sizeof(uint64_t) * W);
        BUF[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        int nx = 1 - cur;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = BUF[nx][v];
            memcpy(dst, BUF[cur][v], sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = BUF[cur][nb[v][k]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        cur = nx;
    }
    return cur;
}

/* Number of unordered pairs at distance greater than DD (unreachable counts). */
static long cost(void) {
    int idx = compute_balls(DD);
    int W = (n + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(BUF[idx][v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void build_s0(void) {
    ns0 = 0;
    for (int v = 0; v < n; v++)
        if (color[v] == 0) S0[ns0++] = v;
}

/* Bipartite double-edge switch on side-0 list S: a-b, c-e -> a-e, c-b. */
static int do_switch(const int *S, int ns) {
    if (ns < 2) return 0;
    for (int tries = 0; tries < 40; tries++) {
        int a = S[rndi(ns)];
        if (deg[a] == 0) continue;
        int b = nb[a][rndi(deg[a])];
        int c = S[rndi(ns)];
        if (c == a || deg[c] == 0) continue;
        int e = nb[c][rndi(deg[c])];
        if (A[a][e] || A[c][b]) continue;
        J_rem(a, b);
        J_rem(c, e);
        J_add(a, e);
        J_add(c, b);
        return 1;
    }
    return 0;
}

static int anneal(const int *S, int ns, int iters) {
    long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && clock() > t_end) break;
        if (jn > JMAX - 1000) break;
        int m0 = jn;
        if (!do_switch(S, ns)) continue;
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndi(100) < 8)) cur = nw;
        else undo_to(m0);
    }
    return cur == 0;
}

/* Join deficient opposite-side vertices in random order (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dd) {
            if (color[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < dd; j++) {
            int b = R[j];
            if (deg[b] < dd && !A[a][b]) J_add(a, b);
        }
    }
}

/* Insert one vertex on the side opposite to a random side, then anneal. Rolls back on failure. */
static int attempt(void) {
    int nbf = n;
    if (nbf + 4 >= MAXN) return 0;
    int s = rndi(2);
    int ncand = 0;
    for (int v = 0; v < nbf; v++)
        if (color[v] == s) cand[ncand++] = v;
    if (ncand == 0) return 0;

    int idx = compute_balls(DD - 1);
    int W0 = (nbf + 63) >> 6;
    for (int v = 0; v < nbf; v++) memcpy(CB[v], BUF[idx][v], sizeof(uint64_t) * W0);

    jn = 0;
    jactive = 1;
    int chosen[MAXD];
    int nch = 0;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(uint64_t) * W0);
    for (int k = 0; k < dd && nch < ncand; k++) {
        int best = -1;
        long bsc = -1;
        for (int i = 0; i < ncand; i++) {
            int c = cand[i];
            if (used[c]) continue;
            int g = 0;
            for (int w = 0; w < W0; w++) g += pc64(CB[c][w] & ~cov[w]);
            long sc = (long)g * 64 + rndi(64);
            if (sc > bsc) {
                bsc = sc;
                best = c;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W0; w++) cov[w] |= CB[best][w];
    }
    for (int i = 0; i < nch; i++) used[chosen[i]] = 0;

    int v = nbf;
    n = nbf + 1;
    color[v] = 1 - s;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int c = chosen[i];
        if (deg[c] >= dd) {
            int t = nb[c][rndi(deg[c])];
            J_rem(c, t);
        }
        J_add(c, v);
    }

    fill();
    build_s0();
    int ok = anneal(S0, ns0, ANNEAL_IT);
    if (ok) {
        jn = 0;
        jactive = 0;
        return 1;
    }
    undo_to(0);
    n = nbf;
    jn = 0;
    jactive = 0;
    return 0;
}

/* Cost-preserving random walk on valid graphs, for escaping plateaus. */
static void walk(int steps) {
    build_s0();
    jactive = 1;
    for (int i = 0; i < steps && clock() < t_end; i++) {
        jn = 0;
        if (!do_switch(S0, ns0)) continue;
        if (cost() != 0) undo_to(0);
    }
    jn = 0;
    jactive = 0;
}

/* Delete random edges while the diameter bound still holds. */
static void prune(int tests) {
    jactive = 0;
    int m = 0;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (v < u) {
                EA[m] = v;
                EB[m] = u;
                m++;
            }
        }
    }
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = EA[i];
        EA[i] = EA[j];
        EA[j] = t;
        t = EB[i];
        EB[i] = EB[j];
        EB[j] = t;
    }
    for (int i = 0; i < m && tests > 0; i++) {
        int a = EA[i], b = EB[i];
        tests--;
        raw_rem(a, b);
        if (cost() != 0) raw_add(a, b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 12345ULL;
    double budget = atof(argv[4]);
    t_end = clock() + (clock_t)(budget * CLOCKS_PER_SEC);

    int in_n = 0, in_m = 0;
    if (scanf("%d %d", &in_n, &in_m) != 2) in_n = 0;
    if (in_n < 1 || in_n > MAXN - 200 || dd < 1 || dd > MAXD || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    n = in_n;
    for (int i = 0; i < in_m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || a >= n || b < 0 || b >= n || a == b) continue;
        if (A[a][b] || deg[a] >= dd || deg[b] >= dd) continue;
        raw_add(a, b);
    }

    /* 2-colour the input (any colouring works if the graph is bipartite). */
    static int stk[MAXN];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (color[w] < 0) {
                    color[w] = 1 - color[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    /* Repair the input if it is not yet valid. */
    build_s0();
    jactive = 1;
    jn = 0;
    anneal(S0, ns0, ANNEAL_IT * 5);
    jn = 0;
    jactive = 0;

    int fails = 0;
    while (clock() < t_end) {
        if (n >= MAXN - 4) break;
        if (attempt()) {
            fails = 0;
            prune(150);
        } else if (++fails >= 12) {
            walk(200);
            fails = 0;
        }
    }

    jactive = 0;
    jn = 0;
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %d\n", n, m);
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
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
# Shared Python helpers.
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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


def _spare_matching_base(n0, e0, d, rng, keep_free):
    """Match spare slots of a point-line base with non-incident cross edges, keeping some free."""
    n = n0
    half = n // 2
    adj = _to_sets(n, e0)
    rounds = d - max(len(a) for a in adj)
    for _ in range(max(0, rounds)):
        order = [p for p in range(half) if len(adj[p]) < d]
        rng.shuffle(order)
        target = max(0, len(order) - keep_free)
        count = 0
        for p in order:
            if count >= target:
                break
            cands = [L for L in range(half, n) if len(adj[L]) < d and L not in adj[p]]
            if not cands:
                continue
            L = rng.choice(cands)
            adj[p].add(L)
            adj[L].add(p)
            count += 1
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins (same neighbourhood, same side) in random order while degrees allow."""
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    ub = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane otherwise.
    base_n, base_e = best_n, list(best_e)
    base_is_gq = False
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is not None:
            base_is_gq = True
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.14 * time_limit, rng)
            consider(n1, e1)
        if best_n >= ub:
            return best_n, list(best_e)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.20 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Spare-slot matching on the quadrangle base, with a sweep of kept free slots.
    if base_is_gq and D >= 4:
        spare_end = start + 0.26 * time_limit
        while time.monotonic() < spare_end:
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            gn, ge = _grow(sn, se, d, D, spare_end, rng)
            consider(gn, ge)

    if best_n >= ub:
        return best_n, list(best_e)

    # C engine: vertex insertion with bitset-based annealing repair, from the best graph.
    c_end = start + 0.85 * time_limit - 2.0
    budget = c_end - time.monotonic()
    if D >= 2 and budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=(best_n, best_e), timeout=budget + 3.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
