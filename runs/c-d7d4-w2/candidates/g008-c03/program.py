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

#define MAXN 2600
#define MAXD 48
#define MAXW ((MAXN + 63) / 64)
#define LOGMAX (1 << 20)

static int dg, Dg, n;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char am[MAXN][MAXN];
static int col[MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static int log_t[LOGMAX], log_u[LOGMAX], log_v[LOGMAX];
static int logn = 0;
static int logging = 1;
static uint64_t rs = 88172645463325252ULL;
static double limit_s = 1.0;
static clock_t t0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdouble(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int timeup(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC > limit_s;
}

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static void lg(int t, int u, int v) {
    if (logging && logn < LOGMAX) {
        log_t[logn] = t;
        log_u[logn] = u;
        log_v[logn] = v;
        logn++;
    }
}

static void raw_del_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][--deg[u]];
            return;
        }
    }
}

static void raw_add(int u, int v) {
    am[u][v] = am[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void raw_rem(int u, int v) {
    am[u][v] = am[v][u] = 0;
    raw_del_one(u, v);
    raw_del_one(v, u);
}

static void add_edge(int u, int v) {
    raw_add(u, v);
    lg(0, u, v);
}

static void rem_edge(int u, int v) {
    raw_rem(u, v);
    lg(1, u, v);
}

static void new_vertex(int c) {
    int v = n;
    n++;
    deg[v] = 0;
    col[v] = c;
    lg(2, v, c);
}

static void undo_to(int pos) {
    logging = 0;
    while (logn > pos) {
        logn--;
        int t = log_t[logn], u = log_u[logn], v = log_v[logn];
        if (t == 0) raw_rem(u, v);
        else if (t == 1) raw_add(u, v);
        else n--;
    }
    logging = 1;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > Dg. */
static long long cost(void) {
    int w = (n + 63) >> 6;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < Dg; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt + (size_t)v * w;
            const uint64_t *c = cur + (size_t)v * w;
            memcpy(x, c, sizeof(uint64_t) * (size_t)w);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *y = cur + (size_t)nb[v][i] * w;
                for (int k = 0; k < w; k++) x[k] |= y[k];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        const uint64_t *c = cur + (size_t)v * w;
        for (int k = 0; k < w; k++) pc += popc(c[k]);
        bad += n - pc;
    }
    return bad / 2;
}

/* Add cross-side edges between deficient vertices. Only shortens distances. */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dg) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < dg; j++) {
            int b = R[j];
            if (deg[b] < dg && !am[a][b]) add_edge(a, b);
        }
    }
}

/* Add a vertex of colour c joined to up to dg vertices of the other colour. */
static int attach_vertex(int c) {
    int v = n;
    new_vertex(c);
    static int cand[MAXN], ordv[MAXN];
    int nc = 0, k = 0;
    for (int x = 0; x < v; x++)
        if (col[x] != c) cand[nc++] = x;
    shuffle(cand, nc);
    for (int i = 0; i < nc; i++)
        if (deg[cand[i]] < dg) ordv[k++] = cand[i];
    for (int i = 0; i < nc; i++)
        if (deg[cand[i]] >= dg) ordv[k++] = cand[i];
    int take = dg < k ? dg : k;
    for (int i = 0; i < take; i++) {
        int x = ordv[i];
        if (deg[x] >= dg) {
            int y = nb[x][rint_(deg[x])];
            rem_edge(x, y);
        }
        add_edge(x, v);
    }
    return v;
}

static int pick_side(int c) {
    for (int t = 0; t < 100; t++) {
        int x = rint_(n);
        if (col[x] == c && deg[x] > 0) return x;
    }
    return -1;
}

/* Degree-preserving double-edge switch between two colour-0 vertices. */
static int try_switch(void) {
    int a = pick_side(0), c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = nb[a][rint_(deg[a])];
    int e = nb[c][rint_(deg[c])];
    if (b == e || am[a][e] || am[c][b]) return 0;
    rem_edge(a, b);
    rem_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    return 1;
}

static long long anneal(int iters) {
    long long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if (logn > LOGMAX - 4096) break;
        if ((it & 31) == 0 && timeup()) break;
        int p = logn;
        if (!try_switch()) continue;
        long long nc = cost();
        if (nc <= cur || (nc - cur <= 2 && rdouble() < 0.05)) cur = nc;
        else undo_to(p);
    }
    return cur;
}

/* One attempt: add a vertex, repair by switches. Commit only if valid. */
static int attempt(int iters) {
    logn = 0;
    int c = rint_(2);
    attach_vertex(c);
    fill();
    long long r = anneal(iters);
    if (r == 0) {
        fill();
        logn = 0;
        return 1;
    }
    undo_to(0);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dg = atoi(argv[1]);
    Dg = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    limit_s = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t0 = clock();

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (dg < 1 || dg > MAXD || Dg < 2 || N0 < 0 || M0 < 0 || N0 > MAXN - 200) {
        printf("0 0\n");
        return 0;
    }
    n = N0;
    if (N0 == 0) {
        n = 2 * dg;
        for (int i = 0; i < dg; i++)
            for (int j = 0; j < dg; j++) raw_add(i, dg + j);
    } else {
        for (int i = 0; i < M0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                printf("0 0\n");
                return 0;
            }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || am[u][v] ||
                deg[u] >= dg || deg[v] >= dg) {
                printf("0 0\n");
                return 0;
            }
            raw_add(u, v);
        }
    }

    for (int v = 0; v < n; v++) col[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int x = stk[--sp];
            for (int i = 0; i < deg[x]; i++) {
                int y = nb[x][i];
                if (col[y] < 0) {
                    col[y] = 1 - col[x];
                    stk[sp++] = y;
                } else if (col[y] == col[x]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    while (!timeup()) {
        if (n + 2 >= MAXN) break;
        attempt(3000);
    }

    int m = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) m++;
    printf("%d %d\n", n, m);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) printf("%d %d\n", u, nb[u][i]);
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 steps."""
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
    """Greedily join deficient opposite-side vertices in random order (only shortens distances)."""
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


# ----------------------------------------------------------------------------
# Native search: vertex addition plus degree-preserving switch annealing (C).
# ----------------------------------------------------------------------------

def _c_improve(n, edges, d, D, seconds, seed):
    """Run the C engine from a valid start graph. Returns (n, edges) if larger and valid, else None."""
    if seconds < 1.0 or n > 2000:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{seconds:.2f}"],
                        stdin_graph=(n, edges), timeout=seconds + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return None
    if n2 > n and lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, which is Moore-optimal for D = 2.
    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback
    if D < 3:
        return best_n, list(best_e)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: W(q) for D >= 4 (degree q+1), otherwise PG(2,q).
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, start + 0.25 * time_limit, rng)
        consider(n1, e1)
        n2, e2 = _duplicate_twins(n1, e1, d, rng)
        e2 = _saturate_edges(n2, e2, d, rng)
        consider(n2, e2)

    # Native annealing search from the best valid graph found so far.
    elapsed = time.monotonic() - start
    c_budget = 0.80 * time_limit - elapsed - 3.0
    if c_budget >= 2.0:
        res = _c_improve(best_n, best_e, d, D, c_budget, seed)
        if res is not None:
            consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback[0], list(fallback[1])
    return best_n, list(best_e)
