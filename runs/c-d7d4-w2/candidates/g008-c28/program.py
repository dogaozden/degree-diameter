import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200112L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXW (MAXN / 64)

static int N, DG, DIAM;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static int col[MAXN];
static uint64_t X[2][MAXN][MAXW];
static uint64_t rs = 1;

static int sN;
static int sdeg[MAXN], scol[MAXN], snb[MAXN][MAXD];
static int bN;
static int bdeg[MAXN], bnb[MAXN][MAXD];
static int side0[MAXN];
static int isch[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int ri(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (nb[a][i] == b) return 1;
    return 0;
}
static void half_del(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
    }
}
static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}
static void del_edge(int a, int b) {
    half_del(a, b);
    half_del(b, a);
}

/* Fill X with radius-R balls; returns index of the buffer holding them. */
static int balls(int R) {
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(X[0][v], 0, sizeof(uint64_t) * W);
        X[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        int s = r & 1, t = s ^ 1;
        for (int v = 0; v < N; v++) {
            uint64_t *o = X[t][v];
            memcpy(o, X[s][v], sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *x = X[s][nb[v][i]];
                for (int w = 0; w < W; w++) o[w] |= x[w];
            }
        }
    }
    return R & 1;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). 0 means valid diameter. */
static int cost(void) {
    int idx = balls(DIAM);
    int W = (N + 63) / 64;
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(X[idx][v][w]);
        bad += N - c;
    }
    return (int)(bad / 2);
}

static void save_state(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof(int) * N);
    memcpy(scol, col, sizeof(int) * N);
    memcpy(snb, nb, sizeof(int) * MAXD * N);
}
static void restore_state(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof(int) * N);
    memcpy(col, scol, sizeof(int) * N);
    memcpy(nb, snb, sizeof(int) * MAXD * N);
}
static void save_best(void) {
    bN = N;
    memcpy(bdeg, deg, sizeof(int) * N);
    memcpy(bnb, nb, sizeof(int) * MAXD * N);
}

/* Bipartite double-edge switches (degrees kept) minimising the cost. Returns final cost. */
static int anneal(int iters, double deadline) {
    int ns = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) side0[ns++] = v;
    int cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        int a = side0[ri(ns)];
        if (deg[a] == 0) continue;
        int b = nb[a][ri(deg[a])];
        int c = side0[ri(ns)];
        if (c == a || deg[c] == 0) continue;
        int e = nb[c][ri(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        int nc = cost();
        if (nc <= cur || (nc == cur + 1 && ri(10) == 0)) {
            cur = nc;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur;
}

/* Join deficient opposite-side non-adjacent pairs (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= DG) continue;
        if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
    }
    for (int i = nl - 1; i > 0; i--) { int j = ri(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t; }
    for (int i = nr - 1; i > 0; i--) { int j = ri(i + 1); int t = R[i]; R[i] = R[j]; R[j] = t; }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < DG; j++) {
            int b = R[j];
            if (deg[b] >= DG || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/* Random switches that keep the graph valid (plateau moves). */
static void plateau(int steps) {
    int ns = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) side0[ns++] = v;
    for (int it = 0; it < steps; it++) {
        int a = side0[ri(ns)];
        if (deg[a] == 0) continue;
        int b = nb[a][ri(deg[a])];
        int c = side0[ri(ns)];
        if (c == a || deg[c] == 0) continue;
        int e = nb[c][ri(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        if (cost() != 0) {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
}

/* Try to add one vertex attached to a greedy cover, repair with switches. Keeps validity. */
static int try_grow(double deadline) {
    if (N + 1 >= MAXN) return 0;
    int s = ri(2);
    int idx = balls(DIAM - 1);
    int W = (N + 63) / 64;
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD], nch = 0;
    for (nch = 0; nch < DG; nch++) {
        int bs = -1;
        long long best = -1;
        for (int u = 0; u < N; u++) {
            if (col[u] != s || isch[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(X[idx][u][w] & ~cov[w]);
            if (g == 0) continue;
            long long sc = (long long)g * 4096 + ri(4096);
            if (sc > best) { best = sc; bs = u; }
        }
        if (bs < 0) break;
        isch[bs] = 1;
        chosen[nch] = bs;
        for (int w = 0; w < W; w++) cov[w] |= X[idx][bs][w];
    }
    int ok = 0;
    if (nch > 0) {
        save_state();
        int v = N++;
        col[v] = 1 - s;
        deg[v] = 0;
        for (int i = 0; i < nch; i++) {
            int u = chosen[i];
            if (deg[u] >= DG) {
                int t = nb[u][ri(deg[u])];
                del_edge(u, t);
            }
            add_edge(u, v);
        }
        fill();
        if (anneal(800, deadline) == 0) ok = 1;
        else restore_state();
    }
    for (int i = 0; i < nch; i++) isch[chosen[i]] = 0;
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double T = atof(argv[4]);
    double deadline = now() + T;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0 ||
        DG < 1 || DG > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
            has_edge(u, v) || deg[u] >= DG || deg[v] >= DG) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject odd cycles. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[u][i];
                if (col[w] == -1) { col[w] = 1 - col[u]; q[t++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    if (anneal(20000, deadline) != 0) { printf("0 0\n"); return 0; }
    save_best();

    while (now() < deadline) {
        plateau(20);
        try_grow(deadline);
        if (N > bN) save_best();
    }

    int me = 0;
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < bdeg[v]; i++) if (bnb[v][i] > v) me++;
    printf("%d %d\n", bN, me);
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < bdeg[v]; i++)
            if (bnb[v][i] > v) printf("%d %d\n", v, bnb[v][i]);
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
    """Incidence graph of points and lines of the generalized quadrangle W(q): order 2(q+1)(q^2+1), diameter 4."""
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
    """W(q) for the largest prime power q <= 16 with q + 1 <= d, or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=30):
    """Add vertices whose neighbourhoods cover all vertices from the deficient side."""
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
    """Join deficient opposite-side vertices in random order (keeps bipartite and degree bound)."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Cover-vertex growth alternated with saturation. Each step keeps the diameter bound."""
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
    """On a point-line base, add cross edges between non-incident points and lines (only shortens distances)."""
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
    """Randomized twin / growth / saturation pipeline."""
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
# Bi-Cayley graphs over Z_m x|_r Z_k: a_g ~ b_{g*s}, s in S. The group acts
# transitively on each side, so checking BFS from a_e and b_e certifies the diameter.
# ----------------------------------------------------------------------------

def _groups_of_order(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_table(m, k, r):
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    table = [[0] * N for _ in range(N)]
    for x in range(N):
        a1, b1 = divmod(x, k)
        row = table[x]
        for y in range(N):
            c, d2 = divmod(y, k)
            row[y] = ((a1 + pw[b1] * c) % m) * k + (b1 + d2) % k
    return table


def _bicayley_adj(N, table, S):
    adj = [[] for _ in range(2 * N)]
    for g in range(N):
        row = table[g]
        for s in S:
            b = N + row[s]
            adj[g].append(b)
            adj[b].append(g)
    return adj


def _cayley_cost(adj, D):
    total = 0
    N2 = len(adj)
    N = N2 // 2
    for src in (0, N):
        dist = [-1] * N2
        dist[src] = 0
        frontier = [src]
        cnt = 1
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - cnt
    return total


def _climb(N, table, d, D, rng, iters, deadline):
    S = rng.sample(range(N), d)
    cur = _cayley_cost(_bicayley_adj(N, table, S), D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(N)
        if cand in S:
            continue
        newS = list(S)
        newS[i] = cand
        c2 = _cayley_cost(_bicayley_adj(N, table, newS), D)
        if c2 <= cur or (c2 == cur + 1 and rng.random() < 0.05):
            S, cur = newS, c2
    return S if cur == 0 else None


def _bicayley_search(d, D, rng, deadline, consider, lo_n):
    """Search bi-Cayley graphs of order 2N for N increasing past lo_n / 2."""
    lo = max(d, lo_n // 2 + 1)
    hi = lib.moore_bound(d, D) // 2
    N = lo
    while N <= hi and time.monotonic() < deadline:
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:3]:
            if time.monotonic() >= deadline:
                break
            table = _group_table(m, k, r)
            S = _climb(N, table, d, D, rng, 150, deadline)
            if S is not None:
                edges = [(g, N + table[g][s]) for g in range(N) for s in S]
                consider(2 * N, edges)
                break
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.88 * time_limit
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

    # Phase A: structured base (generalized quadrangle for D >= 4, projective plane for D = 3).
    base_is_gq = False
    base = None
    if D >= 4:
        base = _best_gq(d)
        base_is_gq = base is not None
    if base is None and D >= 3:
        base = _best_pg(d)

    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, t0 + 0.08 * time_limit, rng)
        consider(n1, e1)

    # Phase B: randomized twin / growth pipelines.
    trial_end = t0 + 0.16 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Phase C: spare-slot matching on the quadrangle base, sweeping kept free slots.
    if base_is_gq and time.monotonic() < end:
        spare_end = t0 + 0.22 * time_limit
        while time.monotonic() < spare_end:
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            gn, ge = _grow(sn, se, d, D, spare_end, rng)
            consider(gn, ge)

    # Phase D: bi-Cayley search over small groups.
    if d >= 2 and time.monotonic() < end:
        _bicayley_search(d, D, rng, t0 + 0.32 * time_limit, consider, best_n)

    # Phase E: C engine (plateau shuffling, add-vertex with cover, switch repair), from the best graph.
    rem = end - time.monotonic()
    if rem > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(rem * 0.9, 3)],
                             stdin_graph=(best_n, best_e), timeout=rem)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
