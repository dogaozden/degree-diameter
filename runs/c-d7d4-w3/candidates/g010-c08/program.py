import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealing on bipartite graphs with a fixed degree cap.
# Moves keep the graph bipartite and degrees <= d. Vertices are added when the
# cost (number of pairs at distance > D) reaches zero. The best valid graph is
# printed before the time budget ends.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 64
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2)

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (u64)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int Dg, Dia, N, W;
static int col[MAXN], deg[MAXN], adj[MAXN][MAXDEG];
static u64 BA[MAXN][MAXW], BB[MAXN][MAXW];
static int bestN = 0, bestM = 0, bestCol[MAXN];
static int bu[MAXE], bv[MAXE];

static void set_N(int k) { N = k; W = (N + 63) / 64; }

static int pc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long cost_fn(void) {
    int n = N, w = W, v, r, i, k;
    u64 (*cur)[MAXW] = BA, (*nxt)[MAXW] = BB;
    for (v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(u64) * (size_t)w);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < Dia; r++) {
        for (v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(u64) * (size_t)w);
            for (i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (k = 0; k < w; k++) nxt[v][k] |= cur[u][k];
            }
        }
        u64 (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        for (k = 0; k < w; k++) c += pc(cur[v][k]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}

static void rm1(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

static void add_e(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_e(int a, int b) {
    rm1(a, b);
    rm1(b, a);
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    if (T <= 0) return 0;
    return rndu() < exp(-(double)delta / T);
}

static long long move_add(long long cur, double T) {
    int tries, a = -1, b = -1;
    for (tries = 0; tries < 60; tries++) {
        int x = rndi(N), y = rndi(N);
        if (col[x] == col[y] || deg[x] >= Dg || deg[y] >= Dg || has_edge(x, y)) continue;
        a = x;
        b = y;
        break;
    }
    if (a < 0) return cur;
    add_e(a, b);
    long long nc = cost_fn();
    if (accept(nc - cur, T)) return nc;
    del_e(a, b);
    return cur;
}

static long long move_swap(long long cur, double T) {
    int x, y, z, w, a, b, c, e;
    x = rndi(N);
    if (!deg[x]) return cur;
    y = adj[x][rndi(deg[x])];
    a = (col[x] == 0) ? x : y;
    b = (a == x) ? y : x;
    z = rndi(N);
    if (!deg[z]) return cur;
    w = adj[z][rndi(deg[z])];
    c = (col[z] == 0) ? z : w;
    e = (c == z) ? w : z;
    if (c == a || e == b) return cur;
    if (has_edge(a, e) || has_edge(c, b)) return cur;
    del_e(a, b);
    del_e(c, e);
    add_e(a, e);
    add_e(c, b);
    long long nc = cost_fn();
    if (accept(nc - cur, T)) return nc;
    del_e(a, e);
    del_e(c, b);
    add_e(a, b);
    add_e(c, e);
    return cur;
}

static void grow_vertex(void) {
    int v = N, c, got = 0, tries = 0, x, y;
    set_N(N + 1);
    col[v] = rndi(2);
    deg[v] = 0;
    c = col[v];
    while (got < Dg && tries < 20000) {
        tries++;
        x = rndi(v);
        if (col[x] == c || has_edge(v, x)) continue;
        if (deg[x] >= Dg) {
            if (!deg[x]) continue;
            y = adj[x][rndi(deg[x])];
            del_e(x, y);
        }
        add_e(v, x);
        got++;
    }
}

static void save_best(void) {
    int i, v, m = 0;
    bestN = N;
    for (v = 0; v < N; v++) {
        bestCol[v] = col[v];
        for (i = 0; i < deg[v]; i++) {
            if (adj[v][i] > v && m < MAXE) {
                bu[m] = v;
                bv[m] = adj[v][i];
                m++;
            }
        }
    }
    bestM = m;
}

static void restore_best(void) {
    int v, i;
    set_N(bestN);
    for (v = 0; v < N; v++) {
        deg[v] = 0;
        col[v] = bestCol[v];
    }
    for (i = 0; i < bestM; i++) add_e(bu[i], bv[i]);
}

int main(int argc, char **argv) {
    int n = 0, m = 0, i, v;
    if (argc < 5) return 1;
    Dg = atoi(argv[1]);
    Dia = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    long budget = atol(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    for (i = 0; i < 20; i++) rnd();
    time_t t0 = time(NULL);

    if (Dg < 1 || Dg > MAXDEG) { printf("0 0\n"); return 0; }
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN || m < 0 || m > MAXE) { printf("0 0\n"); return 0; }
    set_N(n);
    for (v = 0; v < N; v++) deg[v] = 0;
    for (i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) { printf("0 0\n"); return 0; }
        if (a < 0 || a >= N || b < 0 || b >= N || a == b || deg[a] >= Dg || deg[b] >= Dg) {
            printf("0 0\n");
            return 0;
        }
        adj[a][deg[a]++] = b;
        adj[b][deg[b]++] = a;
    }
    {
        int q[MAXN], qh = 0, qt = 0, ok = 1;
        for (v = 0; v < N; v++) col[v] = -1;
        for (v = 0; v < N && ok; v++) {
            if (col[v] != -1) continue;
            col[v] = 0;
            q[qt++] = v;
            while (qh < qt && ok) {
                int x = q[qh++];
                for (i = 0; i < deg[x]; i++) {
                    int y = adj[x][i];
                    if (col[y] == -1) {
                        col[y] = 1 - col[x];
                        q[qt++] = y;
                    } else if (col[y] == col[x]) {
                        ok = 0;
                    }
                }
            }
        }
        if (!ok) { printf("0 0\n"); return 0; }
    }

    long long cur = cost_fn();
    if (cur != 0) { printf("0 0\n"); return 0; }
    save_best();

    grow_vertex();
    cur = cost_fn();
    long long phaseMin = cur;
    long long since = 0;
    const long long STALL = 60000;
    double T = 0.6;
    long long it = 0;

    while (1) {
        if (cur == 0) {
            if (N > bestN) save_best();
            if (N >= MAXN - 1) break;
            grow_vertex();
            cur = cost_fn();
            phaseMin = cur;
            since = 0;
            T = 0.6;
            continue;
        }
        if ((it & 127) == 0 && (long)(time(NULL) - t0) >= budget) break;
        it++;
        double r = rndu();
        if (r < 0.3) cur = move_add(cur, T);
        else cur = move_swap(cur, T);
        T *= 0.99998;
        if (T < 0.08) T = 0.08;
        if (cur < phaseMin) {
            phaseMin = cur;
            since = 0;
        } else if (++since > STALL) {
            restore_best();
            grow_vertex();
            cur = cost_fn();
            phaseMin = cur;
            since = 0;
            T = 0.4;
        }
    }
    if (cur == 0 && N > bestN) save_best();

    printf("%d %d\n", bestN, bestM);
    for (i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for the structured phase.
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
# Driver. Structured start (about 15% of time), then the C annealing engine
# runs from the best valid graph for most of the rest. Every kept graph passes
# lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    rng = random.Random(seed)

    # Phase A: structured base, grown, then twin/grow trials.
    tA = start + 0.15 * time_limit
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, tA, rng)
        consider(n1, e1)
    if D >= 2:
        while time.monotonic() < tA:
            n, e = _trial(best_n, best_e, d, D, rng, tA)
            consider(n, e)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: C annealing engine from the best valid graph.
    if 2 <= d <= 64 and D >= 2:
        t_end = start + 0.82 * time_limit
        budget = int(t_end - time.monotonic() - 2.0)
        if budget >= 2:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, budget],
                                stdin_graph=(best_n, best_e), timeout=budget + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
