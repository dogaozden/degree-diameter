import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grow by one vertex (cover of the opposite side), fill spare
# degree, repair the diameter with bipartite double-edge switches (degrees kept),
# and roll back when repair fails. Every accepted state is valid by construction.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 64
#define MAXW 18
#define MAXE (MAXN * MAXD / 2 + 64)
#define ANN_ITERS 3000
#define ANN_TEMP 0.35

static int d_ = 3, D_ = 3;
static int N = 0;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static int side[MAXN];
static uint64_t BUF1[MAXN][MAXW];
static uint64_t BUF2[MAXN][MAXW];
static uint64_t (*CUR)[MAXW] = BUF1;
static uint64_t rs = 88172645463325252ULL;
static double t_end = 0.0;
static int S0[MAXN];
static char picked[MAXN];
static int eu[MAXE], ev[MAXE];
static int bu[MAXE], bv[MAXE];
static int su[MAXE], sv[MAXE];

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int a, int b) {
    A[a][b] = 1; A[b][a] = 1;
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void rem1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
    }
}

static void del_e(int a, int b) {
    A[a][b] = 0; A[b][a] = 0;
    rem1(a, b);
    rem1(b, a);
}

static void clear_edges(void) {
    for (int v = 0; v < N; v++) {
        for (int j = 0; j < deg[v]; j++) A[v][adj[v][j]] = 0;
        deg[v] = 0;
    }
}

static int dump(int *xu, int *xv) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int j = 0; j < deg[v]; j++) {
            int u = adj[v][j];
            if (v < u) {
                xu[m] = v;
                xv[m] = u;
                m++;
            }
        }
    }
    return m;
}

static void restore(int sn, int sm) {
    clear_edges();
    N = sn;
    for (int i = 0; i < sm; i++) add_e(su[i], sv[i]);
}

static void compute_balls(int r) {
    int w = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = BUF1;
    uint64_t (*nxt)[MAXW] = BUF2;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < w; i++) cur[v][i] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            for (int i = 0; i < w; i++) nxt[v][i] = cur[v][i];
            for (int j = 0; j < deg[v]; j++) {
                int u = adj[v][j];
                for (int i = 0; i < w; i++) nxt[v][i] |= cur[u][i];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    CUR = cur;
}

static long long cost_full(void) {
    compute_balls(D_);
    int w = (N + 63) >> 6;
    long long s = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < w; i++) c += pc64(CUR[v][i]);
        s += N - c;
    }
    return s / 2;
}

static long long anneal(int iters, double T) {
    int ns = 0;
    for (int v = 0; v < N; v++) if (side[v] == 0) S0[ns++] = v;
    if (ns == 0) return 1;
    long long cur = cost_full();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now_s() > t_end) break;
        int a = S0[rndint(ns)];
        if (deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int c = S0[rndint(ns)];
        if (c == a || deg[c] == 0) continue;
        int e = adj[c][rndint(deg[c])];
        if (A[a][e] || A[c][b]) continue;
        del_e(a, b); del_e(c, e);
        add_e(a, e); add_e(c, b);
        long long nw = cost_full();
        long long dl = nw - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cur = nw;
        } else {
            del_e(a, e); del_e(c, b);
            add_e(a, b); add_e(c, e);
        }
    }
    return cur;
}

static int grow_once(void) {
    if (N + 1 >= MAXN - 1) return 0;
    int c = rndint(2);
    int t = 1 - c;
    compute_balls(D_ - 1);
    int w = (N + 63) >> 6;
    uint64_t cov[MAXW];
    for (int i = 0; i < MAXW; i++) cov[i] = 0;
    for (int v = 0; v < N; v++) picked[v] = 0;
    int chosen[MAXD];
    int nch = 0;
    for (int k = 0; k < d_ && nch < d_; k++) {
        int best = -1;
        long long bk = -1;
        for (int s = 0; s < N; s++) {
            if (side[s] != t || picked[s]) continue;
            int g = 0;
            for (int i = 0; i < w; i++) g += pc64(CUR[s][i] & ~cov[i]);
            if (g == 0) continue;
            long long key = (long long)g * 1024 + rndint(1024);
            if (key > bk) { bk = key; best = s; }
        }
        if (best < 0) break;
        picked[best] = 1;
        chosen[nch++] = best;
        for (int i = 0; i < w; i++) cov[i] |= CUR[best][i];
    }
    int wv = N;
    side[wv] = c;
    deg[wv] = 0;
    N++;
    for (int k = 0; k < nch; k++) {
        int s = chosen[k];
        if (deg[s] >= d_) {
            int x = adj[s][rndint(deg[s])];
            del_e(s, x);
        }
        add_e(s, wv);
    }
    return 1;
}

static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d_) {
            if (side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = R[i]; R[i] = R[j]; R[j] = tmp;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = L[i]; L[i] = L[j]; L[j] = tmp;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] < d_ && !A[a][b]) add_e(a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    t_end = now_s() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int ok = (n >= 1 && n < MAXN - 2 && d_ >= 1 && d_ < MAXD && m >= 0 && m <= MAXE);
    int cnt = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (ok) { eu[cnt] = u; ev[cnt] = v; cnt++; }
    }

    if (ok) {
        N = n;
        for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = 0; }
        for (int i = 0; i < cnt && ok; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || u >= n || v < 0 || v >= n || u == v || A[u][v] ||
                deg[u] >= d_ || deg[v] >= d_) {
                ok = 0;
            } else {
                add_e(u, v);
            }
        }
    }

    if (ok) {
        for (int v = 0; v < N; v++) side[v] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            S0[qt++] = s;
            while (qh < qt && ok) {
                int x = S0[qh++];
                for (int j = 0; j < deg[x]; j++) {
                    int y = adj[x][j];
                    if (side[y] == -1) {
                        side[y] = 1 - side[x];
                        S0[qt++] = y;
                    } else if (side[y] == side[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }

    int bestN = 0, bm = 0;
    if (ok && D_ >= 2 && cost_full() != 0) ok = 0;
    if (ok) {
        bestN = N;
        bm = dump(bu, bv);
        if (D_ >= 2) {
            while (now_s() < t_end && N < MAXN - 2) {
                int sn = N;
                int sm = dump(su, sv);
                if (!grow_once()) break;
                fill();
                long long cc = anneal(ANN_ITERS, ANN_TEMP);
                if (cc == 0) {
                    if (N > bestN) {
                        bestN = N;
                        bm = dump(bu, bv);
                    }
                } else {
                    restore(sn, sm);
                }
            }
        }
    }

    if (!ok || bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
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
    """Generalized quadrangle incidence graph W(q), largest prime power q <= min(d - 1, 9)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
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
# Python fallback search (used only if the C engine fails): kill, repair, regrow.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
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
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
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
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
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
        if not _anneal(adj, color, d, D, rng, 150, deadline):
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
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

    # Structured bases: generalized quadrangle for D >= 4, projective plane for D = 3.
    try:
        base_n, base_e = best_n, list(best_e)
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
                base_n, base_e = best_n, list(best_e)

        # Short randomized twin-duplication phase for a richer start.
        if D >= 2:
            trial_end = start + 0.22 * time_limit
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)
    except Exception:
        pass

    # Main stage: C engine grows and repairs from the best graph so far.
    c_ok = False
    if D >= 2 and d <= 60:
        try:
            rem = deadline - time.monotonic() - 3.0
            if rem > 2.0:
                start_n, start_e = best_n, list(best_e)
                out = lib.run_c(C_SOURCE, [d, D, seed, round(rem, 2)],
                                stdin_graph=(start_n, start_e), timeout=rem + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
                c_ok = True
        except Exception:
            c_ok = False

    # Python fallback if the C engine could not run.
    if not c_ok and D >= 2:
        try:
            if time.monotonic() < deadline:
                _lns(best_n, best_e, d, D, deadline, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
