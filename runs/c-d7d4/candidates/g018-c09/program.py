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

#define MAXV 2048
#define WMAX 32
#define MAXDEG 64
#define MAXE (MAXV * MAXDEG / 2)
#define ANNEAL_ITERS 1200

static int N = 0, DEG = 3, DIAM = 2;
static int deg_[MAXV];
static int nb[MAXV][MAXDEG];
static unsigned char A[MAXV][MAXV];
static int col[MAXV];
static uint64_t ballA[MAXV][WMAX];
static uint64_t ballT[MAXV][WMAX];
static uint64_t rs = 88172645463325252ULL;
static double budget = 1.0;

static int EU[MAXE], EV[MAXE];
static int SU[MAXE], SV[MAXE], sm = 0, sn = 0;
static int BU[MAXE], BV[MAXE], bm = 0, bn = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void add_edge(int u, int v) {
    A[u][v] = 1; A[v][u] = 1;
    nb[u][deg_[u]++] = v;
    nb[v][deg_[v]++] = u;
}

static void rm_nb(int u, int v) {
    for (int i = 0; i < deg_[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg_[u]]; return; }
    }
}

static void del_edge(int u, int v) {
    A[u][v] = 0; A[v][u] = 0;
    rm_nb(u, v); rm_nb(v, u);
}

static int extract(int *U, int *V) {
    int m = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg_[v]; i++)
            if (v < nb[v][i]) { U[m] = v; V[m] = nb[v][i]; m++; }
    return m;
}

static void color_all(void) {
    static int q[MAXV];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int h = 0, t = 0;
        col[s] = 0; q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg_[u]; i++) {
                int w = nb[u][i];
                if (col[w] < 0) { col[w] = 1 - col[u]; q[t++] = w; }
            }
        }
    }
}

static void load(int n, int m, const int *U, const int *V) {
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg_[v]; i++) A[v][nb[v][i]] = 0;
    N = n;
    for (int v = 0; v < N; v++) deg_[v] = 0;
    for (int i = 0; i < m; i++) add_edge(U[i], V[i]);
    color_all();
}

static void balls(int r, uint64_t out[][WMAX]) {
    int wd = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        memset(out[v], 0, sizeof(uint64_t) * WMAX);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            memcpy(ballT[v], out[v], sizeof(uint64_t) * wd);
            for (int i = 0; i < deg_[v]; i++) {
                const uint64_t *src = out[nb[v][i]];
                for (int w = 0; w < wd; w++) ballT[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++)
            memcpy(out[v], ballT[v], sizeof(uint64_t) * wd);
    }
}

static long cost(void) {
    balls(DIAM, ballA);
    int wd = (N + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < wd; w++) c += pc(ballA[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void fill(void) {
    static int L0[MAXV], L1[MAXV];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg_[v] < DEG) {
            if (col[v] == 0) L0[n0++] = v; else L1[n1++] = v;
        }
    }
    shuffle(L0, n0);
    shuffle(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        if (deg_[a] >= DEG) continue;
        for (int j = 0; j < n1; j++) {
            int b = L1[j];
            if (deg_[b] < DEG && !A[a][b]) {
                add_edge(a, b);
                if (deg_[a] >= DEG) break;
            }
        }
    }
}

static void add_vertex(int side) {
    if (N + 2 >= MAXV) return;
    int v = N;
    balls(DIAM - 1, ballA);
    N++;
    deg_[v] = 0;
    col[v] = side;
    int wd = (N + 63) >> 6;
    static uint64_t cov[WMAX];
    static int used[MAXV];
    memset(cov, 0, sizeof cov);
    memset(used, 0, sizeof used);
    int oc = 1 - side;
    int chosen[MAXDEG], nc = 0;
    for (int k = 0; k < DEG; k++) {
        int best = -1;
        long bs = -1;
        for (int s = 0; s < v; s++) {
            if (col[s] != oc || used[s]) continue;
            long g = 0;
            for (int w = 0; w < wd; w++) g += pc(ballA[s][w] & ~cov[w]);
            long sc = g * 1024 + rndint(1024);
            if (sc > bs) { bs = sc; best = s; }
        }
        if (best < 0 || bs < 1024) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < wd; w++) cov[w] |= ballA[best][w];
    }
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (deg_[s] >= DEG) {
            int t = nb[s][rndint(deg_[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
}

static long anneal(int iters) {
    static int side0[MAXV];
    int ns0 = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) side0[ns0++] = v;
    long cur = cost();
    for (int it = 0; it < iters && cur > 0 && ns0 > 1; it++) {
        if ((it & 31) == 0 && now() > budget) break;
        int a = side0[rndint(ns0)];
        int c = side0[rndint(ns0)];
        if (a == c || deg_[a] == 0 || deg_[c] == 0) continue;
        int b = nb[a][rndint(deg_[a])];
        int e = nb[c][rndint(deg_[c])];
        if (A[a][e] || A[c][b]) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndint(10) == 0)) {
            cur = nw;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur;
}

static void kill_random(int k) {
    static int mark[MAXV];
    static int map[MAXV];
    static int U2[MAXE], V2[MAXE];
    memset(mark, 0, sizeof mark);
    for (int i = 0; i < k; i++) {
        int v;
        do { v = rndint(N); } while (mark[v]);
        mark[v] = 1;
    }
    int nn = 0;
    for (int v = 0; v < N; v++) map[v] = mark[v] ? -1 : nn++;
    int m = extract(EU, EV);
    int m2 = 0;
    for (int i = 0; i < m; i++) {
        int a = map[EU[i]], b = map[EV[i]];
        if (a >= 0 && b >= 0) { U2[m2] = a; V2[m2] = b; m2++; }
    }
    load(nn, m2, U2, V2);
}

static void snapshot(void) { sn = N; sm = extract(SU, SV); }
static void restore(void) { load(sn, sm, SU, SV); }
static void save_best(void) { bn = N; bm = extract(BU, BV); }

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n >= MAXV - 64 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    static int IU[MAXE], IV[MAXE];
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &IU[i], &IV[i]) != 2) { printf("0 0\n"); return 0; }
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u = IU[i], v = IV[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v] ||
            deg_[u] >= DEG || deg_[v] >= DEG) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    color_all();
    save_best();

    double bound = 0, pw = 1;
    for (int i = 0; i < DIAM; i++) { bound += pw; pw *= (DEG - 1); }
    bound *= 2;

    while (now() < budget) {
        snapshot();
        if (rndint(10) < 7 && (double)(N + 1) <= bound && N + 2 < MAXV) {
            add_vertex(rndint(2));
        } else {
            int k = 1 + rndint(3);
            if (k + 4 < N) kill_random(k);
        }
        fill();
        long c = anneal(ANNEAL_ITERS);
        if (c == 0) {
            if (N > bn) save_best();
            if (N < bn - 2) load(bn, bm, BU, BV);
        } else {
            restore();
        }
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", BU[i], BV[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q). Order 2(q+1)(q^2+1)."""
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


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d (to be thinned)."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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
    """Greedily add vertices whose neighbourhoods cover all vertices at distance <= D-1."""
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
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
# Thinning a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) or PG(2,q)) grown, twin trials
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  C engine: add-vertex / kill-and-repair with annealed double-edge switches,
#      started from the best Python graph; it only keeps zero-bad-pair graphs.
# Every candidate passes lib.is_valid before it is kept. Fallback is K_{d,d}.
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

    def at(f):
        return start + f * time_limit

    # Phase A: structured base, grown, then twin/cover trials.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            consider(*_grow(n0, e0, d, D, at(0.08), rng))
    if D >= 2:
        trial_end = at(0.14)
        while time.monotonic() < trial_end:
            consider(*_trial(base_n, base_e, d, D, rng, trial_end))

    # Phase B: thinned dense structured graph.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.22):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re_ = raw
            end = at(0.22)
            while time.monotonic() < end:
                r = _deletion_trial(d, D, rn, re_, rng, end)
                if r is None:
                    break
                consider(*r)

    # Phase C: C engine from the best graph so far.
    if D >= 2 and d <= 60 and best_n < 2000 and best_n < lib.moore_bound(d, D):
        secs = at(0.93) - time.monotonic() - 1.5
        if secs > 2.0:
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, int(seed) & 0x7FFFFFFF, round(secs, 2)],
                    stdin_graph=(best_n, best_e),
                    timeout=max(1.0, at(0.98) - time.monotonic()),
                )
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
