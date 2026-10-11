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

#define MAXN 2400
#define MAXW 38
#define MAXD 64
#define STALL 20000

typedef uint64_t u64;

static int N, DEG, DIAM;
static int adj[MAXN][MAXD];
static int dg[MAXN];
static int col[MAXN];
static u64 BALL[MAXN][MAXW];
static u64 CB[MAXN][MAXW];
static u64 TMP[MAXN][MAXW];
static int bestadj[MAXN][MAXD];
static int bestdg[MAXN];
static int bestN = -1;
static u64 rs = 1;
static int pa, pb, pc, pe;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < dg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}

static void rep(int v, int old, int nv) {
    for (int k = 0; k < dg[v]; k++) if (adj[v][k] == old) { adj[v][k] = nv; return; }
}

static void add_edge(int a, int b) {
    adj[a][dg[a]++] = b;
    adj[b][dg[b]++] = a;
}

static void shuffle_ints(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* out[v] = bitset of vertices within distance r of v. */
static void compute_balls(int r, u64 out[][MAXW]) {
    int nw = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(out[v], 0, sizeof(u64) * MAXW);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            memcpy(TMP[v], out[v], sizeof(u64) * nw);
            for (int k = 0; k < dg[v]; k++) {
                const u64 *src = out[adj[v][k]];
                for (int w = 0; w < nw; w++) TMP[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++) memcpy(out[v], TMP[v], sizeof(u64) * nw);
    }
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable counted). */
static long long full_cost(void) {
    int nw = (N + 63) / 64;
    compute_balls(DIAM, BALL);
    long long s = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(BALL[v][w]);
        s += N - c;
    }
    return s / 2;
}

/* Adding edges never increases cost, so join deficient opposite-side pairs. */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (dg[v] >= DEG) continue;
        if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
    }
    shuffle_ints(L, nl);
    shuffle_ints(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && dg[a] < DEG; j++) {
            int b = R[j];
            if (dg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void color_graph(void) {
    static int st[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        int sp = 0;
        col[s] = 0; st[sp++] = s;
        while (sp > 0) {
            int u = st[--sp];
            for (int k = 0; k < dg[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) { col[w] = 1 - col[u]; st[sp++] = w; }
            }
        }
    }
}

/* Degree-preserving bipartite double-edge switch proposal. */
static int propose(void) {
    for (int t = 0; t < 200; t++) {
        int a = rint(N);
        if (col[a] != 0 || dg[a] == 0) continue;
        int b = adj[a][rint(dg[a])];
        int c = rint(N);
        if (c == a || col[c] != 0 || dg[c] == 0) continue;
        int e = adj[c][rint(dg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        pa = a; pb = b; pc = c; pe = e;
        return 1;
    }
    return 0;
}

/* (a,b),(c,e) -> (a,e),(c,b). */
static void do_switch(int a, int b, int c, int e) {
    rep(a, b, e); rep(b, a, c); rep(c, e, b); rep(e, c, a);
}

static void undo_switch(int a, int b, int c, int e) {
    rep(a, e, b); rep(e, a, c); rep(c, b, e); rep(b, c, a);
}

static void kick(int k) {
    for (int i = 0; i < k; i++) if (propose()) do_switch(pa, pb, pc, pe);
}

/* Add one vertex whose neighbourhood covers all vertices within DIAM-1 steps. */
static int try_grow(void) {
    if (N >= MAXN - 1) return 0;
    int nw = (N + 63) / 64;
    compute_balls(DIAM - 1, CB);
    static int cand[MAXN], used[MAXN];
    int c0 = rint(2);
    for (int tt = 0; tt < 2; tt++) {
        int c = (tt == 0) ? c0 : 1 - c0;
        int nc = 0;
        for (int v = 0; v < N; v++) if (col[v] == c && dg[v] < DEG) cand[nc++] = v;
        if (nc == 0) continue;
        for (int att = 0; att < 40; att++) {
            if (att > 0) shuffle_ints(cand, nc);
            memset(used, 0, sizeof(int) * nc);
            u64 cov[MAXW];
            memset(cov, 0, sizeof(cov));
            int chosen[MAXD], k = 0, covered = 0;
            while (covered < N && k < DEG) {
                int bg = 0, bi = -1;
                for (int i = 0; i < nc; i++) {
                    if (used[i]) continue;
                    const u64 *bl = CB[cand[i]];
                    int g = 0;
                    for (int w = 0; w < nw; w++) g += popc(bl[w] & ~cov[w]);
                    if (g > bg) { bg = g; bi = i; }
                }
                if (bi < 0) break;
                used[bi] = 1;
                chosen[k++] = cand[bi];
                covered = 0;
                for (int w = 0; w < nw; w++) {
                    cov[w] |= CB[cand[bi]][w];
                    covered += popc(cov[w]);
                }
            }
            if (covered == N) {
                int v = N++;
                col[v] = 1 - c;
                dg[v] = 0;
                for (int i = 0; i < k; i++) add_edge(chosen[i], v);
                return 1;
            }
        }
    }
    return 0;
}

static void save_best(void) {
    bestN = N;
    memcpy(bestadj, adj, sizeof(adj));
    memcpy(bestdg, dg, sizeof(dg));
}

static void print_best(void) {
    long long cnt = 0;
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestdg[v]; k++) if (bestadj[v][k] > v) cnt++;
    printf("%d %lld\n", bestN, cnt);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestdg[v]; k++)
            if (bestadj[v][k] > v) printf("%d %d\n", v, bestadj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) return 1;
    DEG = d; DIAM = D;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    clock_t t0 = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n > MAXN - 400) { printf("0 0\n"); return 0; }
    N = n;
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    color_graph();
    fill_edges();
    long long cur = full_cost();
    if (cur == 0) save_best();

    double temp = 0.5;
    long long stall = 0, bestc = cur, it = 0;
    while (1) {
        if ((it & 31) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        it++;
        if (cur == 0) {
            if (N > bestN) save_best();
            if (try_grow()) {
                fill_edges();
                cur = full_cost();
            } else {
                kick(4);
                cur = full_cost();
                bestc = cur;
                stall = 0;
            }
            continue;
        }
        if (!propose()) continue;
        int a = pa, b = pb, c = pc, e = pe;
        do_switch(a, b, c, e);
        long long nc = full_cost();
        if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / temp)) cur = nc;
        else undo_switch(a, b, c, e);
        if (cur < bestc) { bestc = cur; stall = 0; }
        else if (++stall > STALL) {
            kick(6);
            cur = full_cost();
            bestc = cur;
            stall = 0;
        }
    }
    if (cur == 0 && N > bestN) save_best();
    if (bestN < 0) save_best();
    print_best();
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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
# Bipartite voltage lifts over small groups (Python, short slices).
# ----------------------------------------------------------------------------

def _group_options(G):
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline):
    darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    temp = 0.6
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return n, e


def _lift_phase(d, D, get_best, deadline, rng, consider):
    while time.monotonic() < deadline:
        best_n = get_best()
        s = rng.choice((1, 2, 2, 3, 3, 4))
        G = best_n // (2 * s) + 1 + rng.randrange(4)
        opts = _group_options(G)
        if not opts:
            continue
        M, k, r = rng.choice(opts)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res = _lift_search(d, D, s, G, mul, rng, slice_end)
        if res is not None:
            n, e = res
            consider(n, e)
            n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
            consider(n2, e2)


# ----------------------------------------------------------------------------
# Python pruning and regrowth (fallback when the C engine is unavailable).
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# C engine wrapper.
# ----------------------------------------------------------------------------

def _engine(d, D, seed, graph, secs, timeout_left):
    """Run the C annealer from `graph`. Returns (n, edges) or None on any failure."""
    n, e = graph
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.2f}"], stdin_graph=(n, e),
                        timeout=max(2.0, timeout_left))
        return lib.parse_graph_text(out)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Driver. Fractions of time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, twin/grow trials
#   L  short voltage-lift slice over small groups
#   C  C annealer with switch moves, fill and cover-growth, from the best graph
#   D  Python prune-regrow on whatever remains (cheap fallback)
# Every kept graph passes lib.is_valid; the Haar graph is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def at(f):
        return start + f * time_limit

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

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best_n, list(best_e)

    # Phase A: structured base, grown; then trials.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            if best_n < moore:
                n1, e1 = _grow(n0, e0, d, D, at(0.07), rng)
                consider(n1, e1)
    if best_n >= moore:
        return best_n, list(best_e)
    trial_end = at(0.12)
    while time.monotonic() < trial_end and best_n < moore:
        n, e = _trial(best_n, best_e, d, D, rng, trial_end)
        consider(n, e)
    if best_n >= moore:
        return best_n, list(best_e)

    # Phase L: short voltage-lift slice.
    if time.monotonic() < at(0.22) and best_n < moore:
        _lift_phase(d, D, lambda: best_n, at(0.22), rng, consider)
    if best_n >= moore:
        return best_n, list(best_e)

    # Phase C: C annealer from the best graph found so far.
    if best_n < moore:
        secs = at(0.86) - time.monotonic() - 0.5
        if secs > 1.0:
            res = _engine(d, D, seed, (best_n, best_e), secs, at(0.92) - time.monotonic())
            if res is not None:
                consider(*res)

    # Phase D: Python prune-regrow on the remaining budget.
    if time.monotonic() < at(0.93) and best_n < moore:
        _prune_regrow(best_n, best_e, d, D, at(0.93), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
