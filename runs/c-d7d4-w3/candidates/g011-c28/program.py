import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: fixed-vertex-set annealing with bitset diameter cost, plus
# one-vertex growth with cover-greedy attachment and snapshot restarts.
# Moves: add an edge between spare-degree opposite vertices, slide an edge
# endpoint onto a spare vertex, or a degree-preserving bipartite switch.
# Cost = number of vertex pairs at distance > D. Output: largest valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define MAXD 64
#define NMAX 1080
#define LOGCAP 16
#define STALL 30000
#define T0 0.6
#define TMIN 0.05
#define DECAY 0.99995

static int N, D, DEG;
static int dg[MAXN];
static int nb[MAXN][MAXD];
static int col[MAXN];
static uint64_t A[MAXN][MAXW];
static uint64_t BUF[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static uint64_t cover[MAXW];
static char used[MAXN];
static int spare_list[MAXN];
static int nsp;

static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t t0;
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) { return (int)((A[a][b >> 6] >> (b & 63)) & 1ULL); }

static void raw_add(int a, int b) {
    A[a][b >> 6] |= 1ULL << (b & 63);
    A[b][a >> 6] |= 1ULL << (a & 63);
    nb[a][dg[a]++] = b;
    nb[b][dg[b]++] = a;
}

static void raw_rem(int a, int b) {
    A[a][b >> 6] &= ~(1ULL << (b & 63));
    A[b][a >> 6] &= ~(1ULL << (a & 63));
    for (int k = 0; k < dg[a]; k++)
        if (nb[a][k] == b) { nb[a][k] = nb[a][--dg[a]]; break; }
    for (int k = 0; k < dg[b]; k++)
        if (nb[b][k] == a) { nb[b][k] = nb[b][--dg[b]]; break; }
}

typedef struct { int add; int a, b; } Op;
static Op LOG[LOGCAP];
static int nlog;

static void add_e(int a, int b) {
    raw_add(a, b);
    if (nlog < LOGCAP) { LOG[nlog].add = 1; LOG[nlog].a = a; LOG[nlog].b = b; nlog++; }
}

static void rem_e(int a, int b) {
    raw_rem(a, b);
    if (nlog < LOGCAP) { LOG[nlog].add = 0; LOG[nlog].a = a; LOG[nlog].b = b; nlog++; }
}

static void undo(void) {
    while (nlog > 0) {
        nlog--;
        if (LOG[nlog].add) raw_rem(LOG[nlog].a, LOG[nlog].b);
        else raw_add(LOG[nlog].a, LOG[nlog].b);
    }
}

/* out[v] = bitset of vertices within distance t of v. */
static void balls(int t, uint64_t out[][MAXW]) {
    int W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < t; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) {
                uint64_t x = out[v][w];
                for (int k = 0; k < dg[v]; k++) x |= out[nb[v][k]][w];
                BUF[v][w] = x;
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) out[v][w] = BUF[v][w];
    }
}

static int cost_D(void) {
    balls(D, RB);
    int W = (N + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(RB[v][w]);
        bad += N - c;
    }
    return (int)(bad / 2);
}

static int rand_vertex_side(int side, int want_spare) {
    for (int t = 0; t < 60; t++) {
        int v = rndint(N);
        if (col[v] != side) continue;
        if (want_spare ? (dg[v] < DEG) : (dg[v] > 0)) return v;
    }
    return -1;
}

static void build_spares(void) {
    nsp = 0;
    for (int v = 0; v < N; v++)
        if (dg[v] < DEG) spare_list[nsp++] = v;
}

static int move_add(void) {
    build_spares();
    if (nsp < 2) return 0;
    for (int t = 0; t < 30; t++) {
        int x = spare_list[rndint(nsp)];
        int u = spare_list[rndint(nsp)];
        if (x == u || col[x] == col[u] || has_edge(x, u)) continue;
        add_e(x, u);
        return 1;
    }
    return 0;
}

static int move_slide(void) {
    build_spares();
    if (nsp < 1) return 0;
    int x = spare_list[rndint(nsp)];
    int p = rand_vertex_side(col[x], 0);
    if (p < 0 || p == x) return 0;
    int q = nb[p][rndint(dg[p])];
    if (q == x || has_edge(x, q)) return 0;
    rem_e(p, q);
    add_e(x, q);
    return 1;
}

static int move_switch(void) {
    int side = rndint(2);
    int a = rand_vertex_side(side, 0);
    if (a < 0) return 0;
    int c = rand_vertex_side(side, 0);
    if (c < 0 || c == a) return 0;
    int b = nb[a][rndint(dg[a])];
    int e = nb[c][rndint(dg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    rem_e(a, b);
    rem_e(c, e);
    add_e(a, e);
    add_e(c, b);
    return 1;
}

static int snapN = 0, snapM = 0;
static int snapCol[MAXN];
static int snapU[MAXN * MAXD / 2 + 4], snapV[MAXN * MAXD / 2 + 4];

static void save_snapshot(void) {
    snapN = N;
    snapM = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < dg[v]; k++) {
            int u = nb[v][k];
            if (v < u) { snapU[snapM] = v; snapV[snapM] = u; snapM++; }
        }
    memcpy(snapCol, col, sizeof(int) * N);
}

static void load_snapshot(void) {
    N = snapN;
    memset(A, 0, sizeof A);
    for (int v = 0; v < N; v++) { dg[v] = 0; col[v] = snapCol[v]; }
    for (int i = 0; i < snapM; i++) raw_add(snapU[i], snapV[i]);
}

/* Add one vertex on a random side, attached greedily to cover vertices (stealing if full). */
static int grow_one(void) {
    if (N >= NMAX) return 0;
    int s = rndint(2);
    int W = (N + 63) >> 6;
    balls(D - 1, RB);
    for (int i = 0; i < MAXW; i++) cover[i] = 0;
    memset(used, 0, sizeof used);
    int chosen[MAXD];
    int nc = 0;
    for (int k = 0; k < DEG; k++) {
        int best = -1;
        long bestkey = -1;
        for (int w = 0; w < N; w++) {
            if (col[w] == s || used[w]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += pc64(RB[w][i] & ~cover[i]);
            if (g <= 0) continue;
            long key = (long)g * 4096 + rndint(4096);
            if (key > bestkey) { bestkey = key; best = w; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int i = 0; i < W; i++) cover[i] |= RB[best][i];
    }
    if (nc == 0) return 0;
    int v = N;
    N++;
    for (int i = 0; i < MAXW; i++) A[v][i] = 0;
    dg[v] = 0;
    col[v] = s;
    for (int k = 0; k < nc; k++) {
        int w = chosen[k];
        if (dg[w] >= DEG) {
            int x = nb[w][rndint(dg[w])];
            raw_rem(w, x);
        }
        raw_add(v, w);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    DEG = d;
    rng_s ^= seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rng_s == 0) rng_s = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n > NMAX || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    memset(A, 0, sizeof A);
    for (int i = 0; i < n; i++) dg[i] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || dg[u] >= DEG || dg[v] >= DEG
            || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        raw_add(u, v);
    }
    /* Bipartition by BFS; reject non-bipartite input. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++];
            for (int k = 0; k < dg[x]; k++) {
                int y = nb[x][k];
                if (col[y] == -1) { col[y] = 1 - col[x]; q[tail++] = y; }
                else if (col[y] == col[x]) { printf("0 0\n"); return 0; }
            }
        }
    }

    t0 = clock();
    nlog = 0;
    int cur = cost_D();
    if (cur == 0) save_snapshot();
    double temp = T0;
    long iter = 0, lastok = 0;
    for (;;) {
        if ((iter & 127) == 0 && elapsed() >= budget) break;
        iter++;
        nlog = 0;
        int moved = 0;
        double r = urand();
        if (r < 0.45) moved = move_add();
        else if (r < 0.7) moved = move_slide();
        if (!moved) moved = move_switch();
        if (moved) {
            int nc = cost_D();
            int delta = nc - cur;
            if (delta <= 0 || urand() < exp(-(double)delta / temp)) cur = nc;
            else undo();
        }
        temp *= DECAY;
        if (temp < TMIN) temp = TMIN;
        if (cur == 0) {
            if (N >= snapN) save_snapshot();
            if (!grow_one()) break;
            cur = cost_D();
            temp = T0;
            lastok = iter;
        } else if (snapN > 0 && iter - lastok > STALL) {
            load_snapshot();
            if (!grow_one()) break;
            cur = cost_D();
            temp = T0;
            lastok = iter;
        }
    }
    if (snapN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured constructions.
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


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """Dense structured graph with degree >= d, later thinned into a valid graph."""
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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    """Swap-based local search for a cover of `full` by at most d candidates."""
    if not cands:
        return None
    k = min(d, len(cands))
    cur = rng.sample(cands, k)

    def cov(S):
        c = 0
        for s in S:
            c |= ball[s]
        return c

    cur_cov = cov(cur)
    cur_score = cur_cov.bit_count()
    for it in range(iters):
        if cur_cov == full:
            return cur
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        inn = rng.choice(cands)
        if inn in cur:
            continue
        trial = cur[:]
        trial[i] = inn
        t_cov = cov(trial)
        t_score = t_cov.bit_count()
        if t_score >= cur_score or rng.random() < 0.02:
            cur, cur_cov, cur_score = trial, t_cov, t_score
    return cur if cur_cov == full else None


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
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _cover_search(cands, ball, full, d, rng, 1500, deadline)
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
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


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


def _engine(d, D, n, e, budget, seed):
    """Run the C annealer from (n, e) for about `budget` seconds. Returns (n, edges) or None."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, e), timeout=budget + 2.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


def _warm(d, D, n, e, seed):
    """Compile the C engine up front so compile time does not eat the search budget."""
    try:
        lib.run_c(C_SOURCE, [d, D, seed, 0.01], stdin_graph=(n, e), timeout=120)
    except Exception:
        pass


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) or PG(2,q)), grown, then twin/grow trials   -> 0.12
#   B  thinned dense graph (degree reduction + deletion), repeated       -> 0.25
#   E1 C annealer with spare-slot moves and growth from the best graph   -> 0.60
#   P  redundant-edge pruning and regrowth                               -> 0.72
#   E2 C annealer again from the best graph                              -> 0.96
# Every candidate passes lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.82 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    fallback = lib.haar_graph(d, range(d))
    consider(*fallback)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown; then twin/grow trials.
    if D >= 2:
        base = None
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
        base_n, base_e = best_n, list(best_e)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.06), rng)
            consider(n1, e1)
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense graph, repeated.
    if D >= 2 and time.monotonic() < at(0.25):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.25):
                r = _deletion_trial(d, D, rn, re, rng, at(0.25))
                if r is None:
                    break
                consider(*r)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    def engine_slice(end_f, sd):
        budget = at(end_f) - time.monotonic()
        if budget < 0.5:
            return
        r = _engine(d, D, best_n, best_e, budget, sd)
        if r is None:
            _prune_regrow(best_n, best_e, d, D, at(end_f), rng, consider)
        else:
            consider(*r)

    if D >= 2 and time.monotonic() < at(0.60):
        _warm(d, D, best_n, best_e, seed % 100003)
        # Phase E1: annealer from the best graph so far.
        engine_slice(0.60, seed % 100003)

    # Phase P: prune redundant edges and regrow.
    if D >= 2 and time.monotonic() < at(0.72):
        _prune_regrow(best_n, best_e, d, D, at(0.72), rng, consider)

    # Phase E2: annealer again from the best graph.
    if D >= 2 and time.monotonic() < at(0.96):
        engine_slice(0.96, seed % 100003 + 1)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
