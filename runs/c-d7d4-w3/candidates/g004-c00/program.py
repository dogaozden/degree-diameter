import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: penalty annealing with vertex insertion.
#
# State: a bipartite graph (colour classes 0/1) with max degree d. Cost =
# (number of vertex pairs at distance > D, unreachable pairs included)
# + PEN * (total degree overflow above d). Moves: degree-preserving edge
# switches, endpoint rewires (which may overflow, penalised), and fills of
# spare-degree pairs. Whenever the current graph has cost 0, the engine
# inserts a new vertex joined to the lowest-degree opposite-side vertices and
# anneals again. Failed attempts restore the best valid graph. Output is the
# best graph with cost 0 (degree <= d, bipartite, diameter <= D).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define WMAX 19
#define MAXDEG 64
#define DEGCAP 32
#define MAXE (MAXN * DEGCAP)
#define PEN 2
#define ITERS 40000L

static int N = 0, D_ = 2, DEG = 3;
static unsigned char A[MAXN][MAXN];
static int deg[MAXN], col[MAXN];
static int nb[MAXN][MAXDEG];
static uint64_t B1[MAXN][WMAX], B2[MAXN][WMAX];
static uint64_t rs = 88172645463325252ULL;
static double t_end = 0.0;

static int bn = 0, bm = 0;
static int bcol[MAXN];
static int beu[MAXE], bev[MAXE];

static int lg_t[16], lg_a[16], lg_b[16], lg_n = 0;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void edge_add(int a, int b) {
    A[a][b] = 1; A[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void list_remove(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
}

static void edge_del(int a, int b) {
    A[a][b] = 0; A[b][a] = 0;
    list_remove(a, b);
    list_remove(b, a);
}

static void L_add(int a, int b) {
    lg_t[lg_n] = 1; lg_a[lg_n] = a; lg_b[lg_n] = b; lg_n++;
    edge_add(a, b);
}

static void L_del(int a, int b) {
    lg_t[lg_n] = 0; lg_a[lg_n] = a; lg_b[lg_n] = b; lg_n++;
    edge_del(a, b);
}

static void undo(void) {
    while (lg_n > 0) {
        lg_n--;
        if (lg_t[lg_n] == 1) edge_del(lg_a[lg_n], lg_b[lg_n]);
        else edge_add(lg_a[lg_n], lg_b[lg_n]);
    }
}

static void reset_state(int n) {
    int lim = N > n ? N : n;
    for (int v = 0; v < lim; v++) {
        deg[v] = 0;
        for (int u = 0; u < lim; u++) A[v][u] = 0;
    }
    N = n;
    lg_n = 0;
}

static long cost(void) {
    int n = N;
    int w = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) B1[v][k] = 0;
        B1[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[WMAX] = B1;
    uint64_t (*nxt)[WMAX] = B2;
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < w; k++) nxt[v][k] = cur[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int k = 0; k < w; k++) nxt[v][k] |= cur[u][k];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(cur[v][k]);
        bad += n - c;
    }
    bad /= 2;
    long over = 0;
    for (int v = 0; v < n; v++)
        if (deg[v] > DEG) over += deg[v] - DEG;
    return bad + PEN * over;
}

static void compute_colors(void) {
    static int stk[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[u][i];
                if (col[w] < 0) { col[w] = 1 - col[u]; stk[sp++] = w; }
            }
        }
    }
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < N; u++)
        for (int v = u + 1; v < N; v++)
            if (A[u][v]) {
                if (m >= MAXE) return;
                beu[m] = u; bev[m] = v; m++;
            }
    bn = N; bm = m;
    memcpy(bcol, col, sizeof(int) * N);
}

static void load_best(void) {
    reset_state(bn);
    memcpy(col, bcol, sizeof(int) * bn);
    for (int i = 0; i < bm; i++) edge_add(beu[i], bev[i]);
}

static int pick_side_vertex(int c) {
    for (int t = 0; t < 1000; t++) {
        int v = rndi(N);
        if (col[v] == c && deg[v] > 0) return v;
    }
    return -1;
}

static int move_switch(void) {
    int a = pick_side_vertex(0);
    if (a < 0) return 0;
    int b = nb[a][rndi(deg[a])];
    int c = pick_side_vertex(0);
    if (c < 0 || c == a) return 0;
    int e = nb[c][rndi(deg[c])];
    if (A[a][e] || A[c][b] || e == b) return 0;
    L_del(a, b);
    L_del(c, e);
    L_add(a, e);
    L_add(c, b);
    return 1;
}

static int move_rewire(void) {
    int a = pick_side_vertex(0);
    if (a < 0) return 0;
    int b = nb[a][rndi(deg[a])];
    if (rndi(2)) {
        int e = rndi(N);
        if (col[e] != 1 || e == b || A[a][e] || deg[e] >= MAXDEG - 1) return 0;
        L_del(a, b);
        L_add(a, e);
    } else {
        int c = rndi(N);
        if (col[c] != 0 || c == a || A[c][b] || deg[c] >= MAXDEG - 1) return 0;
        L_del(a, b);
        L_add(c, b);
    }
    return 1;
}

static int move_fill(void) {
    for (int t = 0; t < 60; t++) {
        int a = rndi(N), b = rndi(N);
        if (col[a] != 0 || col[b] != 1) continue;
        if (deg[a] >= DEG || deg[b] >= DEG || A[a][b]) continue;
        L_add(a, b);
        return 1;
    }
    return 0;
}

static long anneal(long iters, double T0, double T1) {
    long cur = cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        lg_n = 0;
        int r = rndi(10);
        int ok;
        if (r < 4) ok = move_switch();
        else if (r < 9) ok = move_rewire();
        else ok = move_fill();
        if (!ok) { undo(); continue; }
        long nc = cost();
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            lg_n = 0;
        } else {
            undo();
        }
    }
    lg_n = 0;
    return cur;
}

static void add_vertex(int c) {
    int v = N++;
    deg[v] = 0;
    col[v] = c;
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (col[u] != c && deg[u] < MAXDEG - 1) cand[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    for (int i = 1; i < nc; i++) {
        int x = cand[i];
        int j = i - 1;
        while (j >= 0 && deg[cand[j]] > deg[x]) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = x;
    }
    int k = nc < DEG ? nc : DEG;
    for (int i = 0; i < k; i++) edge_add(v, cand[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    DEG = d;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    t_end = now() + budget;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 100 ||
        DEG < 1 || DEG > DEGCAP || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    reset_state(n);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v] ||
            deg[u] >= DEG || deg[v] >= DEG)
            continue;
        edge_add(u, v);
    }
    compute_colors();
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (col[u] == col[nb[u][i]]) { printf("0 0\n"); return 0; }

    long c0 = cost();
    if (c0 != 0) c0 = anneal(ITERS * 4, 2.0, 0.1);
    if (c0 == 0) save_best();
    if (bn == 0) { printf("0 0\n"); return 0; }

    while (now() < t_end && N < MAXN - 2) {
        load_best();
        add_vertex(rndi(2));
        long c = anneal(ITERS, 2.0, 0.1);
        if (c == 0) save_best();
    }

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", beu[i], bev[i]);
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
# Shared Python graph helpers.
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
# Bipartite voltage lifts over small (possibly non-abelian) groups.
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples describing groups of order G: cyclic plus Z_M x|_r Z_k with M*k = G."""
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
    """Anneal voltages of a bipartite lift. Returns a valid (n, edges) or None."""
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
    """Repeatedly try lifts that would beat the current best order."""
    while time.monotonic() < deadline:
        best_n = get_best()
        s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
        G_min = best_n // (2 * s) + 1
        G = G_min + rng.randrange(4)
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
# C search driver.
# ----------------------------------------------------------------------------

def _c_search(n, edges, d, D, seed, budget):
    """Run the C penalty-annealing vertex inserter for about `budget` seconds.

    Returns a valid (n2, e2) with n2 > n, or None. Any failure returns None.
    """
    if budget < 1.0 or n > 1000 or d > 32 or d < 1:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(n, edges), timeout=budget + 15.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 > n and lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


# ----------------------------------------------------------------------------
# Driver. Time fractions of time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials, to 0.15
#   L  voltage lifts over small groups, to 0.30
#   C  C penalty-annealing vertex insertion from the best graph, to 0.85
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)

    def at(f):
        return start + f * tl

    rng = random.Random(seed)

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

    # Phase A: structured base, grown; then twin/grow trials.
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
        n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.30):
        _lift_phase(d, D, lambda: best_n, at(0.30), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: C penalty-annealing vertex insertion from the best valid graph.
    c_budget = start + 0.85 * tl - 1.0 - time.monotonic()
    if D >= 2 and c_budget >= 1.0:
        cseed = int(seed) & 0x7FFFFFFF
        res = _c_search(best_n, best_e, d, D, cseed, c_budget)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
