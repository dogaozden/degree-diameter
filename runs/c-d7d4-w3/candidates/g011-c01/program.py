# New stage: a C simulated-annealing "grow and repair" engine. It starts from the
# best valid graph found by the Python pipeline (GQ/PG base, voltage lifts, twin
# duplication), adds one vertex at a time, and repairs the diameter by annealing
# over degree-preserving endpoint moves, double-edge switches, edge additions and
# edge removals. The cost is the number of vertex pairs at distance > D, computed
# with bitsets. Only states with cost 0 are ever recorded, so the output is always
# valid. If the C stage fails, the Python result is kept.
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

#define MAXN 1024
#define WMAX 16
#define MAXD 32
#define MAXE (MAXN * MAXD)

static int N, DEG, DIAM, CAP;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char ex[MAXN][MAXN];
static int nedges;
static uint64_t BA[MAXN][WMAX];
static uint64_t BB[MAXN][WMAX];

static int bestN, bestM;
static int bestU[MAXE], bestV[MAXE];

typedef struct { int type, a, b; } Op;
static Op oplog[32];
static int nlog;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long cost_fn(void) {
    int wn = (N + 63) >> 6;
    uint64_t (*cur)[WMAX] = BA;
    uint64_t (*nxt)[WMAX] = BB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < wn; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < wn; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < wn; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < wn; w++) c += popc(cur[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void del_one(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
    }
}

static void add_e(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
    ex[a][b] = 1; ex[b][a] = 1;
    nedges++;
}

static void rem_e(int a, int b) {
    del_one(a, b); del_one(b, a);
    ex[a][b] = 0; ex[b][a] = 0;
    nedges--;
}

static void do_add(int a, int b) {
    add_e(a, b);
    oplog[nlog].type = 1; oplog[nlog].a = a; oplog[nlog].b = b; nlog++;
}

static void do_rem(int a, int b) {
    rem_e(a, b);
    oplog[nlog].type = 0; oplog[nlog].a = a; oplog[nlog].b = b; nlog++;
}

static void undo_all(void) {
    while (nlog > 0) {
        nlog--;
        Op o = oplog[nlog];
        if (o.type) rem_e(o.a, o.b);
        else add_e(o.a, o.b);
    }
}

static int rand_connected(void) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(N);
        if (deg[v] > 0) return v;
    }
    return -1;
}

/* Move: re-attach one end of a random edge (x,y) to a random z on y's side. */
static int mv_endpoint(void) {
    int x = rand_connected();
    if (x < 0) return 0;
    int y = nb[x][rndint(deg[x])];
    int z = -1;
    for (int t = 0; t < 60; t++) {
        int c = rndint(N);
        if (side[c] == side[y] && deg[c] < DEG && !ex[x][c]) { z = c; break; }
    }
    if (z < 0) return 0;
    do_rem(x, y);
    do_add(x, z);
    return 1;
}

/* Move: degree-preserving double-edge switch. */
static int mv_switch(void) {
    int x = rand_connected();
    if (x < 0) return 0;
    int y = nb[x][rndint(deg[x])];
    int x2 = -1;
    for (int t = 0; t < 60; t++) {
        int c = rndint(N);
        if (c != x && side[c] == side[x] && deg[c] > 0) { x2 = c; break; }
    }
    if (x2 < 0) return 0;
    int y2 = nb[x2][rndint(deg[x2])];
    if (y2 == y || ex[x][y2] || ex[x2][y]) return 0;
    do_rem(x, y);
    do_rem(x2, y2);
    do_add(x, y2);
    do_add(x2, y);
    return 1;
}

/* Move: add an edge between two vertices with spare degree. */
static int mv_add(void) {
    for (int t = 0; t < 60; t++) {
        int x = rndint(N);
        if (deg[x] >= DEG) continue;
        int y = rndint(N);
        if (side[y] == side[x] || deg[y] >= DEG || ex[x][y]) continue;
        do_add(x, y);
        return 1;
    }
    return 0;
}

/* Move: remove a random edge. */
static int mv_remove(void) {
    int x = rand_connected();
    if (x < 0) return 0;
    int y = nb[x][rndint(deg[x])];
    do_rem(x, y);
    return 1;
}

/* Simulated annealing on the bad-pair cost. Returns the final cost. */
static long long anneal(long long iters, double T0, double T1, double tstop) {
    long long cur = cost_fn();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now() > tstop) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        nlog = 0;
        double r = rnd01();
        int ok;
        if (r < 0.45) ok = mv_endpoint();
        else if (r < 0.80) ok = mv_switch();
        else if (r < 0.95) ok = mv_add();
        else ok = mv_remove();
        if (!ok) { nlog = 0; continue; }
        long long nc = cost_fn();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nc;
        else undo_all();
        nlog = 0;
    }
    return cur;
}

static void take_snapshot(void) {
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v][i];
            if (v < u && bestM < MAXE) {
                bestU[bestM] = v;
                bestV[bestM] = u;
                bestM++;
            }
        }
    }
}

static void restore_best(void) {
    for (int v = 0; v < N; v++) {
        while (deg[v] > 0) rem_e(v, nb[v][0]);
    }
    N = bestN;
    for (int i = 0; i < bestM; i++) add_e(bestU[i], bestV[i]);
    nlog = 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed budget [cap]\n"); return 1; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    CAP = (argc >= 6) ? atoi(argv[5]) : MAXN - 1;
    if (CAP > MAXN - 1) CAP = MAXN - 1;

    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    double tstop = now() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 1 || n > MAXN - 1 || DEG < 1 || DEG > MAXD - 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    N = n;
    nedges = 0;
    nlog = 0;
    int bad = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || ex[u][v] ||
            deg[u] >= DEG || deg[v] >= DEG) {
            bad = 1;
            continue;
        }
        add_e(u, v);
    }

    /* Two-colour the input and check bipartiteness. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N && !bad; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int x = q[head++];
            for (int i = 0; i < deg[x]; i++) {
                int y = nb[x][i];
                if (side[y] < 0) { side[y] = 1 - side[x]; q[tail++] = y; }
                else if (side[y] == side[x]) bad = 1;
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    if (cost_fn() != 0) {
        anneal(20000, 2.0, 0.15, tstop);
        if (cost_fn() != 0) {
            printf("0 0\n");
            return 0;
        }
    }
    take_snapshot();

    const int ROUNDS = 3;
    const long long K = 12000;
    while (now() < tstop && N < CAP) {
        int s = rndint(2);
        side[N] = s;
        deg[N] = 0;
        N++;
        long long c = 1;
        for (int r = 0; r < ROUNDS && c != 0 && now() < tstop; r++) {
            c = anneal(K, 2.5, 0.15, tstop);
        }
        if (c == 0) take_snapshot();
        else restore_best();
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
'''


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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
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
# Voltage lifts over small groups, searched by annealing (Python, cheap stage).
# ----------------------------------------------------------------------------

def _group_specs(lo, hi):
    """Cyclic groups and semidirect products Z_m x| Z_k with order in [lo, hi]."""
    specs = [("cyc", n) for n in range(lo, hi + 1)]
    for k in range(2, 13):
        for m in range(2, hi // k + 1):
            if not (lo <= m * k <= hi):
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append(("semi", m, k, r))
    return specs


def _make_group(spec):
    """Return (order, mul, inv) for a group spec from _group_specs."""
    if spec[0] == "cyc":
        return lib.cyclic_group(spec[1])
    _, m, k, r = spec
    return lib.semidirect_group(m, k, r)


def _random_base(a, d, rng, order):
    """Random base darts [i, j, g]: every A-vertex and B-vertex gets exactly d darts."""
    left = [i for i in range(a) for _ in range(d)]
    right = list(left)
    rng.shuffle(right)
    return [[left[k], right[k], rng.randrange(order)] for k in range(len(left))]


def _lift_adj(a, order, darts, R):
    """Adjacency lists of the lift. Side A is indices 0..a*order-1, side B is the rest."""
    N = 2 * a * order
    off = a * order
    adj = [[] for _ in range(N)]
    for i, j, g in darts:
        Rg = R[g]
        ba = i * order
        bb = off + j * order
        for x in range(order):
            u = ba + x
            v = bb + Rg[x]
            adj[u].append(v)
            adj[v].append(u)
    return adj


def _lift_cost(adj, a, order, D):
    """Number of (representative, vertex) pairs at distance > D, over the 2a representatives."""
    N = len(adj)
    total = 0
    sources = [i * order for i in range(a)] + [a * order + j * order for j in range(a)]
    for s in sources:
        seen = [False] * N
        seen[s] = True
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _lift_edges(a, order, darts, R):
    """Sorted edge list of the lift (every edge joins side A to side B)."""
    off = a * order
    E = set()
    for i, j, g in darts:
        Rg = R[g]
        for x in range(order):
            E.add((i * order + x, off + j * order + Rg[x]))
    return sorted(E)


def _voltage_search(a, d, D, order, R, rng, iters, deadline):
    """Anneal darts of a random base until the lift has diameter <= D. Returns darts or None."""
    darts = _random_base(a, d, rng, order)
    cur = _lift_cost(_lift_adj(a, order, darts, R), a, order, D)
    for _ in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        new = [list(x) for x in darts]
        if rng.random() < 0.7:
            new[rng.randrange(len(new))][2] = rng.randrange(order)
        else:
            k1 = rng.randrange(len(new))
            k2 = rng.randrange(len(new))
            new[k1][1], new[k2][1] = new[k2][1], new[k1][1]
        c2 = _lift_cost(_lift_adj(a, order, new, R), a, order, D)
        if c2 <= cur or rng.random() < 0.02:
            darts, cur = new, c2
    return darts if cur == 0 else None


def _lift_stage(d, D, get_best, rng, deadline, consider):
    """Repeatedly search voltage lifts over random groups just above the current best order."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        best = get_best()
        avail = [a for a in (1, 2) if best // (2 * a) + 1 <= moore // (2 * a)]
        if not avail:
            return
        a = rng.choice(avail)
        lo = best // (2 * a) + 1
        hi = min(moore // (2 * a), lo + 60)
        specs = _group_specs(lo, hi)
        if not specs:
            return
        spec = rng.choice(specs)
        order, mul, _ = _make_group(spec)
        R = [[mul(x, g) for x in range(order)] for g in range(order)]
        darts = _voltage_search(a, d, D, order, R, rng, 1500, deadline)
        if darts is not None:
            consider(2 * a * order, _lift_edges(a, order, darts, R))


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def at(frac):
        return start + frac * time_limit

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)

    # Voltage-lift search over small groups (Python, cheap).
    lift_end = at(0.15)
    if time.monotonic() < lift_end:
        _lift_stage(d, D, lambda: best_n, rng, lift_end, consider)

    # Randomized twin-duplication pipelines from the structured base.
    trial_end = at(0.20)
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # NEW: C grow-and-repair annealing from the best valid graph found so far.
    cap = min(moore, 1000)
    c_end = at(0.88) - 2.0
    budget = c_end - time.monotonic()
    if d <= 30 and best_n < cap and budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), cap],
                             stdin_graph=(best_n, best_e), timeout=budget + 20.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
