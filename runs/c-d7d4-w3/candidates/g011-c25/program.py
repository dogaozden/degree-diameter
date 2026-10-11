import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C annealer (new in this version).
#
# Input: a valid bipartite graph (max degree d, diameter <= D), read from stdin.
# State: a valid graph. Cost = number of vertex pairs at distance > D, computed
# with bitsets (radius-D balls by repeated OR over neighbours).
#
# Moves:
#   switch    degree-preserving edge swap between two A-side vertices, Metropolis
#   grow      add a new vertex on a random side; take its d neighbours from the
#             other side, stealing one edge from each full neighbour; fill spare
#             degree; anneal back to cost 0. Failure restores the saved state.
#   perturb   force K random switches (leaves the vertex count unchanged), then
#             anneal back to cost 0. Failure restores the saved state.
# The state is always valid, so the output is valid whenever it is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 16

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} Snap;

static int d, D, n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t bsA[MAXN][MAXW];
static uint64_t bsB[MAXN][MAXW];
static double T_temp = 0.4;
static double deadline_s = 10.0;
static uint64_t rs = 88172645463325252ULL;
static Snap sG, sP;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long cost_fn(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = bsA;
    uint64_t (*nxt)[MAXW] = bsB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * MAXW);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < D; k++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * W);
            for (int j = 0; j < deg[v]; j++) {
                uint64_t *src = cur[adj[v][j]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++)
        if (adj[a][j] == b) return 1;
    return 0;
}
static void del_dir(int a, int b) {
    for (int j = 0; j < deg[a]; j++) {
        if (adj[a][j] == b) {
            adj[a][j] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void add_dir(int a, int b) { adj[a][deg[a]++] = b; }
static void add_edge(int a, int b) { add_dir(a, b); add_dir(b, a); }
static void del_edge(int a, int b) { del_dir(a, b); del_dir(b, a); }

static void save_s(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(deg));
    memcpy(s->adj, adj, sizeof(adj));
    memcpy(s->side, side, sizeof(side));
}
static void load_s(const Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(deg));
    memcpy(adj, s->adj, sizeof(adj));
    memcpy(side, s->side, sizeof(side));
}

static int pick_on(int s) {
    for (int t = 0; t < 200; t++) {
        int v = rndi(n);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

static void shuffle_arr(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Degree-preserving switch: (a,b),(c,e) -> (a,e),(c,b), with a,c on side 0. */
static int try_switch(int force, long *cur) {
    int a = pick_on(0);
    int c = pick_on(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj[a][rndi(deg[a])];
    int e = adj[c][rndi(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    long nc = cost_fn();
    if (force || nc <= *cur || rndu() < exp((double)(*cur - nc) / T_temp)) {
        *cur = nc;
        return 1;
    }
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
    return 0;
}

static long anneal(long cur, long iters) {
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now() > deadline_s) break;
        try_switch(0, &cur);
    }
    return cur;
}

/* Greedy random fill of spare degree between the two sides (never raises cost). */
static void fill_all(void) {
    static int L0[MAXN];
    static int L1[MAXN];
    int k0 = 0, k1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= d) continue;
        if (side[v] == 0) L0[k0++] = v;
        else L1[k1++] = v;
    }
    shuffle_arr(L0, k0);
    shuffle_arr(L1, k1);
    for (int i = 0; i < k0; i++) {
        int a = L0[i];
        for (int j = 0; j < k1 && deg[a] < d; j++) {
            int b = L1[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add one vertex with stealing, fill, anneal. Keeps the new state only if cost reaches 0. */
static int grow_attempt(int iters, Snap *sv) {
    save_s(sv);
    int c = rndi(2);
    int v = n++;
    side[v] = c;
    deg[v] = 0;
    static int opp[MAXN];
    int k = 0;
    for (int u = 0; u < v; u++)
        if (side[u] != c) opp[k++] = u;
    shuffle_arr(opp, k);
    for (int i = 0; i < k && deg[v] < d; i++) {
        int u = opp[i];
        if (deg[u] < d) add_edge(u, v);
    }
    for (int i = 0; i < k && deg[v] < d; i++) {
        int u = opp[i];
        if (deg[u] >= d && deg[u] > 0 && !has_edge(u, v)) {
            int w = adj[u][rndi(deg[u])];
            del_edge(u, w);
            add_edge(u, v);
        }
    }
    fill_all();
    long cur = cost_fn();
    cur = anneal(cur, iters);
    if (cur == 0) return 1;
    load_s(sv);
    return 0;
}

/* Force K switches, then anneal back to cost 0; otherwise restore. */
static int perturb_attempt(int K, int iters, Snap *sv) {
    save_s(sv);
    long cur = cost_fn();
    for (int k = 0; k < K; k++) try_switch(1, &cur);
    cur = anneal(cur, iters);
    if (cur == 0) return 1;
    load_s(sv);
    return 0;
}

static int bipartize(void) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int j = 0; j < deg[u]; j++) {
                int w = adj[u][j];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    q[t++] = w;
                } else if (side[w] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    deadline_s = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 8 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || deg[u] >= d || deg[v] >= d || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    if (!bipartize()) {
        printf("0 0\n");
        return 0;
    }
    long cur = cost_fn();
    if (cur > 0) cur = anneal(cur, 400000L);
    if (cur > 0) {
        printf("0 0\n");
        return 0;
    }

    int gsucc = 0, psucc = 0;
    while (now() < deadline_s) {
        if (n >= MAXN - 2) break;
        if (rndi(10) < 6) gsucc += grow_attempt(2000, &sG);
        else psucc += perturb_attempt(3, 3000, &sP);
    }
    (void)gsucc;
    (void)psucc;

    if (cost_fn() != 0) {
        printf("0 0\n");
        return 0;
    }
    int m = 0;
    for (int v = 0; v < n; v++)
        for (int j = 0; j < deg[v]; j++)
            if (adj[v][j] > v) m++;
    printf("%d %d\n", n, m);
    for (int v = 0; v < n; v++)
        for (int j = 0; j < deg[v]; j++)
            if (adj[v][j] > v) printf("%d %d\n", v, adj[v][j]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases (from the parent).
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
# Shared graph helpers (from the parent).
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
# Voltage lifts over small (semi)direct product groups (from the parent).
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


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    """Anneal voltages of a bipartite lift.

    Returns (result, darts, temp): result is a valid (n, edges) or None when the
    deadline hit first. darts and temp let the caller resume the run later.
    """
    if darts is None:
        darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None, darts, temp
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
    return (n, e), darts, temp


def _lift_phase(d, D, get_best, deadline, rng, consider):
    """Anneal lifts that would beat the current best order, resuming parked runs."""
    states = {}  # key (s, G, M, k, r) -> (darts, temp)
    while time.monotonic() < deadline:
        best_n = get_best()
        states = {key: v for key, v in states.items() if 2 * key[0] * key[1] > best_n}
        if states and rng.random() < 0.7:
            key = rng.choice(list(states))
            darts, temp = states.pop(key)
            s, G, M, k, r = key
        else:
            darts, temp = None, 0.6
            s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
            G_min = best_n // (2 * s) + 1
            G = G_min + rng.randrange(4)
            opts = _group_options(G)
            if not opts:
                continue
            M, k, r = rng.choice(opts)
            key = (s, G, M, k, r)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res, darts, temp = _lift_search(d, D, s, G, mul, rng, slice_end, darts, temp)
        if res is None:
            states[key] = (darts, temp)
            if len(states) > 40:
                states.pop(next(iter(states)))
            continue
        n, e = res
        consider(n, e)
        n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# Python large-neighbourhood search (fallback when the C engine fails).
# ----------------------------------------------------------------------------

def _fill(adj, color, d, rng):
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
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# C engine driver (new).
# ----------------------------------------------------------------------------

def _c_engine(d, D, seed, graph, secs, timeout):
    """Run the C annealer from graph for about secs CPU seconds; return (n, edges) or None."""
    n, e = graph
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.2f}"],
                    stdin_graph=(n, e), timeout=timeout)
    cn, ce = lib.parse_graph_text(out)
    if cn <= 0:
        return None
    return cn, ce


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.9 * time_limit, split into phases:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials
#   L  voltage lifts over small groups, annealed to diameter <= D, then grown
#   E  C annealer (bitset cost, vertex insertion with stealing, perturbation)
#   C  Python LNS fallback for leftover time
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.9 * time_limit

    def at(f):
        return start + f * T

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
        n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.10)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.30):
        _lift_phase(d, D, lambda: best_n, at(0.30), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase E: C annealer from the best valid graph found so far.
    if D >= 2:
        secs = at(0.96) - time.monotonic() - 2.0
        if secs >= 2.0:
            try:
                res = _c_engine(d, D, int(seed) % 1000000007, (best_n, list(best_e)),
                                secs, at(0.99) - time.monotonic())
            except (RuntimeError, ValueError, OSError):
                res = None
            if res is not None:
                consider(res[0], res[1])

    # Phase C: Python LNS for any leftover time.
    if D >= 2 and time.monotonic() < at(0.96):
        _lns(best_n, best_e, d, D, at(0.96), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
