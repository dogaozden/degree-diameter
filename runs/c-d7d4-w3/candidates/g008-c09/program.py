import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: deletion search on a dense bipartite base graph.
#
# Input: base graph on stdin ("n m" then edges), argv = d D seed seconds.
# State: a subset of alive vertices. Energy = bad pairs (distance > D inside the
# induced subgraph, unreachable counted) + excess degree - 0.5 * alive count.
# Simulated annealing with single-vertex flips. Every state with zero bad pairs
# and zero excess is a valid bipartite graph of diameter <= D and max degree <= d;
# the largest such state is printed. Prints "0 0" if none was found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define STALL 12000L

static const double T0 = 1.0;
static const double T1 = 0.05;

static int N, W, DD, DMAX;
static int *off, *nb;
static u64 *cur, *nxt;
static unsigned char *alive, *bestAlive;
static u64 rs;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int rndint(int m) {
    return (int)(rnd() % (u64)m);
}

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void evaluate(long *bad, long *excess, int *cnt) {
    int c = 0;
    long ex = 0;
    for (int v = 0; v < N; v++) if (alive[v]) c++;
    for (int v = 0; v < N; v++) {
        if (!alive[v]) continue;
        int k = 0;
        for (int i = off[v]; i < off[v + 1]; i++) if (alive[nb[i]]) k++;
        if (k > DMAX) ex += k - DMAX;
    }
    *cnt = c;
    *excess = ex;

    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        if (alive[v]) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);

    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            if (!alive[v]) continue;
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = off[v]; i < off[v + 1]; i++) {
                int u = nb[i];
                if (!alive[u]) continue;
                const u64 *s2 = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *t = cur;
        cur = nxt;
        nxt = t;
    }

    long ps = 0;
    for (int v = 0; v < N; v++) {
        if (!alive[v]) continue;
        const u64 *b = cur + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(b[w]);
        ps += c - pc;
    }
    *bad = ps / 2;
}

static double energy(long b, long x, int c) {
    return (double)b + (double)x - 0.5 * (double)c;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    DMAX = d;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *dg = calloc((size_t)n, sizeof(int));
    int k = 0;
    for (int i = 0; i < m; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) continue;
        eu[k] = a;
        ev[k] = b;
        k++;
        dg[a]++;
        dg[b]++;
    }
    m = k;

    N = n;
    W = (N + 63) / 64;
    off = malloc(sizeof(int) * (size_t)(N + 1));
    off[0] = 0;
    for (int v = 0; v < N; v++) off[v + 1] = off[v] + dg[v];
    nb = malloc(sizeof(int) * (size_t)(2 * m > 0 ? 2 * m : 1));
    int *pos = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) pos[v] = off[v];
    for (int i = 0; i < m; i++) {
        nb[pos[eu[i]]++] = ev[i];
        nb[pos[ev[i]]++] = eu[i];
    }

    cur = calloc((size_t)N * (size_t)W, sizeof(u64));
    nxt = calloc((size_t)N * (size_t)W, sizeof(u64));
    alive = malloc((size_t)N);
    bestAlive = calloc((size_t)N, 1);
    for (int v = 0; v < N; v++) alive[v] = 1;

    rs = (u64)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd();

    clock_t t0 = clock();
    long bad, ex, nbad, nex;
    int cnt, ncnt;
    evaluate(&bad, &ex, &cnt);
    double E = energy(bad, ex, cnt);
    int bestCnt = 0;
    if (bad == 0 && ex == 0) {
        bestCnt = cnt;
        memcpy(bestAlive, alive, (size_t)N);
    }

    long iter = 0, lastImp = 0;
    double T = T0;
    for (;;) {
        if ((iter & 7) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
            double frac = el / tl;
            T = T0 * pow(T1 / T0, frac);
        }
        iter++;
        int v = rndint(N);
        alive[v] ^= 1;
        evaluate(&nbad, &nex, &ncnt);
        double NE = energy(nbad, nex, ncnt);
        double dE = NE - E;
        if (dE <= 0.0 || rnd01() < exp(-dE / T)) {
            E = NE;
            bad = nbad;
            ex = nex;
            cnt = ncnt;
            if (bad == 0 && ex == 0 && cnt > bestCnt) {
                bestCnt = cnt;
                memcpy(bestAlive, alive, (size_t)N);
                lastImp = iter;
            }
        } else {
            alive[v] ^= 1;
        }
        if (bestCnt > 0 && iter - lastImp > STALL) {
            memcpy(alive, bestAlive, (size_t)N);
            evaluate(&bad, &ex, &cnt);
            E = energy(bad, ex, cnt);
            lastImp = iter;
        }
    }

    if (bestCnt == 0) {
        printf("0 0\n");
        return 0;
    }
    int *map = malloc(sizeof(int) * (size_t)N);
    int k2 = 0;
    for (int v = 0; v < N; v++) {
        if (bestAlive[v]) map[v] = k2++;
        else map[v] = -1;
    }
    long me = 0;
    for (int v = 0; v < N; v++) {
        if (!bestAlive[v]) continue;
        for (int i = off[v]; i < off[v + 1]; i++) {
            int u = nb[i];
            if (bestAlive[u] && v < u) me++;
        }
    }
    printf("%d %ld\n", k2, me);
    for (int v = 0; v < N; v++) {
        if (!bestAlive[v]) continue;
        for (int i = off[v]; i < off[v + 1]; i++) {
            int u = nb[i];
            if (bestAlive[u] && v < u) printf("%d %d\n", map[v], map[u]);
        }
    }
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
            nb_ = adj[v]
            if not nb_ or len(nb_) > d:
                continue
            if any(len(adj[u]) >= d for u in nb_):
                continue
            w = len(adj)
            adj.append(set(nb_))
            for u in nb_:
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
# Unstructured d-regular bipartite search (from the parent).
# ----------------------------------------------------------------------------

def _rr_add_pair(adj, left, right, d, rng):
    elist = [(x, y) for x in left for y in adj[x]]
    rng.shuffle(elist)
    xs, ys, picked = set(), set(), []
    for x, y in elist:
        if x in xs or y in ys:
            continue
        xs.add(x)
        ys.add(y)
        picked.append((x, y))
        if len(picked) == d:
            break
    if len(picked) < d:
        return False
    a = len(adj)
    adj.append(set())
    b = len(adj)
    adj.append(set())
    left.append(a)
    right.append(b)
    for x, y in picked:
        adj[x].discard(y)
        adj[y].discard(x)
        adj[a].add(y)
        adj[y].add(a)
        adj[x].add(b)
        adj[b].add(x)
    return True


def _rr_anneal(adj, left, D, rng, iters, deadline):
    elist = [(x, y) for x in left for y in adj[x]]
    cur = _cost(adj, D)
    temp = 0.5
    for _ in range(iters):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            return False
        p = rng.randrange(len(elist))
        q = rng.randrange(len(elist))
        a, b = elist[p]
        c, e = elist[q]
        if a == c or b == e:
            continue
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
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            elist[p] = (a, e)
            elist[q] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
        temp = max(0.05, temp * 0.9995)
    return cur == 0


def _rr_phase(d, D, deadline, rng, consider):
    h = d
    adj = [set() for _ in range(2 * h)]
    left = list(range(h))
    right = list(range(h, 2 * h))
    for i in range(h):
        for j in right:
            adj[i].add(j)
            adj[j].add(i)
    while time.monotonic() < deadline:
        if not _rr_add_pair(adj, left, right, d, rng):
            break
        if not _rr_anneal(adj, left, D, rng, 2000, deadline):
            break
        e = [(u, v) for u in left for v in adj[u]]
        consider(len(adj), e)


# ----------------------------------------------------------------------------
# Bipartite voltage lifts over small groups (from the parent).
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
# Large-neighbourhood search and pruning (from the parent).
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
# Parent pipeline, unchanged except for its name. Budget T = 0.8 * time_limit.
# ----------------------------------------------------------------------------

def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.8 * time_limit

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
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase R: unstructured degree-preserving growth with annealing.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.50):
        _rr_phase(d, D, at(0.50), rng, consider)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.64):
        _lift_phase(d, D, lambda: best_n, at(0.64), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: LNS from the best valid graph of any construction.
    if D >= 2 and time.monotonic() < at(0.84):
        _lns(best_n, best_e, d, D, at(0.84), rng, consider)

    # Phase D: prune redundant edges and regrow from the best graph.
    if D >= 2 and time.monotonic() < at(0.97):
        _prune_regrow(best_n, best_e, d, D, at(0.97), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)


# ----------------------------------------------------------------------------
# NEW construction: delete vertices from the W(d) incidence graph.
#
# W(q) with q = d is (d+1)-regular, bipartite and has diameter 4. Removing a
# vertex set so that every survivor loses a neighbour gives max degree d.
# Deletion can push diameter above 4, so the C engine anneals the kept set
# against the true bad-pair count and only reports valid states.
# ----------------------------------------------------------------------------

def _deletion_search(d, D, seed, budget):
    n0, e0 = _gq_w(d)
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                     stdin_graph=(n0, e0), timeout=budget + 20.0)
    n, e = lib.parse_graph_text(text)
    if n < 1:
        return None
    rng = random.Random(seed)
    e = _saturate_edges(n, e, d, rng)
    n, e = _grow(n, e, d, D, time.monotonic() + 2.0, rng)
    e = _saturate_edges(n, e, d, rng)
    return n, e


def _pick(cands, d, D, cur):
    best_n, best_e = cur
    for n, e in cands:
        if n > best_n and lib.is_valid(n, list(e), d, D):
            best_n, best_e = n, list(e)
    return best_n, best_e


# ----------------------------------------------------------------------------
# Driver.
#
# For D = 4 with d a prime power, half the budget goes to the deletion engine
# on W(d); the remainder goes to the parent pipeline. Every candidate passes
# lib.is_valid, and a valid K_{1,1}-free fallback is always kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1 or D == 1:
        return _parent_build(d, D, seed, time_limit)

    cur = (2, [(0, 1)])
    cands = []
    budget = 0.85 * time_limit

    use_del = D == 4 and d >= 3 and lib.is_prime_power(d)
    if use_del:
        try:
            res = _deletion_search(d, D, seed, 0.5 * budget)
            if res is not None:
                cands.append(res)
        except Exception:
            pass
        left = budget - (time.monotonic() - start)
        parent_tl = max(left, 0.0) / 0.8
    else:
        parent_tl = time_limit

    try:
        cands.append(_parent_build(d, D, seed, parent_tl))
    except Exception:
        pass

    return _pick(cands, d, D, cur)
