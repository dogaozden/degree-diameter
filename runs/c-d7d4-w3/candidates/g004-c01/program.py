import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost annealing with vertex insertion.
#
# State: bipartite graph with max degree d on N vertices. Cost = number of
# unordered vertex pairs at distance > D, computed from radius-D balls held
# as bitsets. Moves: degree-preserving edge switches (a-b, c-e -> a-e, c-b
# with side(a) = side(c)) and edge additions between spare-degree vertices.
# When cost reaches 0 the graph is saved and a new vertex is inserted,
# greedily joined to opposite-colour vertices by ball coverage (radius D-1).
# If the search stalls, it restores the best saved graph and grows again.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 64
#define MAXE 40000
#define STALE_LIMIT 20000L

static int N, DD, DIAM;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static uint64_t BR[MAXN][MAXW];
static uint64_t BS[MAXN][MAXW];
static uint64_t TMP[MAXN][MAXW];

static int IU[MAXE], IV[MAXE];
static int BU[MAXE], BV[MAXE];
static int bestN = 0, bestM = 0;
static int bestSide[MAXN];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (nb[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void drop_nb(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (nb[u][k] == v) {
            nb[u][k] = nb[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    drop_nb(u, v);
    drop_nb(v, u);
}

/* out[v] = set of vertices within distance r of v, over the current N vertices. */
static void balls(int r, uint64_t out[][MAXW]) {
    int W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) TMP[v][w] = out[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = out[nb[v][k]];
                for (int w = 0; w < W; w++) TMP[v][w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) out[v][w] = TMP[v][w];
    }
}

/* Number of unordered pairs at distance > DIAM. Zero iff the graph is valid. */
static long bad_pairs(void) {
    balls(DIAM, BR);
    int W = (N + 63) / 64;
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(BR[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

/* Append a vertex of colour c joined greedily to opposite-colour vertices by coverage.
   Returns the number of edges added; 0 means N was left unchanged. */
static int grow_vertex(int c) {
    if (N + 1 >= MAXN) return 0;
    int v = N;
    int Wold = (N + 63) / 64;
    balls(DIAM - 1, BS);
    uint64_t cov[MAXW];
    for (int w = 0; w < Wold; w++) cov[w] = 0;
    N = v + 1;
    side[v] = c;
    deg[v] = 0;
    int added = 0;
    while (added < DD) {
        int best = -1;
        long bestkey = -1000000000L;
        for (int s = 0; s < v; s++) {
            if (side[s] == c || has_edge(s, v)) continue;
            int g = 0;
            for (int w = 0; w < Wold; w++) g += popc(BS[s][w] & ~cov[w]);
            if (g == 0 && deg[s] >= DD) continue;
            long key = (long)(2 * g - (deg[s] >= DD ? 1 : 0)) * 1024L + rndint(1024);
            if (key > bestkey) {
                bestkey = key;
                best = s;
            }
        }
        if (best < 0) break;
        if (deg[best] >= DD) {
            int t = nb[best][rndint(deg[best])];
            del_edge(best, t);
        }
        add_edge(best, v);
        for (int w = 0; w < Wold; w++) cov[w] |= BS[best][w];
        added++;
    }
    if (added == 0) {
        N = v;
        return 0;
    }
    return added;
}

/* Degree-preserving switch: a-b, c-e -> a-e, c-b with side(a) = side(c). */
static int try_switch(int *pa, int *pb, int *pc, int *pe) {
    int a = rndint(N);
    if (deg[a] == 0) return 0;
    int b = nb[a][rndint(deg[a])];
    int c = rndint(N);
    if (c == a || side[c] != side[a] || deg[c] == 0) return 0;
    int e = nb[c][rndint(deg[c])];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    *pa = a;
    *pb = b;
    *pc = c;
    *pe = e;
    return 1;
}

static void undo_switch(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Add an edge between two spare-degree vertices of opposite colour. */
static int try_add(void) {
    static int sp[2][MAXN];
    int ns[2] = {0, 0};
    for (int v = 0; v < N; v++)
        if (deg[v] < DD) sp[side[v]][ns[side[v]]++] = v;
    if (ns[0] == 0 || ns[1] == 0) return 0;
    for (int t = 0; t < 20; t++) {
        int a = sp[0][rndint(ns[0])];
        int b = sp[1][rndint(ns[1])];
        if (!has_edge(a, b)) {
            add_edge(a, b);
            return 1;
        }
    }
    return 0;
}

static void save_best(void) {
    if (N <= bestN) return;
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++) {
        bestSide[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (v < u) {
                BU[bestM] = v;
                BV[bestM] = u;
                bestM++;
            }
        }
    }
}

static void restore_best(void) {
    N = bestN;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        side[v] = bestSide[v];
    }
    for (int i = 0; i < bestM; i++) add_edge(BU[i], BV[i]);
}

static void print_graph(int nn, int mm, int *U, int *V) {
    printf("%d %d\n", nn, mm);
    for (int i = 0; i < mm; i++) printf("%d %d\n", U[i], V[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    int n = 0, m = 0;
    int readok = 1;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
        readok = 0;
    }
    if (m < 0 || m > MAXE || n < 0 || n > MAXN) readok = 0;
    if (readok) {
        for (int i = 0; i < m; i++) {
            if (scanf("%d %d", &IU[i], &IV[i]) != 2) {
                readok = 0;
                break;
            }
        }
    }
    if (!readok || DD < 1 || DD > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int good = 1;
    N = n;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        side[v] = 0;
    }
    for (int i = 0; i < m && good; i++) {
        int u = IU[i], v = IV[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || deg[u] >= DD || deg[v] >= DD ||
            has_edge(u, v)) {
            good = 0;
            break;
        }
        add_edge(u, v);
    }
    if (good) {
        static int col[MAXN], q[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N && good; s++) {
            if (col[s] >= 0) continue;
            int qh = 0, qt = 0;
            col[s] = 0;
            q[qt++] = s;
            while (qh < qt && good) {
                int u = q[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int v = nb[u][k];
                    if (col[v] < 0) {
                        col[v] = 1 - col[u];
                        q[qt++] = v;
                    } else if (col[v] == col[u]) {
                        good = 0;
                        break;
                    }
                }
            }
        }
        if (good)
            for (int v = 0; v < N; v++) side[v] = col[v];
    }
    if (!good || N < 2) {
        print_graph(n, m, IU, IV);
        return 0;
    }

    long cur = bad_pairs();
    if (cur == 0) save_best();

    clock_t c0 = clock();
    double T = 0.6;
    long stale = 0, iter = 0;
    int stop = 0;
    while (!stop) {
        if ((iter & 15) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC >= tl) break;
        iter++;
        if (cur == 0) {
            save_best();
            if (!grow_vertex(rndint(2))) break;
            cur = bad_pairs();
            stale = 0;
            T = 0.3 + 1.2 * rnd01();
            continue;
        }
        stale++;
        if (stale > STALE_LIMIT) {
            if (bestN > 0) {
                restore_best();
                cur = bad_pairs();
            }
            stale = 0;
            T = 0.3 + 1.2 * rnd01();
            continue;
        }
        if (rnd01() < 0.2) {
            if (try_add()) cur = bad_pairs();
            continue;
        }
        int a, b, c, e;
        if (!try_switch(&a, &b, &c, &e)) continue;
        long nc = bad_pairs();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo_switch(a, b, c, e);
        }
    }

    if (bestN > 0)
        print_graph(bestN, bestM, BU, BV);
    else
        print_graph(n, m, IU, IV);
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
# Bipartite voltage lifts over small groups (Python, annealed).
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
# C engine driver.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, n, edges, budget):
    """Run the C annealer from (n, edges) for about `budget` seconds. Returns (n, edges) or None."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(n, edges), timeout=budget + 3.0)
        rn, re_ = lib.parse_graph_text(text)
    except Exception:
        return None
    return rn, re_


# ----------------------------------------------------------------------------
# Large-neighbourhood search and pruning (Python).
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
# Driver. Budget T = 0.85 * time_limit, split into phases:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials
#   L  voltage lifts over small groups, annealed to diameter <= D
#   X  C annealer (bitset cost, edge switches, vertex insertion) from the best graph
#   C  LNS from the best valid graph
#   D  redundant-edge pruning and regrowth
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

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
        n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.20)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.40):
        _lift_phase(d, D, lambda: best_n, at(0.40), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase X: C annealer from the best valid graph, with vertex insertion.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.86):
        budget = at(0.88) - time.monotonic() - 2.0  # margin for the one-off compile
        if budget >= 2.0:
            res = _c_search(d, D, seed, best_n, best_e, budget)
            if res is not None:
                consider(res[0], res[1])

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: LNS from the best valid graph of any construction.
    if D >= 2 and time.monotonic() < at(0.93):
        _lns(best_n, best_e, d, D, at(0.93), rng, consider)

    # Phase D: prune redundant edges and regrow from the best graph.
    if D >= 2 and time.monotonic() < at(0.99):
        _prune_regrow(best_n, best_e, d, D, at(0.99), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
