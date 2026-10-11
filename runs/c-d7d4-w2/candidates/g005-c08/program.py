import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley hill climbing over semidirect products Z_m x|_r Z_k.
#
# Parent idea (kept): vertices a_g, b_x in a group G of order N, edges
# a_g ~ b_{g*s} for a d-element set S. Left translations are automorphisms
# that are transitive on each side, so the diameter check reduces to BFS from
# a_e and b_e.
#
# New here: the whole search runs in C. Each group gets many more hill-climbing
# steps than the Python version could afford, and the engine sweeps N upward
# from the current best order and keeps the largest success.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define CAP 512
#define ITER 6000
#define GTRY 4

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static double cpu_secs(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int *g_adjA, *g_adjB, *g_degB, *g_dist, *g_q, *g_pw, *g_S;
static int g_N, g_m, g_k, g_d, g_D;
static double g_deadline;

static void set_group(int m, int k, int r) {
    g_m = m;
    g_k = k;
    g_N = m * k;
    for (int b = 0; b < k; b++) {
        if (b == 0) g_pw[0] = 1 % m;
        else g_pw[b] = (int)((long long)g_pw[b - 1] * r % m);
    }
}

/* (a,b)*(c,d) = (a + r^b c, b + d), element (a,b) coded a*k + b. */
static int mulg(int x, int y) {
    int a1 = x / g_k, b1 = x % g_k, c = y / g_k, d2 = y % g_k;
    return ((a1 + g_pw[b1] * c) % g_m) * g_k + (b1 + d2) % g_k;
}

static void build_adj(const int *S) {
    int N = g_N, d = g_d;
    for (int x = 0; x < N; x++) g_degB[x] = 0;
    for (int g = 0; g < N; g++) {
        for (int i = 0; i < d; i++) {
            int x = mulg(g, S[i]);
            g_adjA[g * d + i] = N + x;
            g_adjB[x * d + g_degB[x]] = g;
            g_degB[x]++;
        }
    }
}

/* Number of vertices farther than D from a_e or from b_e. */
static long cost_of(void) {
    int N = g_N, d = g_d, D = g_D, N2 = 2 * N;
    long total = 0;
    for (int si = 0; si < 2; si++) {
        int src = (si == 0) ? 0 : N;
        for (int v = 0; v < N2; v++) g_dist[v] = -1;
        int qh = 0, qt = 0;
        g_dist[src] = 0;
        g_q[qt++] = src;
        while (qh < qt) {
            int u = g_q[qh++];
            if (g_dist[u] >= D) continue;
            const int *nb = (u < N) ? &g_adjA[u * d] : &g_adjB[(u - N) * d];
            for (int i = 0; i < d; i++) {
                int v = nb[i];
                if (g_dist[v] < 0) {
                    g_dist[v] = g_dist[u] + 1;
                    g_q[qt++] = v;
                }
            }
        }
        total += N2 - qt;
    }
    return total;
}

static int in_set(const int *S, int cnt, int c) {
    for (int i = 0; i < cnt; i++) if (S[i] == c) return 1;
    return 0;
}

static int climb(int iters) {
    int N = g_N, d = g_d;
    for (int i = 0; i < d; i++) {
        int c;
        do { c = rndi(N); } while (in_set(g_S, i, c));
        g_S[i] = c;
    }
    build_adj(g_S);
    long cur = cost_of();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && cpu_secs() >= g_deadline) break;
        int i = rndi(d);
        int c = rndi(N);
        if (in_set(g_S, d, c)) continue;
        int old = g_S[i];
        g_S[i] = c;
        build_adj(g_S);
        long c2 = cost_of();
        if (c2 <= cur || (c2 == cur + 1 && rndi(20) == 0)) {
            cur = c2;
        } else {
            g_S[i] = old;
        }
    }
    return cur == 0;
}

static int cm[CAP], ck[CAP], cr[CAP];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [lo_n]\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int lo_n = (argc > 5) ? atoi(argv[5]) : 0;
    if (d < 2 || D < 2) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double t0 = cpu_secs();
    g_deadline = t0 + 0.8 * budget;

    double moore = 0.0;
    if (d == 2) {
        moore = 2.0 * D;
    } else {
        double p = 1.0;
        for (int i = 0; i < D; i++) { moore += p; p *= (d - 1); }
        moore *= 2.0;
    }
    long hi = (long)(moore / 2.0);
    if (hi > 4000) hi = 4000;
    long lo = lo_n / 2 + 1;
    if (lo < d) lo = d;
    if (hi < lo) { printf("0 0\n"); return 0; }

    int maxN = (int)hi;
    g_d = d;
    g_D = D;
    g_adjA = malloc(sizeof(int) * (size_t)maxN * d);
    g_adjB = malloc(sizeof(int) * (size_t)maxN * d);
    g_degB = malloc(sizeof(int) * (size_t)maxN);
    g_dist = malloc(sizeof(int) * (size_t)2 * maxN);
    g_q = malloc(sizeof(int) * (size_t)2 * maxN);
    g_pw = malloc(sizeof(int) * (size_t)maxN);
    g_S = malloc(sizeof(int) * (size_t)d);
    int *bestS = malloc(sizeof(int) * (size_t)d);
    if (!g_adjA || !g_adjB || !g_degB || !g_dist || !g_q || !g_pw || !g_S || !bestS) {
        printf("0 0\n");
        return 0;
    }

    long bestN = 0;
    int bm = 0, bk = 0, br = 0;

    for (long N = lo; N <= hi && cpu_secs() < g_deadline; N++) {
        int nc = 0;
        for (int k = 1; k <= N && nc < CAP; k++) {
            if (N % k) continue;
            int m = (int)(N / k);
            if (m == 1) {
                cm[nc] = 1; ck[nc] = k; cr[nc] = 0; nc++;
                continue;
            }
            for (int r = 1; r < m && nc < CAP; r++) {
                if (gcd_i(r, m) == 1 && powmod_i(r, k, m) == 1 % m) {
                    cm[nc] = m; ck[nc] = k; cr[nc] = r; nc++;
                }
            }
        }
        for (int i = nc - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int tm = cm[i]; cm[i] = cm[j]; cm[j] = tm;
            int tk = ck[i]; ck[i] = ck[j]; ck[j] = tk;
            int tr = cr[i]; cr[i] = cr[j]; cr[j] = tr;
        }
        int found = 0;
        for (int t = 0; t < nc && t < GTRY && !found; t++) {
            if (cpu_secs() >= g_deadline) break;
            set_group(cm[t], ck[t], cr[t]);
            if (climb(ITER)) {
                found = 1;
                bestN = N;
                bm = cm[t];
                bk = ck[t];
                br = cr[t];
                memcpy(bestS, g_S, sizeof(int) * (size_t)d);
            }
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    int N = (int)bestN;
    set_group(bm, bk, br);
    memcpy(g_S, bestS, sizeof(int) * (size_t)d);
    build_adj(g_S);
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + mulg(g, g_S[i]));
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
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
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
# Large-neighbourhood search (kill, repair, regrow), anchored to the best graph.
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
# Bi-Cayley graphs over small groups (Python fallback if the C engine fails).
# ----------------------------------------------------------------------------

def _groups_of_order(N):
    """All (m, k, r) with the semidirect product Z_m x|_r Z_k of order N = m*k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k; element (a, b) is coded a*k + b, identity 0."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    table = [[0] * N for _ in range(N)]
    for x in range(N):
        a1, b1 = divmod(x, k)
        row = table[x]
        for y in range(N):
            c, d2 = divmod(y, k)
            row[y] = ((a1 + pw[b1] * c) % m) * k + (b1 + d2) % k
    return table


def _bicayley_adj(N, table, S):
    """Adjacency lists of the bi-Cayley graph: a_g = g, b_x = N + x, a_g ~ b_{g*s}."""
    adj = [[] for _ in range(2 * N)]
    for g in range(N):
        row = table[g]
        ag = adj[g]
        for s in S:
            b = N + row[s]
            ag.append(b)
            adj[b].append(g)
    return adj


def _cayley_cost(adj, D):
    """Vertices farther than D from a_e or from b_e (both sources, both sides)."""
    total = 0
    N2 = len(adj)
    N = N2 // 2
    for src in (0, N):
        dist = [-1] * N2
        dist[src] = 0
        frontier = [src]
        cnt = 1
        for depth in range(1, D + 1):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = depth
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - cnt
    return total


def _climb(N, table, d, D, rng, iters, deadline):
    """Hill-climb a d-element generating set S minimising the Cayley cost. Returns S or None."""
    S = rng.sample(range(N), d)
    cur = _cayley_cost(_bicayley_adj(N, table, S), D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(N)
        if cand in S:
            continue
        newS = list(S)
        newS[i] = cand
        c2 = _cayley_cost(_bicayley_adj(N, table, newS), D)
        if c2 <= cur or (c2 == cur + 1 and rng.random() < 0.05):
            S, cur = newS, c2
    return S if cur == 0 else None


def _bicayley_search(d, D, rng, deadline, consider, lo_n):
    """Python bi-Cayley search of increasing order N (n = 2N) that beats lo_n vertices."""
    lo = max(d, lo_n // 2 + 1)
    hi = lib.moore_bound(d, D) // 2
    N = lo
    while N <= hi and time.monotonic() < deadline:
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:4]:
            if time.monotonic() >= deadline:
                break
            table = _group_table(m, k, r)
            S = _climb(N, table, d, D, rng, 200, deadline)
            if S is not None:
                edges = [(g, N + table[g][s]) for g in range(N) for s in S]
                consider(2 * N, edges)
                break
        N += 1


def _c_bicayley(d, D, seed, budget, lo_n, consider):
    """Run the C bi-Cayley engine for about `budget` seconds and offer its graph to consider."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", lo_n],
                     stdin_graph=None, timeout=budget + 15.0)
    n, edges = lib.parse_graph_text(text)
    if n > 0 and edges:
        consider(n, edges)


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

    # Already at the Moore bound: nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A (to 0.1 T): structured base, growth, and twin pipelines.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.05 * time_limit, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.1 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase C (0.1 T to 0.6 T): bi-Cayley search in C, with Python fallback.
    bi_end = start + 0.6 * time_limit
    if D >= 2 and d >= 2 and time.monotonic() < bi_end:
        budget = bi_end - time.monotonic()
        try:
            _c_bicayley(d, D, seed, budget, best_n, consider)
        except Exception:
            _bicayley_search(d, D, rng, bi_end, consider, best_n)

    # Phase B (0.6 T to 0.9 T): kill-repair-regrow from the best valid graph.
    if D >= 2 and time.monotonic() < deadline:
        _lns(best_n, best_e, d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
