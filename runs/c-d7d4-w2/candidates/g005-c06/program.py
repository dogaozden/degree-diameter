import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

/* Searches 2+2 voltage lifts over semidirect products Z_m x|_r Z_k.
   Base: A0, A1, B0, B1. Pair (i,j) carries cnt[2i+j] distinct voltages with
   cnt = (a, d-a, d-a, a). Lift vertices: A_{i,x} = i*N+x, B_{j,y} = 2N+j*N+y,
   edge A_{i,x} ~ B_{j, x*g} for each voltage g on pair (i,j).
   Left multiplication is an automorphism, so the diameter is certified by BFS
   from the four representatives A0,e  A1,e  B0,e  B1,e. Cost = sum of unreached
   counts within radius D. Output: best valid lift found, or "0 0". */

#define MAXD 32
#define MAXGROUPS 8192
#define ITERS 6000
#define REPS 2

static int dd, DD;
static clock_t t_start;
static double budget_s, slice_end;
static unsigned long long rs = 1;

static unsigned long long rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (unsigned long long)n); }
static double rnd01(void) { return (double)(rnd() >> 11) / 9007199254740992.0; }

static double elapsed(void) { return (double)(clock() - t_start) / CLOCKS_PER_SEC; }
static int time_left(void) { return elapsed() < slice_end; }

static int N;
static int *mt = NULL;
static int cnt[4];
static int vg[4][MAXD];
static int *adjv = NULL, *degv = NULL, *distv = NULL, *qv = NULL;

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
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

/* Element (a,b) is coded a*k+b; (a,b)(c,d) = (a + r^b c, b + d). */
static void make_group(int m, int k, int r) {
    N = m * k;
    free(mt);
    mt = malloc(sizeof(int) * (size_t)N * N);
    int *pw = malloc(sizeof(int) * k);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, d2 = y % k;
            int aa = (int)((a1 + (long long)pw[b1] * c) % m);
            mt[x * N + y] = aa * k + (b1 + d2) % k;
        }
    }
    free(pw);
}

static void build_adj(void) {
    int V = 4 * N;
    for (int v = 0; v < V; v++) degv[v] = 0;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) {
            int p = 2 * i + j;
            for (int t = 0; t < cnt[p]; t++) {
                int g = vg[p][t];
                for (int x = 0; x < N; x++) {
                    int u = i * N + x;
                    int v = 2 * N + j * N + mt[x * N + g];
                    adjv[u * dd + degv[u]++] = v;
                    adjv[v * dd + degv[v]++] = u;
                }
            }
        }
}

static long long cost_fn(void) {
    build_adj();
    int V = 4 * N;
    int srcs[4] = {0, N, 2 * N, 3 * N};
    long long total = 0;
    for (int s = 0; s < 4; s++) {
        for (int v = 0; v < V; v++) distv[v] = -1;
        int h = 0, tl = 0;
        distv[srcs[s]] = 0;
        qv[tl++] = srcs[s];
        while (h < tl) {
            int u = qv[h++];
            if (distv[u] >= DD) continue;
            for (int q = 0; q < degv[u]; q++) {
                int w = adjv[u * dd + q];
                if (distv[w] < 0) {
                    distv[w] = distv[u] + 1;
                    qv[tl++] = w;
                }
            }
        }
        total += V - tl;
    }
    return total;
}

static int in_prefix(int p, int g, int len) {
    for (int t = 0; t < len; t++)
        if (vg[p][t] == g) return 1;
    return 0;
}

static void random_init(void) {
    for (int p = 0; p < 4; p++) {
        for (int t = 0; t < cnt[p]; t++) {
            int g;
            do {
                g = rndint(N);
            } while (in_prefix(p, g, t));
            vg[p][t] = g;
        }
    }
}

static long long anneal(int iters) {
    random_init();
    long long cur = cost_fn();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && !time_left()) break;
        int p = rndint(4);
        if (cnt[p] == 0) continue;
        int t = rndint(cnt[p]);
        int g = rndint(N);
        if (in_prefix(p, g, cnt[p])) continue;
        int old = vg[p][t];
        vg[p][t] = g;
        long long nc = cost_fn();
        double T = 1.5 * (1.0 - (double)it / iters) + 0.05;
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T))
            cur = nc;
        else
            vg[p][t] = old;
    }
    return cur;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    int nmin = atoi(argv[5]), nmax = atoi(argv[6]);
    if (dd < 2 || dd > MAXD || DD < 2 || nmin < 1 || nmax < 1 || nmax > 4000) {
        printf("0 0\n");
        return 0;
    }
    if (nmin < dd) nmin = dd;
    if (nmax < nmin) {
        printf("0 0\n");
        return 0;
    }
    t_start = clock();
    int maxV = 4 * nmax;
    adjv = malloc(sizeof(int) * (size_t)maxV * dd);
    degv = malloc(sizeof(int) * maxV);
    distv = malloc(sizeof(int) * maxV);
    qv = malloc(sizeof(int) * maxV);

    static int gM[MAXGROUPS], gK[MAXGROUPS], gR[MAXGROUPS], ord[MAXGROUPS];
    static int bestvg[4][MAXD];
    int have_best = 0, bestm = 0, bestk = 0, bestr = 0, besta = 0;

    for (int NN = nmin; NN <= nmax; NN++) {
        double now = elapsed();
        if (now >= budget_s) break;
        slice_end = now + (budget_s - now) / (double)(nmax - NN + 1);

        int gc = 0;
        for (int k = 1; k <= NN && gc < MAXGROUPS; k++) {
            if (NN % k) continue;
            int m = NN / k;
            if (m == 1) {
                gM[gc] = 1;
                gK[gc] = k;
                gR[gc] = 0;
                gc++;
                continue;
            }
            for (int r = 1; r < m && gc < MAXGROUPS; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_i(r, k, m) != 1) continue;
                gM[gc] = m;
                gK[gc] = k;
                gR[gc] = r;
                gc++;
            }
        }
        for (int i = 0; i < gc; i++) ord[i] = i;
        shuffle_int(ord, gc);

        int found = 0;
        for (int gi = 0; gi < gc && !found && time_left(); gi++) {
            int g = ord[gi];
            make_group(gM[g], gK[g], gR[g]);
            int alist[MAXD], na = 0;
            for (int a = 1; a < dd; a++) alist[na++] = a;
            shuffle_int(alist, na);
            for (int ai = 0; ai < na && !found && time_left(); ai++) {
                int a = alist[ai];
                cnt[0] = a;
                cnt[1] = dd - a;
                cnt[2] = dd - a;
                cnt[3] = a;
                for (int rep = 0; rep < REPS && !found && time_left(); rep++) {
                    if (anneal(ITERS) == 0) {
                        found = 1;
                        have_best = 1;
                        bestm = gM[g];
                        bestk = gK[g];
                        bestr = gR[g];
                        besta = a;
                        memcpy(bestvg, vg, sizeof(vg));
                    }
                }
            }
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    make_group(bestm, bestk, bestr);
    int a = besta;
    cnt[0] = a;
    cnt[1] = dd - a;
    cnt[2] = dd - a;
    cnt[3] = a;
    memcpy(vg, bestvg, sizeof(vg));
    int E = 2 * N * dd;
    printf("%d %d\n", 4 * N, E);
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) {
            int p = 2 * i + j;
            for (int t = 0; t < cnt[p]; t++) {
                int gv = vg[p][t];
                for (int x = 0; x < N; x++)
                    printf("%d %d\n", i * N + x, 2 * N + j * N + mt[x * N + gv]);
            }
        }
    return 0;
}
"""


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
# Bold construction: 2+2 voltage lifts over semidirect products (C search).
#
# Base graph has two vertices per side and a 2x2 dart-count pattern
# (a, d-a; d-a, a). Each dart is a group element; the lift has 4N vertices and
# is d-regular. Left multiplication is an automorphism, so the diameter is
# certified from four BFS trees. This is a different family from the
# one-vertex-per-side bi-Cayley graphs (order 2N) used before.
# ----------------------------------------------------------------------------

def _lift_search(d, D, seed, budget, nmin, nmax):
    """Run the C lift search for group orders nmin..nmax. Returns (n, edges) or None."""
    if nmin > nmax or budget < 2:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", nmin, nmax],
                        timeout=budget + 3)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 1:
        return None
    return n, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D < 2 or d < 2:
        return best_n, list(best_e)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A (to 0.1 T): structured base, grown by cover vertices.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            consider(base[0], base[1])
            n1, e1 = _grow(base[0], base[1], d, D, start + 0.1 * time_limit, rng)
            consider(n1, e1)

    # Phase C (to 0.7 T): bold change, 2+2 voltage lifts over semidirect products.
    # Lift order is 4N, so only group orders N with 4N > best_n are useful.
    lift_end = start + 0.7 * time_limit
    nmin = best_n // 4 + 1
    nmax = lib.moore_bound(d, D) // 4
    budget = lift_end - time.monotonic()
    if budget > 3 and nmin <= nmax:
        res = _lift_search(d, D, seed, budget - 1.0, nmin, nmax)
        if res is not None:
            consider(res[0], res[1])

    # Phase B (to 0.9 T): kill-repair-regrow from the best valid graph.
    deadline = start + 0.9 * time_limit
    _lns(best_n, best_e, d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
