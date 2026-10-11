import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Voltage-lift search over bipartite base graphs with P vertices per side.
   Base: A_i -- B_{(i+t)%P} for t = 0..DEG-1, voltage gv[t][i] in a finite group G of order N.
   Lift: vertices (block, x), block < 2P, x in G; A_i,x ~ B_j,x*g.
   G acts on each fibre by left multiplication, so BFS from (A_i,e) and (B_j,e) suffices. */

#define MAXN 8192
#define MAXDEG 16
#define MAXP 4
#define MAXG 1024
#define MAXE 70000
#define MAXCAND 4096
#define ITERS 40000L

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int DEG, DD, P, NG, NV;
static int gmul[MAXG][MAXG];
static int ginv[MAXG];
static int gv[MAXDEG][MAXP];
static int distv[MAXN];
static int que[MAXN];
static int cand_m[MAXCAND], cand_k[MAXCAND], cand_r[MAXCAND];
static int ncand;
static int bestE_u[MAXE], bestE_v[MAXE], bestM;
static int best_n;
static int found;
static clock_t t0;
static double TL;

static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static long long gcd_ll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long long moore_bound(int d, int D) {
    if (D == 0 || d == 0) return 1;
    if (d == 1) return D >= 1 ? 2 : 1;
    if (d == 2) return 2LL * D;
    long long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        pw *= (d - 1);
    }
    return 2 * s;
}

/* Semidirect product Z_m x| Z_k, element a*k+b, (a,b)(c,d) = (a + r^b c, b + d). k=1 gives Z_m. */
static void make_group(int m, int k, int r) {
    int pw[MAXG];
    for (int b = 0; b < k; b++) {
        long long v = 1 % m;
        for (int t = 0; t < b; t++) v = v * r % m;
        pw[b] = (int)v;
    }
    int N = m * k;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, d = y % k;
            int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
            gmul[x][y] = aa * k + (b + d) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (gmul[x][y] == 0) {
                ginv[x] = y;
                break;
            }
    NG = N;
}

static void enum_groups(int N) {
    ncand = 0;
    for (int k = 1; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        int rmax = (m == 1) ? 0 : m - 1;
        for (int r = 0; r <= rmax && ncand < MAXCAND; r++) {
            if (gcd_ll(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cand_m[ncand] = m;
            cand_k[ncand] = k;
            cand_r[ncand] = r;
            ncand++;
        }
    }
}

/* 1 if assigning voltage g to dart (t,i) clashes with another dart t2 < upto in the same pair. */
static int conflict(int t, int i, int g, int upto) {
    for (int t2 = 0; t2 < upto; t2++) {
        if (t2 == t) continue;
        if (t2 % P != t % P) continue;
        if (gv[t2][i] == g) return 1;
    }
    return 0;
}

/* Number of (source, vertex) pairs at distance > DD, over the 2P representative sources. */
static int bfs_cost(void) {
    int total = 0;
    int nsrc = 2 * P;
    for (int s = 0; s < nsrc; s++) {
        for (int v = 0; v < NV; v++) distv[v] = -1;
        int head = 0, tail = 0, reached = 1;
        int src = s * NG;
        distv[src] = 0;
        que[tail++] = src;
        while (head < tail) {
            int v = que[head++];
            int dv = distv[v];
            if (dv >= DD) continue;
            int blk = v / NG, x = v % NG;
            if (blk < P) {
                int i = blk;
                for (int t = 0; t < DEG; t++) {
                    int j = (i + t) % P;
                    int y = gmul[x][gv[t][i]];
                    int w = (P + j) * NG + y;
                    if (distv[w] < 0) {
                        distv[w] = dv + 1;
                        que[tail++] = w;
                        reached++;
                    }
                }
            } else {
                int j = blk - P;
                for (int t = 0; t < DEG; t++) {
                    int i = ((j - t) % P + P) % P;
                    int y = gmul[x][ginv[gv[t][i]]];
                    int w = i * NG + y;
                    if (distv[w] < 0) {
                        distv[w] = dv + 1;
                        que[tail++] = w;
                        reached++;
                    }
                }
            }
        }
        total += NV - reached;
    }
    return total;
}

static int init_volt(void) {
    for (int t = 0; t < DEG; t++)
        for (int i = 0; i < P; i++) {
            int ok = 0;
            for (int tries = 0; tries < 200; tries++) {
                int g = rndint(NG);
                if (!conflict(t, i, g, t)) {
                    gv[t][i] = g;
                    ok = 1;
                    break;
                }
            }
            if (!ok) return 0;
        }
    return 1;
}

static int anneal(long iters, double T0, double T1, double tlimit) {
    int cur = bfs_cost();
    if (cur == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 255) == 0 && elapsed() > tlimit) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int t = rndint(DEG), i = rndint(P);
        int g = rndint(NG);
        if (g == gv[t][i]) continue;
        if (conflict(t, i, g, DEG)) continue;
        int old = gv[t][i];
        gv[t][i] = g;
        int nc = bfs_cost();
        int diff = nc - cur;
        if (diff <= 0 || rnd01() < exp(-(double)diff / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            gv[t][i] = old;
        }
    }
    return cur == 0;
}

static void store_best(void) {
    int m = 0;
    for (int i = 0; i < P; i++)
        for (int t = 0; t < DEG; t++)
            for (int x = 0; x < NG; x++) {
                int j = (i + t) % P;
                int u = i * NG + x;
                int v = (P + j) * NG + gmul[x][gv[t][i]];
                if (m < MAXE) {
                    bestE_u[m] = u;
                    bestE_v[m] = v;
                    m++;
                }
            }
    bestM = m;
    best_n = NV;
    found = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    int lo = (argc > 5) ? atoi(argv[5]) : 2 * DEG;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    t0 = clock();
    best_n = lo;
    found = 0;
    bestM = 0;
    if (DEG < 3 || DD < 2 || DEG > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    long long moore = moore_bound(DEG, DD);
    long long cap = moore < MAXN ? moore : MAXN;
    while (elapsed() < TL - 0.3 && best_n + 2 <= cap) {
        P = 1 + rndint(MAXP);
        long long Nmax = cap / (2LL * P);
        if (Nmax > MAXG) Nmax = MAXG;
        long long Nmin = best_n / (2 * P) + 1;
        if (Nmin > Nmax) continue;
        int N = (int)Nmin + rndint(3);
        if (N > Nmax) N = (int)Nmax;
        enum_groups(N);
        if (ncand == 0) continue;
        int c = rndint(ncand);
        make_group(cand_m[c], cand_k[c], cand_r[c]);
        NV = 2 * P * NG;
        if (NG < (DEG + P - 1) / P) continue;
        if (!init_volt()) continue;
        if (anneal(ITERS, 2.0, 0.1, TL - 0.2)) store_best();
    }
    if (found) {
        printf("%d %d\n", best_n, bestM);
        for (int k = 0; k < bestM; k++) printf("%d %d\n", bestE_u[k], bestE_v[k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (unchanged from the parent).
# ----------------------------------------------------------------------------

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
# Large-neighbourhood search (kill, repair, regrow).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


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


def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Voltage-lift search (new engine, run in C).
# ----------------------------------------------------------------------------

def _lift_search(d, D, seed, budget, lo):
    """Run the C lift search for at most `budget` seconds. Returns a valid (n, edges) with n > lo, or None."""
    if d < 3 or D < 2 or budget < 1.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", lo], timeout=budget + 5.0)
        n, edges = lib.parse_graph_text(out)
    except Exception:
        return None
    if n <= lo or not lib.is_valid(n, edges, d, D):
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    moore = lib.moore_bound(d, D)

    # Structured base (generalized quadrangle for D >= 4, projective plane for D = 3).
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Bold stage: voltage lifts over small bipartite bases, searched in C.
    if D >= 2 and best_n < moore and time.monotonic() < start + 0.5 * time_limit:
        budget = start + 0.5 * time_limit - time.monotonic() - 1.5
        lift = _lift_search(d, D, seed, budget, best_n)
        if lift is not None:
            consider(*lift)

    # Twin-duplication pipelines from the best graph so far.
    if D >= 2 and best_n < moore:
        trial_end = start + 0.6 * time_limit
        stall = 0
        while time.monotonic() < trial_end and stall < 25:
            before = best_n
            n, e = _trial(best_n, list(best_e), d, D, rng, trial_end)
            consider(n, e)
            stall = 0 if best_n > before else stall + 1

    # Kill-repair-regrow search.
    if D >= 2 and best_n < moore and time.monotonic() < deadline:
        _lns(best_n, list(best_e), d, D, start + 0.8 * time_limit, rng, consider)

    # Add-and-repair from the largest valid graph found so far.
    if D >= 2 and best_n < moore and time.monotonic() < deadline:
        _repair(d, D, best_n, list(best_e), deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
