# New stage: a C voltage-lift annealer. It searches Z_m, Z_k and Z_m x|_r Z_k lifts of
# small bipartite base graphs (a in 1..4 on each side, degree d). Each group element
# acts by right multiplication, so left translation is an automorphism, and the
# diameter is checked exactly with BFS from the 2a representatives. Darts are annealed
# by voltage changes and by endpoint swaps, which keep all degrees fixed. The search
# runs in C, starts from the best Python graph, and only accepts lifts larger than the
# current best. The parent's GQ/PG, twin-duplication, LNS and prune stages remain as
# the fallback and post-processing.
import itertools
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

#define MAXA 4
#define MAXG 1500
#define POOLCAP 200000
#define WIN 40
#define ITERS 4000

typedef struct { int m, k, r; } GSpec;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int GM = 1, GK = 1, G = 1;
static int *pw = NULL, *RT = NULL, *RI = NULL;

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long long aa = ((long long)a + (long long)pw[b] * c) % GM;
    return (int)aa * GK + (b + e) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m; GK = k; G = m * k;
    free(pw);
    pw = malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    free(RT); free(RI);
    RT = malloc(sizeof(int) * (size_t)G * G);
    RI = malloc(sizeof(int) * (size_t)G * G);
    for (int g = 0; g < G; g++)
        for (int x = 0; x < G; x++) RT[g * G + x] = gmul(x, g);
    for (int g = 0; g < G; g++)
        for (int x = 0; x < G; x++) RI[g * G + RT[g * G + x]] = x;
}

/* Lift state: a A-vertices, a B-vertices, LT = a*d darts. Dart t joins A-vertex t/d
   to B-vertex perm[t] with voltage dg[t]. */
static int LA = 1, LD = 1, LT = 1;
static int *perm = NULL, *dg = NULL, *bd = NULL;
static int *stamp = NULL, *qbuf = NULL;
static int stamp_cur = 0;
static int STAMP_N = 2 * MAXA * MAXG + 8;

static void rebuild_bd(void) {
    for (int j = 0; j < LA; j++) {
        int s = 0;
        for (int t = 0; t < LT; t++)
            if (perm[t] == j) bd[j * LD + s++] = t;
    }
}

static void init_darts(int a, int d) {
    LA = a; LD = d; LT = a * d;
    for (int t = 0; t < LT; t++) perm[t] = t / d;
    for (int t = LT - 1; t > 0; t--) {
        int r = rndi(t + 1);
        int tmp = perm[t]; perm[t] = perm[r]; perm[r] = tmp;
    }
    for (int t = 0; t < LT; t++) dg[t] = rndi(G);
    rebuild_bd();
}

/* Sum over the 2a representatives of the number of vertices at distance > D. */
static long long lift_cost(int D) {
    int a = LA, d = LD;
    int AN = a * G, N = 2 * a * G;
    long long total = 0;
    for (int s = 0; s < 2 * a; s++) {
        int src = (s < a) ? s * G : AN + (s - a) * G;
        if (stamp_cur >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)STAMP_N);
            stamp_cur = 0;
        }
        stamp_cur++;
        int head = 0, tail = 0;
        qbuf[tail++] = src;
        stamp[src] = stamp_cur;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qbuf[head++];
                if (u < AN) {
                    int i = u / G, x = u % G;
                    for (int q = 0; q < d; q++) {
                        int t = i * d + q;
                        int v = AN + perm[t] * G + RT[dg[t] * G + x];
                        if (stamp[v] != stamp_cur) { stamp[v] = stamp_cur; qbuf[tail++] = v; }
                    }
                } else {
                    int w = u - AN, j = w / G, y = w % G;
                    for (int q = 0; q < d; q++) {
                        int t = bd[j * d + q];
                        int v = (t / d) * G + RI[dg[t] * G + y];
                        if (stamp[v] != stamp_cur) { stamp[v] = stamp_cur; qbuf[tail++] = v; }
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long long anneal(int D, int iters, double dl) {
    long long cur = lift_cost(D);
    for (int it = 0; it < iters && cur > 0; it++) {
        if (wall() > dl) break;
        double temp = 0.3 + 2.0 * (1.0 - (double)it / (double)iters);
        if (rndi(10) < 6) {
            int t = rndi(LT);
            int old = dg[t];
            int ng = rndi(G);
            if (ng == old) continue;
            dg[t] = ng;
            long long nc = lift_cost(D);
            if (nc <= cur || rndu() < exp(-(double)(nc - cur) / temp)) cur = nc;
            else dg[t] = old;
        } else {
            int t1 = rndi(LT), t2 = rndi(LT);
            if (perm[t1] == perm[t2]) continue;
            int tmp = perm[t1]; perm[t1] = perm[t2]; perm[t2] = tmp;
            rebuild_bd();
            long long nc = lift_cost(D);
            if (nc <= cur || rndu() < exp(-(double)(nc - cur) / temp)) cur = nc;
            else {
                tmp = perm[t1]; perm[t1] = perm[t2]; perm[t2] = tmp;
                rebuild_bd();
            }
        }
    }
    return cur;
}

static int cmp_ll(const void *x, const void *y) {
    long long a = *(const long long *)x, b = *(const long long *)y;
    return (a > b) - (a < b);
}

static int best_n = 0, best_m = 0;
static int *best_u = NULL, *best_v = NULL;

static void store_best(int n, int m, int *u, int *v) {
    free(best_u); free(best_v);
    best_n = n; best_m = m; best_u = u; best_v = v;
}

static void store_lift(void) {
    int a = LA, d = LD, AN = a * G, N = 2 * a * G;
    long long *codes = malloc(sizeof(long long) * (size_t)LT * (size_t)G);
    long long nc = 0;
    for (int t = 0; t < LT; t++) {
        int i = t / d, j = perm[t], g = dg[t];
        for (int x = 0; x < G; x++) {
            long long u = (long long)i * G + x;
            long long v = (long long)AN + (long long)j * G + RT[g * G + x];
            codes[nc++] = u * N + v;
        }
    }
    qsort(codes, (size_t)nc, sizeof(long long), cmp_ll);
    long long m = 0, prev = -1;
    for (long long k = 0; k < nc; k++) {
        if (codes[k] != prev) { codes[m++] = codes[k]; prev = codes[k]; }
    }
    int *u = malloc(sizeof(int) * (size_t)(m + 1));
    int *v = malloc(sizeof(int) * (size_t)(m + 1));
    for (long long k = 0; k < m; k++) {
        u[k] = (int)(codes[k] / N);
        v[k] = (int)(codes[k] % N);
    }
    free(codes);
    store_best(N, (int)m, u, v);
}

static GSpec *pool = NULL;

static int build_pool(int lo, int hi) {
    int np = 0;
    for (int o = lo; o <= hi && np < POOLCAP; o++) {
        pool[np].m = o; pool[np].k = 1; pool[np].r = 1; np++;
    }
    for (int k = 2; k <= hi / 2; k++) {
        for (int m = 2; m * k <= hi; m++) {
            int o = m * k;
            if (o < lo) continue;
            for (int r = 1; r < m && np < POOLCAP; r++) {
                if (gcd_i(r, m) != 1) continue;
                long long p = 1 % m;
                for (int e = 0; e < k; e++) p = p * r % m;
                if (p != 1 % m) continue;
                pool[np].m = m; pool[np].k = k; pool[np].r = r; np++;
            }
        }
    }
    return np;
}

static double moore_bound(int d, int D) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return D >= 1 ? 2 : 1;
    if (d == 2) return 2.0 * D;
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (double)(d - 1);
        if (s > 1e15) break;
    }
    return 2.0 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: d D seed time_limit\n"); return 1; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double dl = wall() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0) m0 = 0;
    int *su = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *sv = malloc(sizeof(int) * (size_t)(m0 + 1));
    int cnt = 0;
    for (int e = 0; e < m0; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        su[cnt] = u; sv[cnt] = v; cnt++;
    }
    if (n0 > 0 && cnt == m0) store_best(n0, cnt, su, sv);
    else { free(su); free(sv); }

    if (d >= 1 && D >= 1) {
        perm = malloc(sizeof(int) * (size_t)(MAXA * d));
        dg = malloc(sizeof(int) * (size_t)(MAXA * d));
        bd = malloc(sizeof(int) * (size_t)(MAXA * d));
        stamp = calloc((size_t)STAMP_N, sizeof(int));
        qbuf = malloc(sizeof(int) * (size_t)STAMP_N);
        pool = malloc(sizeof(GSpec) * POOLCAP);
        double moore = moore_bound(d, D);

        while (wall() < dl && best_n < moore) {
            int a = 1 + rndi(MAXA);
            long long lo = best_n / (2LL * a) + 1;
            if (lo < 2) lo = 2;
            long long hi = (long long)floor(moore / (2.0 * a));
            if (hi > lo + WIN) hi = lo + WIN;
            if (hi > MAXG) hi = MAXG;
            if (hi < lo) {
                int any = 0;
                for (int b = 1; b <= MAXA; b++) {
                    long long l2 = best_n / (2LL * b) + 1;
                    if (l2 < 2) l2 = 2;
                    long long h2 = (long long)floor(moore / (2.0 * b));
                    if (h2 > MAXG) h2 = MAXG;
                    if (l2 <= h2) any = 1;
                }
                if (!any) break;
                continue;
            }
            int np = build_pool((int)lo, (int)hi);
            if (np == 0) continue;
            GSpec s = pool[rndi(np)];
            set_group(s.m, s.k, s.r);
            for (int att = 0; att < 2 && wall() < dl; att++) {
                init_darts(a, d);
                long long c = anneal(D, ITERS, dl);
                if (c == 0) {
                    if (2 * a * G > best_n) store_lift();
                    break;
                }
            }
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int k = 0; k < best_m; k++) printf("%d %d\n", best_u[k], best_v[k]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases (parent pipeline).
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
# Large-neighbourhood search (kill, repair, regrow).
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
# Redundant-edge pruning, then regrow.
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random redundant edges (keeping diameter <= D). Returns the pruned edge list."""
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
    """Repeatedly prune redundant edges, regrow with cover vertices, keep the best."""
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

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

    # Stage 1: structured base (generalized quadrangle for D >= 4, projective plane for D = 3).
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * T, rng)
            consider(n1, e1)
    if best_n >= moore:
        return best_n, list(best_e)

    # Stage 2: randomized twin-duplication pipelines from the structured base.
    trial_end = start + 0.20 * T
    while time.monotonic() < trial_end and best_n < moore:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Stage 3 (new): C voltage-lift annealer, seeded with the best graph so far.
    c_end = start + 0.78 * T
    budget = c_end - time.monotonic() - 1.0
    remaining = T - (time.monotonic() - start) - 1.5
    if budget > 1.0 and remaining > 1.0 and best_n < moore:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=(best_n, best_e),
                             timeout=min(budget + 5.0, remaining))
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    # Stage 4: kill-repair-regrow search from the best valid graph.
    lns_end = start + 0.85 * T
    if time.monotonic() < lns_end and best_n < moore:
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Stage 5: prune redundant edges to free degree, then regrow.
    prune_end = start + 0.88 * T
    if time.monotonic() < prune_end and best_n < moore:
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
