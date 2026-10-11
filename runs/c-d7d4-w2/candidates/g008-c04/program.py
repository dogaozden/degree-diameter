import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: group-lift search.
#
# A lift of a base bipartite multigraph with a A-vertices and a B-vertices (each of
# degree d) over a group G of order M, with a semidirect product group
# Z_m x| Z_k. Vertex (u, x) for u in base A, x in G is joined to (v, x*g) for
# every dart (u, v, g). Left multiplication by G is an automorphism that acts
# regularly on each fibre, so distances from (w, e) represent all vertices of
# base vertex w. A valid graph therefore needs only 2a BFS runs per evaluation.
# Simulated annealing over dart endpoints (degree preserving swaps) and voltages
# minimises bad pairs. Orders are climbed one level at a time: level P means
# n = 2 * P vertices.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define AMAX 8

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_n(int n) { return (int)(rnext() % (uint64_t)n); }
static double runif(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int dd, DD, AA, MM;
static int *mul_ = NULL, *inv_ = NULL;
static int *ev_ = NULL, *gv_ = NULL, *bl_ = NULL, *bcnt_ = NULL;
static int *vis_ = NULL, *dist_ = NULL, *q_ = NULL;
static int stamp_ = 0;
static double deadline_wall = 0.0;
static int out_n = 0, out_m = 0;
static int *out_a = NULL, *out_b = NULL;

typedef struct { int a, m, k, r; } cfg_t;
static cfg_t *cfgs = NULL;
static int ncfg = 0, cfgcap = 0;

static int powmod_(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Element (p, q) is coded p*k+q; (p1,q1)(p2,q2) = (p1 + r^q1 * p2, q1 + q2). */
static void build_group(int m, int k, int r) {
    int M = m * k;
    int *pw = malloc(sizeof(int) * (size_t)k);
    for (int q = 0; q < k; q++) pw[q] = powmod_(r, q, m);
    for (int e1 = 0; e1 < M; e1++) {
        int p1 = e1 / k, q1 = e1 % k;
        for (int e2 = 0; e2 < M; e2++) {
            int p2 = e2 / k, q2 = e2 % k;
            int p = (int)(((long long)p1 + (long long)pw[q1] * p2) % m);
            int q = (q1 + q2) % k;
            mul_[e1 * M + e2] = p * k + q;
        }
    }
    for (int x = 0; x < M; x++) {
        inv_[x] = 0;
        for (int y = 0; y < M; y++) {
            if (mul_[x * M + y] == 0) { inv_[x] = y; break; }
        }
    }
    free(pw);
}

static void add_cfg(int a, int m, int k, int r) {
    if (ncfg == cfgcap) {
        cfgcap = cfgcap ? 2 * cfgcap : 64;
        cfgs = realloc(cfgs, sizeof(cfg_t) * (size_t)cfgcap);
    }
    cfgs[ncfg].a = a;
    cfgs[ncfg].m = m;
    cfgs[ncfg].k = k;
    cfgs[ncfg].r = r;
    ncfg++;
}

static void enumerate_cfgs(int P) {
    ncfg = 0;
    for (int a = 1; a <= AMAX && a <= P; a++) {
        if (P % a) continue;
        int M = P / a;
        for (int m = 1; m <= M; m++) {
            if (M % m) continue;
            int k = M / m;
            if (m == 1) { add_cfg(a, 1, k, 0); continue; }
            for (int r = 1; r < m; r++) {
                if (gcd_(r, m) != 1) continue;
                if (powmod_(r, k, m) != 1) continue;
                add_cfg(a, m, k, r);
            }
        }
    }
}

static void alloc_cfg(int a, int m, int k, int r) {
    AA = a;
    MM = m * k;
    int M = MM;
    int n = 2 * a * M;
    int nd = a * dd;
    mul_ = malloc(sizeof(int) * (size_t)M * (size_t)M);
    inv_ = malloc(sizeof(int) * (size_t)M);
    build_group(m, k, r);
    ev_ = malloc(sizeof(int) * (size_t)nd);
    gv_ = malloc(sizeof(int) * (size_t)nd);
    bl_ = malloc(sizeof(int) * (size_t)nd);
    bcnt_ = malloc(sizeof(int) * (size_t)a);
    vis_ = calloc((size_t)n, sizeof(int));
    dist_ = malloc(sizeof(int) * (size_t)n);
    q_ = malloc(sizeof(int) * (size_t)n);
    stamp_ = 0;
}

static void free_cfg(void) {
    free(mul_); free(inv_); free(ev_); free(gv_); free(bl_); free(bcnt_);
    free(vis_); free(dist_); free(q_);
    mul_ = inv_ = NULL;
    ev_ = gv_ = bl_ = bcnt_ = NULL;
    vis_ = dist_ = q_ = NULL;
}

/* Cost: ordered bad pairs from the 2a base representatives, plus heavy penalty for duplicate darts. */
static long long eval_cost(void) {
    const int a = AA, M = MM, d = dd, D = DD;
    const int n = 2 * a * M, nd = a * d, aM = a * M;
    long long dups = 0;
    for (int i = 0; i < nd; i++) {
        int ui = i / d;
        for (int j = 0; j < i; j++) {
            if (j / d == ui && ev_[j] == ev_[i] && gv_[j] == gv_[i]) dups++;
        }
    }
    for (int v = 0; v < a; v++) bcnt_[v] = 0;
    for (int i = 0; i < nd; i++) {
        int v = ev_[i];
        if (bcnt_[v] < d) bl_[v * d + bcnt_[v]++] = i;
    }
    long long bad = 0;
    for (int s = 0; s < 2 * a; s++) {
        int src = (s < a) ? s * M : aM + (s - a) * M;
        stamp_++;
        if (stamp_ == 0x7fffffff) {
            memset(vis_, 0, sizeof(int) * (size_t)n);
            stamp_ = 1;
        }
        int head = 0, tail = 0;
        vis_[src] = stamp_;
        dist_[src] = 0;
        q_[tail++] = src;
        while (head < tail) {
            int x = q_[head++];
            int dx = dist_[x];
            if (dx >= D) continue;
            if (x < aM) {
                int u = x / M, y = x % M;
                for (int j = 0; j < d; j++) {
                    int i = u * d + j;
                    int w = aM + ev_[i] * M + mul_[y * M + gv_[i]];
                    if (vis_[w] != stamp_) {
                        vis_[w] = stamp_;
                        dist_[w] = dx + 1;
                        q_[tail++] = w;
                    }
                }
            } else {
                int z = x - aM;
                int v = z / M, y = z % M;
                for (int j = 0; j < d; j++) {
                    int i = bl_[v * d + j];
                    int u = i / d;
                    int xx = mul_[y * M + inv_[gv_[i]]];
                    int w = u * M + xx;
                    if (vis_[w] != stamp_) {
                        vis_[w] = stamp_;
                        dist_[w] = dx + 1;
                        q_[tail++] = w;
                    }
                }
            }
        }
        bad += (long long)(n - tail);
    }
    return bad + 1000LL * dups;
}

static void init_state(void) {
    int nd = AA * dd;
    for (int i = 0; i < nd; i++) ev_[i] = i % AA;
    for (int i = nd - 1; i > 0; i--) {
        int j = rint_n(i + 1);
        int t = ev_[i]; ev_[i] = ev_[j]; ev_[j] = t;
    }
    for (int i = 0; i < nd; i++) gv_[i] = rint_n(MM);
}

static int run_sa(long long iters, double T0, double T1) {
    int nd = AA * dd;
    long long cur = eval_cost();
    if (cur == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 255) == 0 && now_s() > deadline_wall) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int type = (nd > 1 && runif() < 0.5);
        int i = 0, j = 0, old = 0;
        if (type) {
            i = rint_n(nd);
            j = rint_n(nd);
            if (i == j || ev_[i] == ev_[j]) continue;
            int t = ev_[i]; ev_[i] = ev_[j]; ev_[j] = t;
        } else {
            if (MM <= 1) continue;
            i = rint_n(nd);
            old = gv_[i];
            int nv = rint_n(MM);
            if (nv == old) continue;
            gv_[i] = nv;
        }
        long long nw = eval_cost();
        long long delta = nw - cur;
        if (delta <= 0 || runif() < exp(-(double)delta / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            if (type) {
                int t = ev_[i]; ev_[i] = ev_[j]; ev_[j] = t;
            } else {
                gv_[i] = old;
            }
        }
    }
    return 0;
}

static void store_solution(void) {
    int a = AA, M = MM, d = dd, nd = a * d;
    int m = nd * M;
    free(out_a);
    free(out_b);
    out_a = malloc(sizeof(int) * (size_t)m);
    out_b = malloc(sizeof(int) * (size_t)m);
    int k = 0;
    for (int i = 0; i < nd; i++) {
        int u = i / d, v = ev_[i], g = gv_[i];
        for (int x = 0; x < M; x++) {
            out_a[k] = u * M + x;
            out_b[k] = a * M + v * M + mul_[x * M + g];
            k++;
        }
    }
    out_n = 2 * a * M;
    out_m = m;
}

static int search_level(int P, double deadline, int d) {
    enumerate_cfgs(P);
    if (ncfg == 0) return 0;
    dd = d;
    while (now_s() < deadline) {
        cfg_t c = cfgs[rint_n(ncfg)];
        deadline_wall = deadline;
        alloc_cfg(c.a, c.m, c.k, c.r);
        init_state();
        int ok = run_sa(100000, 2.0, 0.2);
        if (ok) {
            store_solution();
            free_cfg();
            return 1;
        }
        free_cfg();
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed budget P0\n");
        return 1;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int P0 = atoi(argv[5]);
    rs = (uint64_t)seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnext();
    dd = d;
    DD = D;

    double t0 = now_s();
    double end = t0 + 0.92 * budget;

    double mo = 0.0, term = 1.0;
    for (int i = 0; i < D; i++) { mo += term; term *= (double)(d - 1); }
    mo *= 2.0;
    int Pmax = (int)(mo / 2.0) + 1;

    int P = P0 < 1 ? 1 : P0;
    if (Pmax > P + 400) Pmax = P + 400;

    int fails = 0;
    while (P <= Pmax && fails < 3) {
        double t = now_s();
        double rem = end - t;
        if (rem < 0.5) break;
        double lvl = 0.3 * rem;
        if (lvl > 10.0) lvl = 10.0;
        if (search_level(P, t + lvl, d)) fails = 0;
        else fails++;
        P++;
    }

    if (out_n > 0) {
        printf("%d %d\n", out_n, out_m);
        for (int k = 0; k < out_m; k++) printf("%d %d\n", out_a[k], out_b[k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Parent pipeline (kept as the safe fallback for the structured/grown graphs).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _local_kill(n, adj, k, rng):
    """Pick k vertices forming a connected cluster (BFS-like from a random seed vertex)."""
    v = rng.randrange(n)
    kill = {v}
    frontier = [v]
    while len(kill) < k and frontier:
        x = frontier.pop(rng.randrange(len(frontier)))
        nb = list(adj[x])
        rng.shuffle(nb)
        for u in nb:
            if len(kill) >= k:
                break
            if u not in kill:
                kill.add(u)
                frontier.append(u)
    while len(kill) < k:
        kill.add(rng.randrange(n))
    return kill


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        if rng.random() < 0.6:
            full_adj = _to_sets(cur_n, cur_e)
            kill = _local_kill(cur_n, full_adj, k, rng)
        else:
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
            pe = _prune_redundant(m, e, D, rng, deadline, 200)
            adj = _to_sets(m, pe)
            color = _bipartition(m, adj)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.55 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        prune_end = start + 0.75 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


# ----------------------------------------------------------------------------
# Entry point: group-lift search (new construction) plus the parent pipeline
# as a safety net. The best valid graph of the two is returned.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    lift_budget = 0.40 * time_limit
    parent_budget = 0.50 * time_limit

    # 1. Group-lift search, starting at about 0.67 of the Moore bound.
    p0 = max(1, int(0.67 * lib.moore_bound(d, D)) // 2)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{lift_budget:.2f}", p0],
                        timeout=lift_budget + 25.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    # 2. Parent pipeline as the safe fallback.
    try:
        n, e = _parent_build(d, D, seed, parent_budget)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
