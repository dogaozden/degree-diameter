import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift search over semidirect products Z_m x| Z_k.
#
# A base graph has s vertices on side A and s on side B, with d darts per base
# vertex. Dart (u, v, g) joins (u, x) to (v, x*g) for every group element x.
# Left multiplication by any h is an automorphism, so the bad-pair count only
# needs BFS from the 2s identity representatives. Simulated annealing over
# voltages and endpoint swaps. Every lift that reaches cost 0 is expanded and
# checked with a full validator before it is kept. The program prints the best
# valid graph it has (at least the input graph, if that was valid).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXS 128
#define MAXL 8000
#define MAXOUT 20000

static int dd, D, s, N, S;
static int du[MAXS], dv[MAXS], dg[MAXS], sv[MAXS], sg[MAXS];
static int lstB[MAXS];
static int mt[MAXN * MAXN];
static int ginv[MAXN];
static int pw[16];
static int vis[MAXL], que[MAXL];
static int stamp = 0, lift_n = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double budget = 1.0;
static int best_n = 0, best_m = 0;
static int *best_eu = NULL, *best_ev = NULL;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(nextr() % (uint64_t)n); }

static double rnd01(void) { return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

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

static double moore_bound(void) {
    double sum = 0.0, p = 1.0;
    for (int i = 0; i < D; i++) { sum += p; p *= (double)(dd - 1); }
    return 2.0 * sum;
}

/* 1 iff simple, max degree <= dd, bipartite and diameter <= D. */
static int check_graph(int n, int m, const int *eu, const int *ev) {
    int ok = 1;
    if (n < 1 || n > MAXOUT || m < 0) return 0;
    int *deg = calloc((size_t)n, sizeof(int));
    int *fill = calloc((size_t)n, sizeof(int));
    int *adj = malloc(sizeof(int) * (size_t)n * (size_t)dd);
    int *col = malloc(sizeof(int) * (size_t)n);
    int *dist = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < m && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) ok = 0;
        else { deg[u]++; deg[v]++; }
    }
    for (int v = 0; v < n && ok; v++)
        if (deg[v] > dd) ok = 0;
    if (ok) {
        for (int i = 0; i < m; i++) {
            int u = eu[i], v = ev[i];
            adj[u * dd + fill[u]++] = v;
            adj[v * dd + fill[v]++] = u;
        }
        for (int u = 0; u < n && ok; u++)
            for (int a = 0; a < deg[u] && ok; a++)
                for (int b = a + 1; b < deg[u]; b++)
                    if (adj[u * dd + a] == adj[u * dd + b]) { ok = 0; break; }
    }
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s0 = 0; s0 < n && ok; s0++) {
            if (col[s0] >= 0) continue;
            int h = 0, t = 0;
            col[s0] = 0;
            q[t++] = s0;
            while (h < t && ok) {
                int u = q[h++];
                for (int a = 0; a < deg[u]; a++) {
                    int w = adj[u * dd + a];
                    if (col[w] < 0) { col[w] = 1 - col[u]; q[t++] = w; }
                    else if (col[w] == col[u]) { ok = 0; break; }
                }
            }
        }
    }
    if (ok) {
        for (int src = 0; src < n && ok; src++) {
            for (int v = 0; v < n; v++) dist[v] = -1;
            int h = 0, t = 0;
            dist[src] = 0;
            q[t++] = src;
            while (h < t) {
                int u = q[h++];
                if (dist[u] >= D) continue;
                for (int a = 0; a < deg[u]; a++) {
                    int w = adj[u * dd + a];
                    if (dist[w] < 0) { dist[w] = dist[u] + 1; q[t++] = w; }
                }
            }
            if (t < n) ok = 0;
        }
    }
    free(deg); free(fill); free(adj); free(col); free(dist); free(q);
    return ok;
}

static void load_start(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXOUT || m < 0 || m > MAXOUT * 16) return;
    int cap = m > 0 ? m : 1;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m = i; break; }
    }
    if (check_graph(n, m, eu, ev)) {
        best_n = n; best_m = m; best_eu = eu; best_ev = ev;
    } else {
        free(eu); free(ev);
    }
}

static void print_best(void) {
    if (best_n <= 0) { printf("1 0\n"); return; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
}

static void setup_group(int Nn) {
    int divs[64], nd = 0;
    for (int k = 1; k <= Nn && k <= 12; k++)
        if (Nn % k == 0) divs[nd++] = k;
    int k = divs[rndint(nd)];
    int m = Nn / k;
    int r = (m > 1) ? 1 : 0;
    if (k > 1 && m > 1) {
        int cand[256], nc = 0;
        for (int rr = 1; rr < m && nc < 256; rr++) {
            if (gcd_i(rr, m) != 1) continue;
            if (powmod_i(rr, k, m) != 1 % m) continue;
            cand[nc++] = rr;
        }
        if (nc > 0) r = cand[rndint(nc)];
    }
    N = Nn;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mt[x * N + y] = ((a + pw[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x * N + y] == 0) { ginv[x] = y; break; }
}

static int ok_dart(int i) {
    for (int j = 0; j < S; j++)
        if (j != i && du[j] == du[i] && dv[j] == dv[i] && dg[j] == dg[i]) return 0;
    return 1;
}

static void rebuild_lists(void) {
    int cnt[4] = {0, 0, 0, 0};
    for (int i = 0; i < S; i++) {
        int v = dv[i];
        lstB[v * dd + cnt[v]++] = i;
    }
}

static int init_darts(void) {
    S = s * dd;
    int pool[MAXS], np = 0;
    for (int v = 0; v < s; v++)
        for (int t = 0; t < dd; t++) pool[np++] = v;
    for (int i = np - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = pool[i]; pool[i] = pool[j]; pool[j] = tmp;
    }
    for (int i = 0; i < S; i++) {
        du[i] = i / dd;
        dv[i] = pool[i];
        dg[i] = rndint(N);
    }
    for (int pass = 0; pass < 2000; pass++) {
        int bad = 0;
        for (int i = 0; i < S; i++)
            if (!ok_dart(i)) { dg[i] = rndint(N); bad = 1; }
        if (!bad) { rebuild_lists(); return 1; }
    }
    return 0;
}

/* Number of lifted vertices within distance D of source id (b*N + x). */
static int bfs_reach(int src) {
    stamp++;
    int h = 0, t = 0;
    que[t++] = src;
    vis[src] = stamp;
    for (int lev = 0; lev < D; lev++) {
        int end = t;
        if (h == end) break;
        while (h < end) {
            int id = que[h++];
            int b = id / N;
            int x = id - b * N;
            if (b < s) {
                for (int j = 0; j < dd; j++) {
                    int i = b * dd + j;
                    int nb = (s + dv[i]) * N + mt[x * N + dg[i]];
                    if (vis[nb] != stamp) { vis[nb] = stamp; que[t++] = nb; }
                }
            } else {
                int v = b - s;
                for (int j = 0; j < dd; j++) {
                    int i = lstB[v * dd + j];
                    int nb = du[i] * N + mt[x * N + ginv[dg[i]]];
                    if (vis[nb] != stamp) { vis[nb] = stamp; que[t++] = nb; }
                }
            }
        }
    }
    return t;
}

/* Proportional to the number of bad pairs (0 iff the lift has diameter <= D). */
static long long cost_fn(void) {
    long long sb = 0;
    for (int b = 0; b < 2 * s; b++)
        sb += (long long)(lift_n - bfs_reach(b * N));
    return sb * (long long)N;
}

static int anneal(long long steps) {
    long long cur = cost_fn();
    if (cur == 0) return 1;
    double T0 = 1.0 * N, T1 = 0.08 * N;
    for (long long st = 0; st < steps; st++) {
        if ((st & 255) == 0 && elapsed() > budget) return 0;
        double T = T0 * pow(T1 / T0, (double)st / (double)steps);
        memcpy(sv, dv, sizeof(int) * (size_t)S);
        memcpy(sg, dg, sizeof(int) * (size_t)S);
        int ok;
        if (rndint(10) < 6) {
            int i = rndint(S);
            int ng = rndint(N);
            if (ng == dg[i]) continue;
            dg[i] = ng;
            ok = ok_dart(i);
        } else {
            int i = rndint(S), j = rndint(S);
            if (dv[i] == dv[j]) continue;
            int tmp = dv[i]; dv[i] = dv[j]; dv[j] = tmp;
            ok = ok_dart(i) && ok_dart(j);
        }
        if (!ok) {
            memcpy(dv, sv, sizeof(int) * (size_t)S);
            memcpy(dg, sg, sizeof(int) * (size_t)S);
            continue;
        }
        rebuild_lists();
        long long nc = cost_fn();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            memcpy(dv, sv, sizeof(int) * (size_t)S);
            memcpy(dg, sg, sizeof(int) * (size_t)S);
            rebuild_lists();
        }
    }
    return 0;
}

static void record_lift(void) {
    int n = 2 * s * N;
    int m = S * N;
    int *eu = malloc(sizeof(int) * (size_t)m);
    int *ev = malloc(sizeof(int) * (size_t)m);
    int c = 0;
    for (int i = 0; i < S; i++)
        for (int x = 0; x < N; x++) {
            eu[c] = du[i] * N + x;
            ev[c] = (s + dv[i]) * N + mt[x * N + dg[i]];
            c++;
        }
    if (n > best_n && check_graph(n, m, eu, ev)) {
        free(best_eu); free(best_ev);
        best_eu = eu; best_ev = ev;
        best_n = n; best_m = m;
    } else {
        free(eu); free(ev);
    }
}

static void search(void) {
    double mb = moore_bound();
    int fails = 0;
    while (elapsed() < budget) {
        int sb = 1 + (rndint(4) == 0) + (rndint(3) == 0);
        long long Nmin = best_n / (2 * sb) + 1;
        long long Nmax = (long long)(mb / (2.0 * sb) + 1e-9);
        if (Nmax > MAXN - 1) Nmax = MAXN - 1;
        if (Nmin > Nmax) {
            if (++fails > 1000) break;
            continue;
        }
        fails = 0;
        long long Nn = Nmin;
        if (rndint(3) == 0) Nn = Nmin + rndint(4);
        if (Nn > Nmax) Nn = Nmin;
        s = sb;
        setup_group((int)Nn);
        lift_n = 2 * s * N;
        if (!init_darts()) continue;
        if (anneal(4000)) record_lift();
    }
}

int main(int argc, char **argv) {
    t0 = clock();
    if (argc < 5) { printf("1 0\n"); return 0; }
    dd = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    load_start();
    if (dd >= 3 && dd <= 32 && D >= 2 && D <= 12) search();
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases and Python helpers (previous pipeline, kept as a safe phase).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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


def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


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


def _legacy(d, D, rng, best, t0, T):
    """Previous Python pipeline: structured base, growth, twin trials, LNS, deletion, pruning.

    Improves the dict `best` ({"n": ..., "e": ...}) in place, using at most about T seconds.
    """
    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"], best["e"] = n, list(e)

    def at(f):
        return t0 + f * T

    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    seed_n, seed_e = best["n"], list(best["e"])
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        if best["n"] >= lib.moore_bound(d, D):
            return
        seed_n, seed_e = n0, list(e0)
        consider(*_grow(n0, e0, d, D, at(0.10), rng))
    if D >= 2:
        trial_end = at(0.20)
        while time.monotonic() < trial_end:
            consider(*_trial(seed_n, seed_e, d, D, rng, trial_end))
        _lns(best["n"], best["e"], d, D, at(0.30), rng, consider)
    if D >= 2:
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.45):
                r = _deletion_trial(d, D, rn, re, rng, at(0.45))
                if r is None:
                    break
                consider(*r)
        _lns(best["n"], best["e"], d, D, at(0.60), rng, consider)
        _prune_regrow(best["n"], best["e"], d, D, at(1.0), rng, consider)


# ----------------------------------------------------------------------------
# Driver. The Python pipeline runs first (about 40% of the time) and gives a
# safe valid graph. The C voltage-lift search then starts from the best graph
# and only accepts strictly larger valid lifts. Every candidate passes
# lib.is_valid; the final fallback is haar_graph(d, range(d)).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)
    n0, e0 = lib.haar_graph(d, range(d))
    best = {"n": n0, "e": list(e0)}
    moore = lib.moore_bound(d, D)

    if best["n"] < moore:
        try:
            _legacy(d, D, rng, best, start, 0.40 * time_limit)
        except Exception:
            pass

    if d >= 3 and D >= 2 and best["n"] < moore and lib.is_valid(best["n"], best["e"], d, D):
        hard = 0.93 * time_limit - (time.monotonic() - start)
        cbudget = hard - 1.5
        if cbudget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{cbudget:.2f}"],
                                stdin_graph=(best["n"], best["e"]), timeout=hard)
                n, e = lib.parse_graph_text(out)
                if n > best["n"] and lib.is_valid(n, e, d, D):
                    best = {"n": n, "e": list(e)}
            except Exception:
                pass

    if lib.is_valid(best["n"], best["e"], d, D):
        return best["n"], list(best["e"])
    return lib.haar_graph(d, range(d))
