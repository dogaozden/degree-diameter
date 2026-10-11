import itertools
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXD 32
#define MAXE (MAXN * MAXD / 2 + 8)

typedef uint64_t u64;

typedef struct {
    int n;
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static int d_ = 0, D_ = 0;
static u64 rs = 88172645463325252ULL;
static double t_end = 0.0;
static Graph cur, best, work;
static long noimp = 0;
static u64 BL[MAXN][MAXW];
static u64 TT[MAXN][MAXW];

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_arc(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) {
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
    }
}

static void del_edge(Graph *g, int u, int v) {
    del_arc(g, u, v);
    del_arc(g, v, u);
}

/* out[v] = bitmask of vertices within distance r of v */
static void balls(const Graph *g, int r, u64 out[MAXN][MAXW]) {
    int N = g->n, W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < r; t++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) TT[v][w] = out[v][w];
            for (int i = 0; i < g->deg[v]; i++) {
                const u64 *s = out[g->adj[v][i]];
                for (int w = 0; w < W; w++) TT[v][w] |= s[w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) out[v][w] = TT[v][w];
    }
}

/* number of unordered pairs at distance > D_ (unreachable counts) */
static long cost(const Graph *g) {
    int N = g->n, W = (N + 63) >> 6;
    balls(g, D_, BL);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(BL[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int covered_all(const u64 *cov, const u64 *full, int W) {
    for (int w = 0; w < W; w++)
        if ((cov[w] & full[w]) != full[w]) return 0;
    return 1;
}

/* add cross-side edges between deficient vertices (only shortens distances) */
static void fill(Graph *g) {
    int N = g->n;
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (g->deg[v] >= d_) continue;
        if (g->col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && g->deg[a] < d_; j++) {
            int b = R[j];
            if (g->deg[b] < d_ && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

/* degree-preserving bipartite double-edge switches minimising bad pairs */
static long anneal(Graph *g, int iters) {
    long cc = cost(g);
    int N = g->n;
    for (int it = 0; it < iters && cc > 0; it++) {
        if ((it & 15) == 0 && now_s() > t_end) break;
        int a = rndi(N);
        if (g->deg[a] == 0) continue;
        int b = g->adj[a][rndi(g->deg[a])];
        int c = rndi(N);
        if (c == a || g->col[c] != g->col[a] || g->deg[c] == 0) continue;
        int e = g->adj[c][rndi(g->deg[c])];
        if (e == a || b == c || has_edge(g, a, e) || has_edge(g, c, b)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long nc = cost(g);
        if (nc <= cc || (nc == cc + 1 && rnd01() < 0.08)) {
            cc = nc;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    return cc;
}

/* try to add one vertex of colour c whose neighbours cover everything within D-1 */
static int try_add(Graph *g, int c, int attempts) {
    int N = g->n;
    if (N + 1 >= MAXN) return 0;
    int W = (N + 63) >> 6;
    balls(g, D_ - 1, BL);
    u64 full[MAXW];
    for (int w = 0; w < MAXW; w++) full[w] = 0;
    for (int v = 0; v < N; v++) full[v >> 6] |= 1ULL << (v & 63);
    int cand[MAXN], nc = 0;
    for (int v = 0; v < N; v++)
        if (g->col[v] != c && g->deg[v] < d_) cand[nc++] = v;
    if (nc == 0) return 0;
    static int gains[MAXN];
    static char used[MAXN];
    for (int att = 0; att < attempts; att++) {
        u64 cov[MAXW];
        for (int w = 0; w < MAXW; w++) cov[w] = 0;
        for (int i = 0; i < nc; i++) used[i] = 0;
        int chosen[MAXD], k = 0;
        while (k < d_ && !covered_all(cov, full, W)) {
            int mx = 0;
            for (int i = 0; i < nc; i++) {
                gains[i] = 0;
                if (used[i]) continue;
                const u64 *b = BL[cand[i]];
                int gs = 0;
                for (int w = 0; w < W; w++) gs += pc64(b[w] & ~cov[w]);
                gains[i] = gs;
                if (gs > mx) mx = gs;
            }
            if (mx == 0) break;
            int pick = -1;
            if (att == 0) {
                for (int i = 0; i < nc; i++)
                    if (gains[i] == mx) { pick = i; break; }
            } else {
                int thr = mx - (rnd01() < 0.5 ? 1 : 0);
                if (thr < 1) thr = 1;
                int ne = 0;
                for (int i = 0; i < nc; i++)
                    if (!used[i] && gains[i] >= thr) ne++;
                int r = rndi(ne);
                for (int i = 0; i < nc; i++) {
                    if (!used[i] && gains[i] >= thr) {
                        if (r == 0) { pick = i; break; }
                        r--;
                    }
                }
            }
            used[pick] = 1;
            chosen[k++] = cand[pick];
            const u64 *b = BL[cand[pick]];
            for (int w = 0; w < W; w++) cov[w] |= b[w];
        }
        if (covered_all(cov, full, W)) {
            g->n = N + 1;
            g->col[N] = c;
            g->deg[N] = 0;
            for (int i = 0; i < k; i++) add_edge(g, chosen[i], N);
            return 1;
        }
    }
    return 0;
}

static void grow(Graph *g) {
    long rounds = 0;
    while (now_s() < t_end && rounds < 100000) {
        rounds++;
        int c0 = rndi(2), added = 0;
        for (int j = 0; j < 2 && !added; j++)
            added = try_add(g, (c0 + j) & 1, 40);
        if (!added) break;
        fill(g);
    }
}

/* delete redundant edges while the diameter bound still holds */
static void prune(Graph *g, int maxtests) {
    static int eu[MAXE], ev[MAXE];
    int cnt = 0;
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (v < u && cnt < MAXE) { eu[cnt] = v; ev[cnt] = u; cnt++; }
        }
    for (int i = cnt - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = eu[i]; eu[i] = eu[j]; eu[j] = t;
        t = ev[i]; ev[i] = ev[j]; ev[j] = t;
    }
    int tests = 0;
    for (int i = 0; i < cnt && tests < maxtests; i++) {
        if ((i & 15) == 0 && now_s() > t_end) break;
        int u = eu[i], v = ev[i];
        if (!has_edge(g, u, v)) continue;
        tests++;
        del_edge(g, u, v);
        if (cost(g) != 0) add_edge(g, u, v);
    }
}

/* kill k vertices (random or BFS-local) into dst, keeping degrees <= d */
static void kill_build(const Graph *src, Graph *dst, int k) {
    int N = src->n;
    static char killed[MAXN];
    static int q[MAXN];
    static int remap[MAXN];
    for (int i = 0; i < N; i++) killed[i] = 0;
    int cnt = 0;
    if (rnd01() < 0.5) {
        while (cnt < k) {
            int v = rndi(N);
            if (!killed[v]) { killed[v] = 1; cnt++; }
        }
    } else {
        int head = 0, tail = 0;
        int s = rndi(N);
        killed[s] = 1;
        q[tail++] = s;
        cnt = 1;
        while (cnt < k && head < tail) {
            int v = q[head++];
            int nb[MAXD], m = src->deg[v];
            for (int i = 0; i < m; i++) nb[i] = src->adj[v][i];
            for (int i = m - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int t = nb[i]; nb[i] = nb[j]; nb[j] = t;
            }
            for (int i = 0; i < m && cnt < k; i++) {
                int u = nb[i];
                if (!killed[u]) { killed[u] = 1; q[tail++] = u; cnt++; }
            }
        }
    }
    int m = 0;
    for (int v = 0; v < N; v++)
        if (!killed[v]) remap[v] = m++;
    dst->n = m;
    for (int i = 0; i < m; i++) dst->deg[i] = 0;
    for (int v = 0; v < N; v++)
        if (!killed[v]) dst->col[remap[v]] = src->col[v];
    for (int v = 0; v < N; v++) {
        if (killed[v]) continue;
        for (int i = 0; i < src->deg[v]; i++) {
            int u = src->adj[v][i];
            if (!killed[u] && v < u) add_edge(dst, remap[v], remap[u]);
        }
    }
}

static void accept(const Graph *g) {
    if (g->n > best.n) {
        best = *g;
        noimp = 0;
    } else {
        noimp++;
    }
    if (g->n >= cur.n - 1) cur = *g;
    else if (g->n < best.n - 3) cur = best;
}

static void output(const Graph *g) {
    long m = 0;
    for (int v = 0; v < g->n; v++) m += g->deg[v];
    printf("%d %ld\n", g->n, m / 2);
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (v < g->adj[v][i]) printf("%d %d\n", v, g->adj[v][i]);
}

static void set_kdd(Graph *g, int d) {
    memset(g, 0, sizeof *g);
    g->n = 2 * d;
    for (int i = 0; i < 2 * d; i++) g->col[i] = (i < d) ? 0 : 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(g, i, d + j);
}

/* read "n m" + edges; returns 1 if the graph is valid for (d_, D_) */
static int read_start(Graph *g) {
    static int stk[MAXN];
    static int colr[MAXN];
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 < 2 || n0 > MAXN - 2 || m0 < 0) return 0;
    memset(g, 0, sizeof *g);
    g->n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) return 0;
        if (g->deg[u] >= d_ || g->deg[v] >= d_ || has_edge(g, u, v)) return 0;
        add_edge(g, u, v);
    }
    for (int i = 0; i < n0; i++) colr[i] = -1;
    for (int s = 0; s < n0; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int v = stk[--sp];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (colr[u] < 0) {
                    colr[u] = 1 - colr[v];
                    stk[sp++] = u;
                } else if (colr[u] == colr[v]) {
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < n0; i++) g->col[i] = colr[i];
    return cost(g) == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d_ < 2 || d_ > MAXD - 1 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= ((u64)seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    t_end = now_s() + budget * 0.92 - 0.1;

    if (!read_start(&cur)) set_kdd(&cur, d_);
    best = cur;
    noimp = 0;

    static const int KS[8] = {1, 1, 2, 2, 3, 4, 6, 8};
    while (now_s() < t_end) {
        if (rnd01() < 0.12) {
            work = cur;
            prune(&work, 150);
            grow(&work);
            accept(&work);
            continue;
        }
        int k = KS[rndi(8)];
        if (noimp > 1500) k = 3 + rndi(6);
        if (k > cur.n - 3) k = cur.n - 3;
        if (k < 1) break;
        kill_build(&cur, &work, k);
        fill(&work);
        if (anneal(&work, 200) != 0) {
            noimp++;
            continue;
        }
        grow(&work);
        accept(&work);
    }
    output(&best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
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
    """Dense structured graph (degree >= d) to be thinned into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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
    """Greedy set cover of `full` by at most d candidates. Returns list or None."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
    """One randomized pipeline: twin duplication mixed with growth and saturation."""
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
# Thin a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

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
    """Delete the worst vertices in batches until the diameter bound holds."""
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


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) or PG(2,q)), grown, plus short twin trials
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  C engine: kill-repair-regrow LNS and redundant-edge pruning from the best graph
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.88 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            base_n, base_e = base
            consider(base_n, base_e)
            n1, e1 = _grow(base_n, base_e, d, D, at(0.08), rng)
            consider(n1, e1)
    if best_n >= target:
        return best_n, list(best_e)

    if D >= 2:
        trial_end = at(0.14)
        while time.monotonic() < trial_end and best_n < target:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
    if best_n >= target:
        return best_n, list(best_e)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.30):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.30):
                r = _deletion_trial(d, D, rn, re, rng, at(0.30))
                if r is None:
                    break
                consider(*r)
    if best_n >= target:
        return best_n, list(best_e)

    # Phase C: C engine from the best valid graph found so far.
    budget = start + T - time.monotonic() - 1.5
    if D >= 2 and d <= 30 and budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, best_e), timeout=budget + 5)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
