import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset annealing growth. Starting from a valid graph, it repeatedly
# adds a vertex joined to a greedy cover of the opposite side, frees degree by
# deleting edges where needed, fills spare degree, then repairs the diameter by
# bipartite double-edge switches (simulated annealing on the bad-pair count).
# The current state is always valid: failed attempts are rolled back.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define ITERS 1500

static int Dg, Dist, N;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int col[MAXN];
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW], BALL[MAXN][MAXW];
static int sdeg[MAXN], sadj[MAXN][MAXDEG], scol[MAXN], sN;
static uint64_t rs;
static clock_t t_end;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void compute_balls(int r, uint64_t (*out)[MAXW]) {
    int n = N, w = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < n; v++) {
        for (int k = 0; k < w; k++) cur[v][k] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            for (int k = 0; k < w; k++) nxt[v][k] = cur[v][k];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int k = 0; k < w; k++) nxt[v][k] |= cur[u][k];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < n; v++)
        for (int k = 0; k < w; k++) out[v][k] = cur[v][k];
}

static long cost_bad(void) {
    int n = N, w = (n + 63) >> 6;
    compute_balls(Dist, BALL);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(BALL[v][k]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}
static void del_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void remove_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

static void save_state(void) {
    sN = N;
    for (int v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        scol[v] = col[v];
        memcpy(sadj[v], adj[v], sizeof(int) * deg[v]);
    }
}
static void restore_state(void) {
    N = sN;
    for (int v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        col[v] = scol[v];
        memcpy(adj[v], sadj[v], sizeof(int) * sdeg[v]);
    }
}

static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static void fill_deficient(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < Dg) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < Dg; j++) {
            int b = R[j];
            if (deg[b] < Dg && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static int choose_cover(int side, int *out) {
    static uint64_t covered[MAXW];
    static int mark[MAXN];
    int n = N, w = (n + 63) >> 6, cnt = 0;
    compute_balls(Dist - 1, BALL);
    for (int k = 0; k < w; k++) covered[k] = 0;
    for (int v = 0; v < n; v++) mark[v] = 0;
    for (int it = 0; it < Dg; it++) {
        int best = -1;
        long bs = -1;
        for (int s = 0; s < n; s++) {
            if (col[s] != side || mark[s]) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += popc(BALL[s][k] & ~covered[k]);
            if (g == 0) continue;
            long sc = (long)g * 64 + rndint(64);
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0) break;
        mark[best] = 1;
        out[cnt++] = best;
        for (int k = 0; k < w; k++) covered[k] |= BALL[best][k];
    }
    return cnt;
}

static int pick_side0(void) {
    for (int tries = 0; tries < 2000; tries++) {
        int v = rndint(N);
        if (col[v] == 0 && deg[v] > 0) return v;
    }
    return -1;
}

static int anneal(int iters) {
    long cur = cost_bad();
    if (cur == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if ((it & 63) == 0 && clock() >= t_end) break;
        int a = pick_side0();
        if (a < 0) break;
        int c = pick_side0();
        if (c < 0 || c == a) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost_bad();
        double T = 0.7 * (1.0 - (double)it / iters) + 0.03;
        int acc = 0;
        if (nw <= cur) acc = 1;
        else if (rnd01() < exp(-(double)(nw - cur) / T)) acc = 1;
        if (acc) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static int grow_once(int iters) {
    int chosen[MAXDEG];
    if (N + 2 >= MAXN) return 0;
    int side = rndint(2);
    int cnt = choose_cover(side, chosen);
    if (cnt == 0) return 0;
    int v = N++;
    col[v] = 1 - side;
    deg[v] = 0;
    for (int i = 0; i < cnt; i++) {
        int s = chosen[i];
        if (deg[s] >= Dg) {
            int t = adj[s][rndint(deg[s])];
            remove_edge(s, t);
        }
        add_edge(s, v);
    }
    fill_deficient();
    return anneal(ITERS);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], 0, 10);
    double tl = atof(argv[4]);
    Dg = d;
    rs = (uint64_t)seed * 2654435761ULL ^ 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    t_end = clock() + (clock_t)(tl * CLOCKS_PER_SEC);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0 || d < 1 || d > MAXDEG - 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        col[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || deg[u] >= Dg || deg[v] >= Dg || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition check. */
    static int stk[MAXN];
    int bip = 1;
    for (int s = 0; s < N && bip; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0 && bip) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) {
        printf("0 0\n");
        return 0;
    }

    if (Dist >= 2) {
        if (cost_bad() != 0) {
            printf("0 0\n");
            return 0;
        }
        while (clock() < t_end) {
            save_state();
            if (!grow_once(ITERS)) restore_state();
        }
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++)
            if (adj[v][i] > v) printf("%d %d\n", v, adj[v][i]);
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python-side growth helpers (used on the structured base).
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the vertices at distance D-1."""
    if D < 2:
        return n, edges
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
    """Greedily join deficient opposite-side vertices in random order. Only shortens distances."""
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
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = {"n": fb_n, "e": list(fb_e)}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = list(e)

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Already at the Moore bound: nothing to gain.
    if best["n"] >= lib.moore_bound(d, D):
        return best["n"], list(best["e"])

    # Bitset annealing growth in C, from the best valid graph found so far.
    if D >= 2 and d <= 63:
        elapsed = time.monotonic() - start
        c_budget = 0.85 * time_limit - elapsed - 1.5
        if c_budget >= 1.0:
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, seed, f"{c_budget:.2f}"],
                    stdin_graph=(best["n"], best["e"]),
                    timeout=c_budget + 15.0,
                )
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    n_out, e_out = best["n"], best["e"]
    if not lib.is_valid(n_out, e_out, d, D):
        return lib.haar_graph(d, range(d))
    return n_out, list(e_out)
