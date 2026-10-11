import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over bipartite edge switches, with vertex insertion.
# Cost = number of vertex pairs at distance > D (bitset BFS). Degrees stay <= d.
# Every accepted state is bipartite and simple. The best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1100
#define MAXD 16
#define MAXW ((MAXN + 63) / 64)
#define LOGCAP 4096

static int N, CAP, DIAM;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];

static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];

static int bN;
static int bdeg[MAXN];
static int bnb[MAXN][MAXD];
static int bside[MAXN];
static int bestValid;

static uint64_t rng_state = 88172645463325252ULL;
static double BUDGET;
static clock_t T_START;

static uint64_t rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T_START) / CLOCKS_PER_SEC; }

static int logT[LOGCAP], logU[LOGCAP], logV[LOGCAP], nlog, logging;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) return 1;
    return 0;
}

static void raw_add(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
}

static void raw_del(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (nb[u][i] == v) { nb[u][i] = nb[u][--deg[u]]; break; }
    for (int i = 0; i < deg[v]; i++)
        if (nb[v][i] == u) { nb[v][i] = nb[v][--deg[v]]; break; }
}

static void op_add(int u, int v) {
    raw_add(u, v);
    if (logging && nlog < LOGCAP) { logT[nlog] = 0; logU[nlog] = u; logV[nlog] = v; nlog++; }
}

static void op_del(int u, int v) {
    raw_del(u, v);
    if (logging && nlog < LOGCAP) { logT[nlog] = 1; logU[nlog] = u; logV[nlog] = v; nlog++; }
}

static void undo_log(void) {
    for (int i = nlog - 1; i >= 0; i--) {
        if (logT[i] == 0) raw_del(logU[i], logV[i]);
        else raw_add(logU[i], logV[i]);
    }
    nlog = 0;
}

static long cost_eval(void) {
    int nw = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * nw);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * nw);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *in = cur[nb[v][i]];
                for (int w = 0; w < nw; w++) nxt[v][w] |= in[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int w = 0; w < nw; w++) cnt += popc(cur[v][w]);
        tot += N - cnt;
    }
    return tot / 2;
}

static int move_switch(void) {
    for (int t = 0; t < 30; t++) {
        int a = rndint(N);
        if (deg[a] == 0) continue;
        int b = nb[a][rndint(deg[a])];
        int c = rndint(N);
        if (c == a || side[c] != side[a] || deg[c] == 0) continue;
        int e = nb[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        op_del(a, b);
        op_del(c, e);
        op_add(a, e);
        op_add(c, b);
        return 1;
    }
    return 0;
}

static int move_add(void) {
    for (int t = 0; t < 60; t++) {
        int a = rndint(N), b = rndint(N);
        if (a == b || side[a] == side[b]) continue;
        if (deg[a] >= CAP || deg[b] >= CAP) continue;
        if (has_edge(a, b)) continue;
        op_add(a, b);
        return 1;
    }
    return 0;
}

static int move_remove(void) {
    for (int t = 0; t < 20; t++) {
        int a = rndint(N);
        if (deg[a] == 0) continue;
        int b = nb[a][rndint(deg[a])];
        op_del(a, b);
        return 1;
    }
    return 0;
}

/* Adds one vertex on a random side, joined to up to CAP opposite-side vertices
   (taking an edge away from a saturated neighbour when needed). Not logged. */
static int insert_vertex(void) {
    if (N >= MAXN - 1) return 0;
    int v = N;
    int c = rndint(2);
    side[v] = c;
    deg[v] = 0;
    N++;
    int got = 0;
    for (int tries = 0; got < CAP && tries < 2000; tries++) {
        int u = rndint(N - 1);
        if (side[u] == c || has_edge(u, v)) continue;
        if (deg[u] >= CAP) {
            if (deg[u] == 0) continue;
            int w = nb[u][rndint(deg[u])];
            raw_del(u, w);
        }
        raw_add(u, v);
        got++;
    }
    return got;
}

static long anneal(long iters, double T0, double T1) {
    long cur = cost_eval();
    if (cur == 0) return 0;
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() >= BUDGET) break;
        double frac = (double)it / (double)iters;
        double T = T0 * pow(T1 / T0, frac);
        int r = rndint(100);
        int ok;
        nlog = 0;
        logging = 1;
        if (r < 60) ok = move_switch();
        else if (r < 92) ok = move_add();
        else ok = move_remove();
        if (ok) {
            long nc = cost_eval();
            long dl = nc - cur;
            if (dl <= 0 || rnd01() < exp(-(double)dl / T)) cur = nc;
            else undo_log();
        }
        logging = 0;
        nlog = 0;
        if (cur == 0) break;
    }
    return cur;
}

static void save_best(void) {
    bN = N;
    memcpy(bdeg, deg, sizeof deg);
    memcpy(bnb, nb, sizeof nb);
    memcpy(bside, side, sizeof side);
}

static void load_best(void) {
    N = bN;
    memcpy(deg, bdeg, sizeof deg);
    memcpy(nb, bnb, sizeof nb);
    memcpy(side, bside, sizeof side);
}

static int color_graph(void) {
    static int queue[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    queue[tail++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_best(void) {
    long m = 0;
    for (int u = 0; u < bN; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (bnb[u][i] > u) m++;
    printf("%d %ld\n", bN, m);
    for (int u = 0; u < bN; u++)
        for (int i = 0; i < bdeg[u]; i++)
            if (bnb[u][i] > u) printf("%d %d\n", u, bnb[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    BUDGET = atof(argv[4]);
    T_START = clock();
    CAP = d;
    DIAM = D;
    if (CAP < 1 || CAP > MAXD || DIAM < 1) { printf("0 0\n"); return 0; }
    rng_state ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rng_state == 0) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= CAP || deg[v] >= CAP) continue;
        if (has_edge(u, v)) continue;
        raw_add(u, v);
    }
    if (!color_graph()) { printf("0 0\n"); return 0; }

    long c0 = cost_eval();
    bestValid = (c0 == 0);
    save_best();

    while (elapsed() < BUDGET) {
        load_best();
        if (bestValid) insert_vertex();
        double T0 = 0.3 + 1.5 * rnd01();
        long iters = 20000 + rndint(20000);
        long cur = anneal(iters, T0, 0.02);
        if (cur == 0 && (!bestValid || N > bN)) {
            bestValid = 1;
            save_best();
        }
    }
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python).
# ----------------------------------------------------------------------------

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


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Growth helpers (Python): cover-vertex extension and degree saturation.
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


def _extend_cover(n, edges, d, D, deadline, rng):
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
            for attempt in range(100):
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


# ----------------------------------------------------------------------------
# Driver. A structured base is grown in Python (about 20% of the budget), then
# the C annealer grows it one vertex at a time, searching for diameter-D
# supergraphs by edge switches. Every candidate is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 2 and best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    rng = random.Random(seed)

    # Structured base, grown in Python.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        consider(*base)
        n1, e1 = _grow(base[0], list(base[1]), d, D, t0 + 0.2 * time_limit, rng)
        consider(n1, e1)

    # C annealing: grow the best valid graph by vertex insertion plus annealing.
    if (D >= 2 and d <= 16 and best_n <= 1000
            and best_n < lib.moore_bound(d, D)):
        elapsed = time.monotonic() - t0
        c_budget = 0.72 * time_limit - elapsed
        tmo = 0.85 * time_limit - elapsed
        if c_budget >= 2.0 and tmo > c_budget:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                                 stdin_graph=(best_n, best_e), timeout=tmo)
                n_c, e_c = lib.parse_graph_text(text)
                consider(n_c, e_c)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
