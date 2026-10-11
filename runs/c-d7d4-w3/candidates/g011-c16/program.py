"""Target d=7, D=4 (and other cases): structured base, then a C engine.

Changes from the parent:
- The Python voltage-lift and spare-anneal phases are replaced by one C engine.
  It keeps the graph concrete, uses bitset distance costs, grows vertices by
  greedy radius-(D-1) cover, and anneals with degree-preserving 2-switches.
- The base is the W(q) quadrangle (D >= 4) or PG(2,q) (D = 3). Moore-bound
  cases return immediately.
- If the C run fails (compile error, crash, timeout), a Python greedy grower
  takes over, and the best valid graph seen so far is always returned.
"""
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

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 40
#define STALL 3000
#define PERT 8
#define T0 0.6
#define TMIN 0.12

static int N = 0, DD = 0, DIAM = 0, W = 1;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char am[MAXN][MAXN];
static int col[MAXN];
static uint64_t BA[MAXN][MAXW], BB[MAXN][MAXW], TB[MAXN][MAXW], CB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static long cur_cost = 0;
static int bestN = -1, bestM = 0;
static int bu[MAXN * MAXD / 2 + 16], bv[MAXN * MAXD / 2 + 16];
static int bestCol[MAXN];

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int n) { return (int)(nextr() % (uint64_t)n); }

static double rndu(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static double clk(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static void setW(void) {
    W = (N + 63) >> 6;
    if (W < 1) W = 1;
}

static void compute_balls(int R, uint64_t out[][MAXW]) {
    uint64_t (*src)[MAXW] = BA;
    uint64_t (*dst)[MAXW] = BB;
    int v, r, k, w;
    for (v = 0; v < N; v++) {
        for (w = 0; w < W; w++) src[v][w] = 0;
        src[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < R; r++) {
        for (v = 0; v < N; v++) {
            for (w = 0; w < W; w++) dst[v][w] = src[v][w];
            for (k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (w = 0; w < W; w++) dst[v][w] |= src[u][w];
            }
        }
        uint64_t (*t)[MAXW] = src;
        src = dst;
        dst = t;
    }
    for (v = 0; v < N; v++)
        for (w = 0; w < W; w++)
            out[v][w] = src[v][w];
}

static long cost_full(void) {
    compute_balls(DIAM, TB);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(TB[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int cov_count(const uint64_t *cov) {
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(cov[w]);
    return c;
}

static int gain_of(int s, const uint64_t *cov) {
    int g = 0;
    for (int w = 0; w < W; w++) g += pc64(CB[s][w] & ~cov[w]);
    return g;
}

static void rm_nb(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    am[a][b] = 1;
    am[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    am[a][b] = 0;
    am[b][a] = 0;
    rm_nb(a, b);
    rm_nb(b, a);
}

static void snapshot(void) {
    bestN = N;
    bestM = 0;
    for (int a = 0; a < N; a++) {
        for (int k = 0; k < deg[a]; k++) {
            int b = nb[a][k];
            if (a < b) {
                bu[bestM] = a;
                bv[bestM] = b;
                bestM++;
            }
        }
    }
    memcpy(bestCol, col, sizeof(int) * (size_t)N);
}

static void load_graph(int n, int m, const int *eu, const int *ev, const int *c) {
    for (int a = 0; a < N; a++) {
        for (int k = 0; k < deg[a]; k++) am[a][nb[a][k]] = 0;
        deg[a] = 0;
    }
    N = n;
    setW();
    for (int k = 0; k < m; k++) add_edge(eu[k], ev[k]);
    memcpy(col, c, sizeof(int) * (size_t)n);
}

/* Add one vertex joined to a greedy set of opposite-colour vertices.
   The cover may be partial; annealing then repairs the diameter. */
static int try_grow(void) {
    static int cands[MAXN];
    static int chosen[MAXD];
    if (N >= MAXN) return 0;
    int c0 = rnd(2);
    for (int t = 0; t < 2; t++) {
        int c = (t == 0) ? c0 : 1 - c0;
        int nc = 0;
        for (int s = 0; s < N; s++)
            if (col[s] != c && deg[s] < DD) cands[nc++] = s;
        if (nc == 0) continue;
        compute_balls(DIAM - 1, CB);
        uint64_t cov[MAXW];
        for (int w = 0; w < MAXW; w++) cov[w] = 0;
        int nch = 0;
        while (nch < DD && nc > 0) {
            int bi = -1, bg = -1;
            int off = rnd(nc);
            for (int i = 0; i < nc; i++) {
                int idx = (i + off) % nc;
                int g = gain_of(cands[idx], cov);
                if (g > bg) {
                    bg = g;
                    bi = idx;
                }
            }
            if (bg <= 0 && nch > 0) break;
            int s = cands[bi];
            chosen[nch++] = s;
            for (int w = 0; w < W; w++) cov[w] |= CB[s][w];
            cands[bi] = cands[nc - 1];
            nc--;
            if (cov_count(cov) == N) break;
        }
        int v = N;
        N++;
        setW();
        col[v] = c;
        deg[v] = 0;
        for (int k = 0; k < nch; k++) add_edge(v, chosen[k]);
        return 1;
    }
    return 0;
}

/* Adding edges never increases a distance, so this keeps validity. */
static void saturate(void) {
    long tries = 60L * N;
    for (long t = 0; t < tries; t++) {
        int a = rnd(N), b = rnd(N);
        if (a == b || col[a] == col[b] || deg[a] >= DD || deg[b] >= DD || am[a][b]) continue;
        add_edge(a, b);
    }
}

/* Random degree-preserving 2-switches, ignoring cost. */
static void perturb(int k) {
    if (N < 4) return;
    for (int t = 0; t < k; t++) {
        int a = rnd(N);
        if (deg[a] == 0) continue;
        int b = nb[a][rnd(deg[a])];
        int c = rnd(N);
        if (c == a || col[c] != col[a] || deg[c] == 0) continue;
        int e = nb[c][rnd(deg[c])];
        if (e == b || am[a][e] || am[c][b]) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
    }
}

static void anneal_step(double T) {
    int a = 0, b = 0, c = 0, e = 0, t, ok;
    long nc;
    int type = rnd(100);
    if (type < 45) {
        ok = 0;
        for (t = 0; t < 30 && !ok; t++) {
            a = rnd(N);
            if (deg[a] >= DD) continue;
            b = rnd(N);
            if (col[a] == col[b] || deg[b] >= DD || am[a][b]) continue;
            ok = 1;
        }
        if (!ok) return;
        add_edge(a, b);
        nc = cost_full();
        if (nc <= cur_cost || rndu() < exp(-(double)(nc - cur_cost) / T)) cur_cost = nc;
        else del_edge(a, b);
    } else if (type < 90) {
        a = rnd(N);
        if (deg[a] == 0) return;
        b = nb[a][rnd(deg[a])];
        ok = 0;
        for (t = 0; t < 30 && !ok; t++) {
            c = rnd(N);
            if (c == a || col[c] != col[a] || deg[c] == 0) continue;
            e = nb[c][rnd(deg[c])];
            if (e == b || am[a][e] || am[c][b]) continue;
            ok = 1;
        }
        if (!ok) return;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        nc = cost_full();
        if (nc <= cur_cost || rndu() < exp(-(double)(nc - cur_cost) / T)) {
            cur_cost = nc;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    } else {
        a = rnd(N);
        if (deg[a] == 0) return;
        b = nb[a][rnd(deg[a])];
        del_edge(a, b);
        nc = cost_full();
        if (nc <= cur_cost || rndu() < exp(-(double)(nc - cur_cost) / T)) cur_cost = nc;
        else add_edge(a, b);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    if (DD < 1 || DD > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n < 1 || n > MAXN || m < 0 || m > MAXN * MAXD / 2) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    int good = 1;
    N = n;
    setW();
    for (int k = 0; k < m; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            good = 0;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || am[u][v] ||
            deg[u] >= DD || deg[v] >= DD) {
            good = 0;
            break;
        }
        eu[k] = u;
        ev[k] = v;
        add_edge(u, v);
    }
    if (good) {
        for (int v = 0; v < n; v++) col[v] = -1;
        int *st = malloc(sizeof(int) * (size_t)n);
        for (int s = 0; s < n && good; s++) {
            if (col[s] != -1) continue;
            int sp = 0;
            col[s] = 0;
            st[sp++] = s;
            while (sp > 0 && good) {
                int x = st[--sp];
                for (int k = 0; k < deg[x]; k++) {
                    int y = nb[x][k];
                    if (col[y] == -1) {
                        col[y] = 1 - col[x];
                        st[sp++] = y;
                    } else if (col[y] == col[x]) {
                        good = 0;
                        break;
                    }
                }
            }
        }
        free(st);
    }
    if (!good) {
        printf("0 0\n");
        return 0;
    }

    cur_cost = cost_full();
    if (cur_cost == 0) snapshot();
    double tend = clk() + tl;
    int stall = 0;
    double T = T0;
    while (clk() < tend) {
        if (cur_cost == 0) {
            if (bestN < 0 || N > bestN) snapshot();
            if (!try_grow()) perturb(PERT);
            saturate();
            cur_cost = cost_full();
            stall = 0;
            T = T0;
            continue;
        }
        anneal_step(T);
        stall++;
        T *= 0.9995;
        if (T < TMIN) T = TMIN;
        if (cur_cost == 0) continue;
        if (stall > STALL) {
            if (bestN > 0) load_graph(bestN, bestM, bu, bv, bestCol);
            perturb(PERT);
            cur_cost = cost_full();
            stall = 0;
            T = T0;
        }
    }

    if (bestN < 0) {
        printf("0 0\n");
        return 0;
    }
    load_graph(bestN, bestM, bu, bv, bestCol);
    if (cost_full() != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
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
        if q <= 9 and lib.is_prime_power(q):   # cap q so the pure-Python build stays fast
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers (fallback growth only).
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


def _greedy_full(cands, ball, full, d, rng):
    """Pick at most d candidates whose radius-(D-1) balls cover everything, or None."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        s = max(pool, key=lambda x: (ball[x] & ~covered).bit_count())
        if (ball[s] & ~covered) == 0:
            break
        chosen.append(s)
        pool.remove(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _py_grow(n, edges, d, D, deadline, rng):
    """Add vertices that keep the graph valid, until the deadline or no growth is possible."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in rng.sample((0, 1), 2):
            cands = [s for s in range(n) if color[s] != c and len(adj[s]) < d]
            chosen = _greedy_full(cands, ball, full, d, rng)
            if chosen:
                v = n
                n += 1
                adj.append(set())
                color.append(c)
                for s in chosen:
                    adj[s].add(v)
                    adj[v].add(s)
                added = True
                break
        if not added:
            break
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # K_{d,d} is valid for every D >= 2 and serves as the safe fallback.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    base = None
    if D >= 4:
        base = _best_gq(d)
    elif D == 3:
        base = _best_pg(d)
    if base is not None:
        consider(*base)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Main search in C, starting from the best structured graph.
    c_ok = False
    remaining = time_limit - (time.monotonic() - t0)
    if remaining > 6.0:
        budget = 0.85 * remaining - 2.0
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, list(best_e)),
                            timeout=remaining - 1.5)
            c_ok = True
            consider(*lib.parse_graph_text(out))
        except Exception:
            c_ok = False

    # Python fallback if the C engine could not run.
    if not c_ok:
        rem = 0.85 * time_limit - (time.monotonic() - t0)
        if rem > 0.5:
            n2, e2 = _py_grow(best_n, best_e, d, D,
                              time.monotonic() + rem, random.Random(seed))
            consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
